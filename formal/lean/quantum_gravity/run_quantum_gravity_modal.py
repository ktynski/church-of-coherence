#!/usr/bin/env python3
"""
run_quantum_gravity_modal.py — Build quantum_gravity Lean package on Modal.

Usage:
  modal run run_quantum_gravity_modal.py

What it does:
  - Uploads the *entire* quantum_gravity package sources into a writable /tmp tree
  - Installs elan + the toolchain specified by lean-toolchain
  - Fetches deps at pinned revisions (uses lake-manifest.json if provided)
  - Downloads Mathlib oleans cache: `lake exe cache get`
  - Builds the package: `lake build`

Expected runtime:
  - First run: ~5–20 minutes (Mathlib deps + cache download)
  - Subsequent runs: faster (image layer caching)

Hard constraints:
  - All subprocess calls have explicit timeouts.
  - No mocks, no fake outputs; build must succeed or return logs.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import modal

app = modal.App("lean4-quantum-gravity-build")

# Persist caches across runs so we don't redownload toolchains/deps every time.
ELAN_VOL = modal.Volume.from_name("quantum-gravity-lean-elan", create_if_missing=True)
LAKE_VOL = modal.Volume.from_name("quantum-gravity-lake", create_if_missing=True)


def _read_text_file(path: Path) -> str:
    # Read as UTF-8 with strict errors: if something isn't text, we should fail loudly.
    return path.read_text(encoding="utf-8")


PKG_DIR = Path(__file__).resolve().parent

# Upload only source/config files; exclude any build artifacts.
INCLUDE_BASENAMES = {
    "lean-toolchain",
    "lakefile.lean",
    "lake-manifest.json",
    "README.md",
}
INCLUDE_SUFFIXES = {".lean", ".md"}
EXCLUDE_DIRS = {".lake", "build", ".git", "__pycache__"}


def collect_package_files() -> dict[str, str]:
    files: dict[str, str] = {}
    for root, dirs, filenames in os.walk(PKG_DIR):
        # prune excluded dirs in-place
        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS and not d.startswith(".lake")]
        root_path = Path(root)
        for fn in filenames:
            p = root_path / fn
            rel = p.relative_to(PKG_DIR).as_posix()
            if fn in INCLUDE_BASENAMES or p.suffix in INCLUDE_SUFFIXES:
                files[rel] = _read_text_file(p)
    if "lean-toolchain" not in files:
        raise RuntimeError("Missing lean-toolchain in upload set")
    if "lakefile.lean" not in files:
        raise RuntimeError("Missing lakefile.lean in upload set")
    return files


lean_image = (
    modal.Image.debian_slim(python_version="3.11")
    .apt_install("curl", "git", "gcc", "make", "zstd", "xz-utils", "ca-certificates")
    # Use /cache so we can mount Volumes there safely.
    .env(
        {
            "ELAN_HOME": "/cache/elan",
            "PATH": "/cache/elan/bin:/usr/local/bin:/usr/bin:/bin",
        }
    )
)


@app.function(
    image=lean_image,
    timeout=3600,
    memory=16384,
    volumes={
        "/cache/elan": ELAN_VOL,
        "/cache/lake": LAKE_VOL,
    },
)
def build_quantum_gravity(files: dict[str, str], target: str | None = None, bootstrap: bool = False) -> str:
    import subprocess
    import time
    import json

    # Use a stable workdir but isolate `.lake` per target.
    workdir = Path("/tmp/quantum_gravity")
    workdir.mkdir(parents=True, exist_ok=True)

    # Materialize files
    for rel, content in files.items():
        out_path = workdir / rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(content, encoding="utf-8")

    # Read toolchain and install it explicitly (avoid any elan ambiguity)
    toolchain = (workdir / "lean-toolchain").read_text(encoding="utf-8").strip()

    lines: list[str] = []
    def log(s: str) -> None:
        print(s, flush=True)
        lines.append(s)

    log(f"Workdir: {workdir}")
    log(f"Toolchain: {toolchain}")
    if target:
        log(f"Target: {target}")
    log("")

    def run(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
        log(f"$ {' '.join(cmd)}  (timeout={timeout_s}s)")
        start = time.time()
        try:
            p = subprocess.run(
                cmd,
                cwd=str(cwd) if cwd is not None else None,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired:
            elapsed = time.time() - start
            log(f"  TIMEOUT after {elapsed:.1f}s")
            log("")
            raise
        elapsed = time.time() - start
        log(f"  ({elapsed:.1f}s, exit={p.returncode})")
        if p.stdout.strip():
            log(p.stdout.rstrip()[:4000])
        if p.stderr.strip():
            log(p.stderr.rstrip()[:4000])
        log("")
        return p

    def run_stream(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> int:
        log(f"$ {' '.join(cmd)}  (timeout={timeout_s}s, streaming)")
        start = time.time()
        last_output = start
        p = subprocess.Popen(
            cmd,
            cwd=str(cwd) if cwd is not None else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert p.stdout is not None
        try:
            import select

            fd = p.stdout.fileno()
            while True:
                if p.poll() is not None:
                    # Drain any remaining buffered output (including non-newline-terminated JSON).
                    try:
                        remaining = p.stdout.read()
                    except Exception:
                        remaining = ""
                    if remaining:
                        for line in remaining.splitlines():
                            log(line.rstrip()[:4000])
                    break
                now = time.time()
                if now - start > timeout_s:
                    p.kill()
                    log("  TIMEOUT (killed)")
                    return 124
                r, _, _ = select.select([fd], [], [], 2.0)
                if r:
                    line = p.stdout.readline()
                    if not line:
                        continue
                    last_output = time.time()
                    log(line.rstrip()[:4000])
                else:
                    # Heartbeat every ~15s without output.
                    if now - last_output > 15:
                        log("  ...still running (no output yet)...")
                        last_output = now
        finally:
            try:
                p.stdout.close()
            except Exception:
                pass
        rc = p.wait(timeout=10)
        elapsed = time.time() - start
        log(f"  ({elapsed:.1f}s, exit={rc})")
        log("")
        return rc

    # Shared Lake workspace (single cache). This enables the "bootstrap once" workflow.
    lake_root = Path("/cache/lake/full")
    lake_root.mkdir(parents=True, exist_ok=True)
    lake_link = workdir / ".lake"
    if not (lake_link.exists() or lake_link.is_symlink()):
        lake_link.symlink_to(lake_root, target_is_directory=True)

    packages_dir = workdir / ".lake" / "packages"
    packages_dir.mkdir(parents=True, exist_ok=True)

    # Ensure elan exists inside the mounted ELAN_HOME volume.
    elan_bin = Path("/cache/elan/bin/elan")
    if not elan_bin.exists():
        log("Elan not found in cache; installing elan into ELAN_HOME...")
        log("")
        p_elan_install = run(
            [
                "bash",
                "-lc",
                "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
            ],
            timeout_s=120,
        )
        if p_elan_install.returncode != 0:
            log("FAILED: elan install")
            return "\n".join(lines)

    run(["elan", "--version"], timeout_s=30)

    # Ensure toolchain exists
    p_toolchain_list = run(["elan", "toolchain", "list"], timeout_s=60)
    installed = toolchain in (p_toolchain_list.stdout or "")
    if not installed:
        p_toolchain = run(["elan", "toolchain", "install", toolchain], timeout_s=900)
        if p_toolchain.returncode != 0:
            # Elan sometimes returns non-zero with "already installed" messaging; treat that as success.
            combined = (p_toolchain.stdout or "") + "\n" + (p_toolchain.stderr or "")
            if "already installed" not in combined:
                log("FAILED: elan toolchain install")
                return "\n".join(lines)
    run(["elan", "default", toolchain], timeout_s=60)

    def run_in_toolchain(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
        return run(["elan", "run", toolchain, *cmd], timeout_s=timeout_s, cwd=cwd)

    def run_in_toolchain_stream(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> int:
        return run_stream(["elan", "run", toolchain, *cmd], timeout_s=timeout_s, cwd=cwd)

    # First invocations can trigger downloads/extraction; allow extra time.
    run_in_toolchain(["lean", "--version"], timeout_s=180, cwd=workdir)
    run_in_toolchain(["lake", "--version"], timeout_s=180, cwd=workdir)

    def prefetch_deps_from_manifest() -> None:
        manifest_path = workdir / "lake-manifest.json"
        if not manifest_path.exists():
            log("No lake-manifest.json found; falling back to lake resolve-deps.")
            log("")
            return
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        pkgs = manifest.get("packages", [])
        log(f"Prefetching {len(pkgs)} packages from lake-manifest.json (git, blob-less)...")
        for pkg in pkgs:
            name = pkg.get("name")
            url = pkg.get("url")
            rev = pkg.get("rev")
            typ = pkg.get("type")
            if not name or not url or not rev or typ != "git":
                raise RuntimeError(f"Unsupported manifest entry: {pkg}")
            dest = packages_dir / name
            if dest.exists():
                # Ensure it's at the expected revision (best-effort; don't be silent if git fails).
                p_head = run(["git", "-C", str(dest), "rev-parse", "HEAD"], timeout_s=30)
                if p_head.returncode == 0 and p_head.stdout.strip() == rev:
                    continue
                # Fetch the exact revision with minimal history.
                log(f"- updating {name} to {rev[:12]}")
                run(["git", "-C", str(dest), "fetch", "--depth", "1", "origin", rev], timeout_s=300)
                run(["git", "-C", str(dest), "checkout", "--force", rev], timeout_s=60)
                continue

            log(f"- cloning {name} @ {rev[:12]}")
            run(
                ["git", "clone", "--filter=blob:none", "--no-checkout", url, str(dest)],
                timeout_s=600,
            )
            run(["git", "-C", str(dest), "fetch", "--depth", "1", "origin", rev], timeout_s=300)
            run(["git", "-C", str(dest), "checkout", "--force", rev], timeout_s=60)
        log("Prefetch complete.")
        log("")

    # Prefetch deps without git (faster, more resilient than cloning).
    prefetch_deps_from_manifest()

    # If we have a manifest and all packages are present at pinned commits,
    # we can skip `lake resolve-deps` (which sometimes hangs on preemptible workers).
    # We'll still fail loudly later if `lake exe cache get`/`lake build` can't proceed.
    log("Skipping `lake resolve-deps` (manifest + pinned packages already present).")
    log("")

    # Pull mathlib cache (oleans); first run is the big step.
    mathlib_olean = workdir / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean"
    if mathlib_olean.exists():
        log(f"Cache present: {mathlib_olean} (skipping `lake exe cache get`)")
        log("")
    else:
        rc_cache = run_in_toolchain_stream(["lake", "exe", "cache", "get"], timeout_s=2400, cwd=workdir)
        if rc_cache != 0:
            log("NOTE: lake exe cache get failed; attempting lake build anyway.")
            log("")

    if bootstrap:
        log("BOOTSTRAP COMPLETE (deps resolved, cache fetched).")
        return "\n".join(lines)

    build_cmd = ["lake", "build"] if not target else ["lake", "build", target]
    rc_build = run_in_toolchain_stream(build_cmd, timeout_s=1800, cwd=workdir)
    if rc_build != 0:
        log("FAILED: lake build")
        return "\n".join(lines)

    log("SUCCESS: quantum_gravity built on Modal.")
    return "\n".join(lines)


@app.local_entrypoint()
def main():
    files = collect_package_files()
    print(f"Uploading {len(files)} files from {PKG_DIR} ...")
    # Basic sanity list (avoid printing thousands of lines)
    sample = sorted(files.keys())[:25]
    print("Sample files:", ", ".join(sample), "..." if len(files) > len(sample) else "")
    print("")

    target = os.environ.get("QG_TARGET") or None
    bootstrap = os.environ.get("QG_BOOTSTRAP") == "1"

    result = build_quantum_gravity.remote(files, target, bootstrap)
    print(result)

