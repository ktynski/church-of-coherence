#!/usr/bin/env python3
"""
run_zx_clifford_modal.py — Build zx_clifford Lean package on Modal.

Usage:
  modal run run_zx_clifford_modal.py

  # Bootstrap only (fetch deps + cache, no build):
  ZX_BOOTSTRAP=1 modal run run_zx_clifford_modal.py

  # Build a specific target:
  ZX_TARGET=Foundation modal run run_zx_clifford_modal.py

  # Count axioms without building:
  ZX_COUNT_AXIOMS=1 modal run run_zx_clifford_modal.py

What it does:
  - Uploads zx_clifford package sources into a writable /tmp tree
  - Installs elan + the toolchain specified by lean-toolchain
  - Fetches deps at pinned revisions (uses lake-manifest.json)
  - Downloads Mathlib oleans cache: `lake exe cache get`
  - Builds the package: `lake build`
  - Optionally counts remaining axiom declarations

Expected runtime:
  - First run: ~5-20 minutes (Mathlib deps + cache download)
  - Subsequent runs: faster (volume caching)

Hard constraints:
  - All subprocess calls have explicit timeouts.
  - No mocks, no fake outputs; build must succeed or return logs.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

import modal

app = modal.App("lean4-zx-clifford-build")

ELAN_VOL = modal.Volume.from_name("zx-clifford-lean-elan", create_if_missing=True)
LAKE_VOL = modal.Volume.from_name("zx-clifford-lake", create_if_missing=True)


def _read_text_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


PKG_DIR = Path(__file__).resolve().parent

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


def count_axioms_in_files(files: dict[str, str]) -> dict[str, list[str]]:
    """Count `axiom` declarations per .lean file. Returns {relpath: [axiom_names]}."""
    pattern = re.compile(r"^axiom\s+(\S+)", re.MULTILINE)
    result: dict[str, list[str]] = {}
    for rel, content in sorted(files.items()):
        if not rel.endswith(".lean"):
            continue
        matches = pattern.findall(content)
        if matches:
            result[rel] = matches
    return result


lean_image = (
    modal.Image.debian_slim(python_version="3.11")
    .apt_install("curl", "git", "gcc", "make", "zstd", "xz-utils", "ca-certificates")
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
def build_zx_clifford(
    files: dict[str, str],
    target: str | None = None,
    bootstrap: bool = False,
) -> str:
    import subprocess
    import time
    import json

    workdir = Path("/tmp/zx_clifford")
    workdir.mkdir(parents=True, exist_ok=True)

    for rel, content in files.items():
        out_path = workdir / rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(content, encoding="utf-8")

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

    lake_root = Path("/cache/lake/full")
    lake_root.mkdir(parents=True, exist_ok=True)
    lake_link = workdir / ".lake"
    if not (lake_link.exists() or lake_link.is_symlink()):
        lake_link.symlink_to(lake_root, target_is_directory=True)

    packages_dir = workdir / ".lake" / "packages"
    packages_dir.mkdir(parents=True, exist_ok=True)

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

    p_toolchain_list = run(["elan", "toolchain", "list"], timeout_s=60)
    installed = toolchain in (p_toolchain_list.stdout or "")
    if not installed:
        p_toolchain = run(["elan", "toolchain", "install", toolchain], timeout_s=900)
        if p_toolchain.returncode != 0:
            combined = (p_toolchain.stdout or "") + "\n" + (p_toolchain.stderr or "")
            if "already installed" not in combined:
                log("FAILED: elan toolchain install")
                return "\n".join(lines)
    run(["elan", "default", toolchain], timeout_s=60)

    def run_in_toolchain(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
        return run(["elan", "run", toolchain, *cmd], timeout_s=timeout_s, cwd=cwd)

    def run_in_toolchain_stream(cmd: list[str], timeout_s: int, cwd: Path | None = None) -> int:
        return run_stream(["elan", "run", toolchain, *cmd], timeout_s=timeout_s, cwd=cwd)

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
                p_head = run(["git", "-C", str(dest), "rev-parse", "HEAD"], timeout_s=30)
                if p_head.returncode == 0 and p_head.stdout.strip() == rev:
                    continue
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

    prefetch_deps_from_manifest()

    log("Skipping `lake resolve-deps` (manifest + pinned packages already present).")
    log("")

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

    log("SUCCESS: zx_clifford built on Modal.")
    return "\n".join(lines)


@app.local_entrypoint()
def main():
    files = collect_package_files()

    count_only = os.environ.get("ZX_COUNT_AXIOMS") == "1"
    if count_only:
        axiom_map = count_axioms_in_files(files)
        total = sum(len(v) for v in axiom_map.values())
        print(f"AXIOM COUNT: {total}")
        print()
        for path, names in axiom_map.items():
            print(f"  {path} ({len(names)}):")
            for n in names:
                print(f"    - {n}")
        return

    print(f"Uploading {len(files)} files from {PKG_DIR} ...")
    sample = sorted(files.keys())[:25]
    print("Sample files:", ", ".join(sample), "..." if len(files) > len(sample) else "")
    print("")

    target = os.environ.get("ZX_TARGET") or None
    bootstrap = os.environ.get("ZX_BOOTSTRAP") == "1"

    result = build_zx_clifford.remote(files, target, bootstrap)
    print(result)
