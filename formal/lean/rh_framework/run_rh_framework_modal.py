#!/usr/bin/env python3
"""
run_rh_framework_modal.py — Build rh_framework Lean package on Modal.

Usage:
  modal run submission/lean/rh_framework/run_rh_framework_modal.py

Builds the full rh_framework package (Mathlib-dependent) on Modal cloud,
including the new thermodynamic closure files:
  - EnergyConvexity.lean
  - NearZeroCase.lean
  - SameSignTheorem.lean
  - SameSignBootstrap.lean
  - BeltramiInvariance.lean
  - NSQuadraticBound.lean
  - CoshSechCalculus.lean      [NEW — Path A]
  - ThermodynamicClosure.lean   [NEW — Path A]
  - NelsonBypass.lean           [NEW — Path A]
  - HQSNVFunctor.lean          [NEW — Path C]

Expected runtime:
  First run: ~10-20 min (Mathlib cache download)
  Subsequent: ~2-5 min (incremental)
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import modal

app = modal.App("lean4-rh-framework-build")

ELAN_VOL = modal.Volume.from_name("rh-framework-lean-elan", create_if_missing=True)
LAKE_VOL = modal.Volume.from_name("rh-framework-lake", create_if_missing=True)

PKG_DIR = Path(__file__).resolve().parent

INCLUDE_BASENAMES = {"lean-toolchain", "lakefile.lean", "lake-manifest.json"}
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
                files[rel] = p.read_text(encoding="utf-8")
    if "lean-toolchain" not in files:
        raise RuntimeError("Missing lean-toolchain")
    if "lakefile.lean" not in files:
        raise RuntimeError("Missing lakefile.lean")
    return files


lean_image = (
    modal.Image.debian_slim(python_version="3.11")
    .apt_install("curl", "git", "gcc", "make", "zstd", "xz-utils", "ca-certificates")
    .env({
        "ELAN_HOME": "/cache/elan",
        "PATH": "/cache/elan/bin:/usr/local/bin:/usr/bin:/bin",
    })
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
def build_rh_framework(files: dict[str, str], bootstrap: bool = False) -> str:
    import subprocess
    import time
    import json

    workdir = Path("/tmp/rh_framework")
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

    log("=" * 70)
    log("RH FRAMEWORK — LEAN 4 BUILD ON MODAL")
    log("=" * 70)
    log(f"Workdir: {workdir}")
    log(f"Toolchain: {toolchain}")
    log(f"Files uploaded: {len(files)}")
    log("")

    lean_files = sorted(k for k in files if k.endswith(".lean") and k != "lakefile.lean")
    log("Lean proof files:")
    for f in lean_files:
        log(f"  {f}")
    log("")

    def run(cmd, timeout_s, cwd=None):
        log(f"$ {' '.join(cmd)}  (timeout={timeout_s}s)")
        start = time.time()
        try:
            p = subprocess.run(cmd, cwd=str(cwd) if cwd else None,
                              capture_output=True, text=True, timeout=timeout_s)
        except subprocess.TimeoutExpired:
            elapsed = time.time() - start
            log(f"  TIMEOUT after {elapsed:.1f}s")
            raise
        elapsed = time.time() - start
        log(f"  ({elapsed:.1f}s, exit={p.returncode})")
        if p.stdout.strip():
            log(p.stdout.rstrip()[:4000])
        if p.stderr.strip():
            log(p.stderr.rstrip()[:4000])
        log("")
        return p

    def run_stream(cmd, timeout_s, cwd=None):
        log(f"$ {' '.join(cmd)}  (timeout={timeout_s}s, streaming)")
        start = time.time()
        last_output = start
        p = subprocess.Popen(cmd, cwd=str(cwd) if cwd else None,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, bufsize=1)
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
                        log("  ...still running...")
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

    lake_root = Path("/cache/lake/rh_framework")
    lake_root.mkdir(parents=True, exist_ok=True)
    lake_link = workdir / ".lake"
    if not (lake_link.exists() or lake_link.is_symlink()):
        lake_link.symlink_to(lake_root, target_is_directory=True)

    packages_dir = workdir / ".lake" / "packages"
    packages_dir.mkdir(parents=True, exist_ok=True)

    elan_bin = Path("/cache/elan/bin/elan")
    if not elan_bin.exists():
        log("Installing elan...")
        p_elan = run(["bash", "-lc",
            "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"],
            timeout_s=120)
        if p_elan.returncode != 0:
            log("FAILED: elan install")
            return "\n".join(lines)

    run(["elan", "--version"], timeout_s=30)

    p_tc = run(["elan", "toolchain", "list"], timeout_s=60)
    if toolchain not in (p_tc.stdout or ""):
        run(["elan", "toolchain", "install", toolchain], timeout_s=900)
    run(["elan", "default", toolchain], timeout_s=60)
    run(["elan", "run", toolchain, "lean", "--version"], timeout_s=180, cwd=workdir)
    run(["elan", "run", toolchain, "lake", "--version"], timeout_s=180, cwd=workdir)

    manifest_path = workdir / "lake-manifest.json"
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        pkgs = manifest.get("packages", [])
        log(f"Prefetching {len(pkgs)} packages from manifest...")
        for pkg in pkgs:
            name = pkg.get("name")
            url = pkg.get("url")
            rev = pkg.get("rev")
            if not name or not url or not rev or pkg.get("type") != "git":
                continue
            dest = packages_dir / name
            if dest.exists():
                p_head = run(["git", "-C", str(dest), "rev-parse", "HEAD"], timeout_s=30)
                if p_head.returncode == 0 and p_head.stdout.strip() == rev:
                    continue
                run(["git", "-C", str(dest), "fetch", "--depth", "1", "origin", rev], timeout_s=300)
                run(["git", "-C", str(dest), "checkout", "--force", rev], timeout_s=60)
                continue
            log(f"  cloning {name} @ {rev[:12]}")
            run(["git", "clone", "--filter=blob:none", "--no-checkout", url, str(dest)], timeout_s=600)
            run(["git", "-C", str(dest), "fetch", "--depth", "1", "origin", rev], timeout_s=300)
            run(["git", "-C", str(dest), "checkout", "--force", rev], timeout_s=60)
        log("")

    mathlib_olean = workdir / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean"
    if mathlib_olean.exists():
        log(f"Mathlib cache present (skipping cache get)")
    else:
        rc_cache = run_stream(["elan", "run", toolchain, "lake", "exe", "cache", "get"],
                              timeout_s=2400, cwd=workdir)
        if rc_cache != 0:
            log("NOTE: cache get failed; attempting build anyway.")

    if bootstrap:
        log("BOOTSTRAP COMPLETE.")
        return "\n".join(lines)

    rc_build = run_stream(["elan", "run", toolchain, "lake", "build"],
                          timeout_s=1800, cwd=workdir)

    log("")
    log("=" * 70)

    sorry_count = 0
    axiom_count = 0
    for rel, content in files.items():
        if not rel.endswith(".lean") or rel == "lakefile.lean":
            continue
        for line in content.splitlines():
            stripped = line.strip()
            if stripped.startswith("sorry") or (stripped.startswith("·") and "sorry" in stripped):
                sorry_count += 1
            if stripped.startswith("axiom "):
                axiom_count += 1

    log(f"sorry count in source: {sorry_count}")
    log(f"axiom count in source: {axiom_count}")

    if rc_build == 0:
        log("")
        log("SUCCESS: rh_framework built on Modal.")
        log(f"  {len(lean_files)} Lean proof files")
        log(f"  {sorry_count} sorry")
        log(f"  {axiom_count} axioms")
        if sorry_count == 0 and axiom_count == 0:
            log("")
            log("  ALL FILES COMPILED. 0 sorry. 0 axioms.")
    else:
        log("")
        log("FAILED: lake build returned non-zero.")

    return "\n".join(lines)


@app.local_entrypoint()
def main():
    files = collect_package_files()
    print(f"Uploading {len(files)} files from {PKG_DIR} ...")
    lean_count = sum(1 for k in files if k.endswith(".lean"))
    print(f"  {lean_count} Lean files, {len(files) - lean_count} config/other")
    sample = sorted(files.keys())[:15]
    print(f"  Sample: {', '.join(sample)}")
    print()

    bootstrap = os.environ.get("RH_BOOTSTRAP") == "1"
    result = build_rh_framework.remote(files, bootstrap)
    print(result)
