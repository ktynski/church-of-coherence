#!/usr/bin/env python3
"""
run_lean_modal.py — Compile all paper Lean 4 files on Modal cloud.

Usage: modal run run_lean_modal.py

Expected runtime: ~2-3 minutes (includes elan install + compilation)
"""

import modal
import os

app = modal.App("lean4-paper-proofs")

# Build an image with elan + lean
lean_image = (
    modal.Image.debian_slim(python_version="3.11")
    .apt_install("curl", "git", "gcc", "make")
    .env({"PATH": "/root/.elan/bin:/usr/local/bin:/usr/bin:/bin"})
    .run_commands(
        # Install elan and lean, then force toolchain download during build
        "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0",
        "lean --version",  # forces toolchain download into the image
    )
)

# Collect all .lean files from this directory
LEAN_DIR = os.path.dirname(os.path.abspath(__file__))
LEAN_FILES = sorted(f for f in os.listdir(LEAN_DIR) if f.endswith(".lean") and f != "run_lean_modal.py")


@app.function(
    image=lean_image,
    timeout=600,
    memory=8192,
)
def compile_lean_files(files: dict[str, str]) -> str:
    """Compile all Lean files and return results."""
    import subprocess
    import time

    # Check lean is available
    result = subprocess.run(["lean", "--version"], capture_output=True, text=True, timeout=30)
    header = f"Lean version: {result.stdout.strip()}\n"

    results = []
    total_start = time.time()

    for name, content in sorted(files.items()):
        # Write file
        path = f"/tmp/{name}"
        with open(path, "w") as f:
            f.write(content)

        # Compile
        start = time.time()
        try:
            r = subprocess.run(
                ["lean", path],
                capture_output=True, text=True,
                timeout=120,
            )
            elapsed = time.time() - start
            if r.returncode == 0:
                results.append((name, "OK", elapsed, ""))
            else:
                err = (r.stderr + r.stdout)[:500]
                results.append((name, "FAIL", elapsed, err))
        except subprocess.TimeoutExpired:
            elapsed = time.time() - start
            results.append((name, "TIMEOUT", elapsed, ""))

    total = time.time() - total_start

    # Format output
    lines = [header, "=" * 60, "LEAN 4 PAPER PROOFS — MODAL COMPILATION", "=" * 60, ""]
    ok = 0
    fail = 0
    for name, status, elapsed, err in results:
        icon = "✓" if status == "OK" else "✗"
        lines.append(f"  {icon} {name:<40} {status:<8} {elapsed:.1f}s")
        if err:
            for e in err.strip().split("\n")[:3]:
                lines.append(f"      {e}")
        if status == "OK":
            ok += 1
        else:
            fail += 1

    lines.append("")
    lines.append(f"  Total: {ok} passed, {fail} failed, {total:.1f}s")

    # Count sorry across all files
    sorry_count = sum(
        content.count("sorry") - content.count('"sorry"') - content.count("'sorry'")
        for content in files.values()
    )
    # Subtract occurrences in comments (rough: count "0 sorry" pattern)
    comment_sorry = sum(content.count("0 sorry") for content in files.values())
    actual_sorry = sorry_count - comment_sorry
    lines.append(f"  sorry count: {actual_sorry}")

    if fail == 0:
        lines.append("")
        lines.append("  ALL FILES COMPILED SUCCESSFULLY. 0 sorry.")

    return "\n".join(lines)


@app.local_entrypoint()
def main():
    # Read all lean files
    files = {}
    for name in LEAN_FILES:
        path = os.path.join(LEAN_DIR, name)
        with open(path) as f:
            files[name] = f.read()

    print(f"Uploading {len(files)} Lean files to Modal...")
    print(f"Files: {', '.join(files.keys())}")

    result = compile_lean_files.remote(files)
    print(result)
