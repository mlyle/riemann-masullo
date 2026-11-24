#!/usr/bin/env python3
"""Rebuild the Chapter 10 critical-zero certificate with Lean 4.36 and zeta-lab sources."""
import argparse
import concurrent.futures
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import tomllib

PROJECT_BASE = "8b40f11bf88cc95e2cb84fcea6d6f4dd81e4b932"
ZETA_BASE = "a401821c9608526425f3d4cf7ff8e59bc37e1c79"
TARGET = "RiemannMasullo/Ch10_TraceSpectral/Sec3_Printed.lean"
PARTIAL = {"Zeta23.RvM.Backlund", "Zeta23.RvM.ZetaGrowth", "Zeta23.RvM.MainTerm"}
IMPORT = re.compile(r"^([ \t]*(?:public |meta )*import[ \t]+(?:all[ \t]+)?)(Zeta23(?:\.\w+)*)\b", re.M)
BUNDLE = Path(__file__).resolve().parent


def rel(module):
    return Path(module.replace(".", "/") + ".lean")


def out(cmd, cwd):
    return subprocess.check_output(cmd, cwd=cwd, text=True).strip()


def materialize(repo, upstream, work):
    source = upstream / "lean/vendor/zeta23"
    local = repo / "RiemannMasullo/External/ZetaLab"
    pending = ["Zeta23.Final"]
    graph = {}
    supplied = set()
    while pending:
        module = pending.pop()
        if module in graph or module in supplied:
            continue
        if (local / rel(module)).is_file() and module not in PARTIAL:
            supplied.add(module)
            continue
        original = (source / rel(module)).read_text()
        graph[module] = {name for _, name in IMPORT.findall(original)}
        pending.extend(graph[module])
    for module in graph:
        target = work / rel(module)
        target.parent.mkdir(parents=True, exist_ok=True)
        original = (source / rel(module)).read_text()
        target.write_text(IMPORT.sub(
            lambda m: m[1] + ("RiemannMasullo.External.ZetaLab." if m[2] in supplied else "") + m[2],
            original))
    return graph, supplied


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True, help="compiled riemann-masullo checkout")
    ap.add_argument("--upstream", type=Path, required=True, help="zeta-lab checkout at a401821c")
    ap.add_argument("--work", type=Path, help="new or empty build directory")
    ap.add_argument("--jobs", type=int, default=2)
    args = ap.parse_args()
    repo = args.repo.resolve()
    upstream = args.upstream.resolve()
    work = args.work.resolve() if args.work else Path(tempfile.mkdtemp(prefix="critical-zero-replay-"))
    if work.exists() and any(work.iterdir()):
        raise SystemExit("Specify an empty work directory")
    work.mkdir(exist_ok=True, parents=True)
    if out(["git", "rev-parse", "HEAD"], upstream) != ZETA_BASE:
        raise SystemExit("zeta-lab checkout differs from pin")
    compare = ["git", "diff", "--quiet", PROJECT_BASE, "--", "RiemannMasullo", "lean-toolchain",
               "lakefile.toml", "lake-manifest.json"]
    if subprocess.run(compare, cwd=repo).returncode:
        raise SystemExit("The project's Lean sources or dependency configuration differ from the pin")
    if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.36.0":
        raise SystemExit("Expected Lean 4.36.0")
    graph, supplied = materialize(repo, upstream, work)
    original = subprocess.check_output(["git", "show", PROJECT_BASE + ":" + TARGET], cwd=repo)
    (work / TARGET).parent.mkdir(parents=True, exist_ok=True)
    (work / TARGET).write_bytes(original)
    for patch in ("native-compat.patch", "chapter10-target.patch"):
        subprocess.run(["git", "apply", "--whitespace=nowarn", str(BUNDLE / patch)], cwd=work, check=True)
    for name in ("UnconditionalCount.lean", "CriticalAudit.lean"):
        shutil.copy2(BUNDLE / name, work / name)
    obj = work / "obj"
    logs = work / "logs"
    obj.mkdir()
    logs.mkdir()
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    core = "RiemannMasullo.Ch10_TraceSpectral.Sec3_Printed"
    existing = sorted("RiemannMasullo.External.ZetaLab." + m for m in supplied)
    subprocess.run([lake, "build", core, *existing], cwd=repo, check=True)
    lean = out([lake, "env", "which", "lean"], repo)
    opts = tomllib.loads((repo / "lakefile.toml").read_text())["leanOptions"]
    flags = []
    def lean_options(table, prefix=""):
        for key, value in table.items():
            name = prefix + key
            if isinstance(value, dict):
                lean_options(value, name + ".")
            else:
                v = str(value).lower() if isinstance(value, bool) else str(value)
                flags.append("-D" + name + "=" + v)
    lean_options(opts)
    paths = out([lake, "env", "printenv", "LEAN_PATH"], repo).split(os.pathsep)
    paths = [str((repo / entry).resolve()) if not os.path.isabs(entry) else entry for entry in paths]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(obj), *paths]), LEAN_NUM_THREADS="2",
               PATH=str(Path(lean).parent) + os.pathsep + os.environ.get("PATH", ""))

    def compile_module(module):
        target = (obj / rel(module)).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        with (logs / (module + ".log")).open("w") as log:
            options = flags if module == core else []
            status = subprocess.run([lean, *options, "-o", str(target), str(rel(module))], cwd=work, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        if status.returncode:
            raise RuntimeError(f"Lean failed for {module}. See {logs / (module + '.log')}")

    ready = set(supplied)
    pending = set(graph)
    running = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for module in sorted(pending):
                if len(running) >= args.jobs:
                    break
                if graph[module] <= ready:
                    pending.remove(module)
                    running[pool.submit(compile_module, module)] = module
            if not running:
                raise RuntimeError("Import cycle in remaining modules")
            completed = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)[0]
            for future in completed:
                module = running.pop(future)
                future.result()
                ready.add(module)
                print("Checked", module, flush=True)
    # Lean selects a root directory for each module namespace. Preserve access to the
    # project artifacts while compiling a replacement for just the target module.
    lib = repo / ".lake/build/lib/lean/RiemannMasullo"
    overlay = obj / "RiemannMasullo"
    overlay.mkdir()
    chapter = "Ch10_TraceSpectral"
    for entry in lib.iterdir():
        if entry.name != chapter:
            (overlay / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    (overlay / chapter).mkdir()
    for entry in (lib / chapter).iterdir():
        if not entry.name.startswith("Sec3_Printed."):
            (overlay / chapter / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    for module in ("UnconditionalCount", core, "CriticalAudit"):
        compile_module(module)
        print((logs / (module + ".log")).read_text(), flush=True)
    checker = [lean, "--run", str(repo / "scripts/Signatures.lean"), core]
    original_env = dict(env, LEAN_PATH=os.pathsep.join(paths))
    original = subprocess.check_output(checker, cwd=repo, env=original_env)
    checked = subprocess.check_output(checker, cwd=repo, env=env)
    if original != checked:
        raise RuntimeError("Public declarations changed")
    print(f"All {len(original.splitlines())} original public signatures match.")
    print("Replayed native proof and audit in", work)


if __name__ == "__main__":
    main()
