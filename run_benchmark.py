#!/usr/bin/env python3
"""Build and measure the Isabelle/HOL bridge benchmark."""

import argparse
from collections import Counter, defaultdict
from contextlib import suppress
from hashlib import sha256
import json
import math
import os
from pathlib import Path
import platform
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time


# __file__ is the path to this Python source. Resolve it so the manifest and
# theories can be found even when you run the script from another directory.
HERE = Path(__file__).resolve().parent
SESSION = "Bridge_Benchmark"
# Order matters. Python uses each tuple position as the method or status number
# exchanged with Benchmark.thy.
METHODS = ("oracle", "pdr_cegar", "pdr_concrete", "smartaxe", "bridgefuzz", "scutum", "bmc")
STATUSES = ("proved", "violation", "alert", "no_finding", "inconclusive", "unsupported")
DEFINITIVE = {"proved", "violation"}
# Freeze the experimental budgets and seeds here. Python ignores underscores
# inside numeric literals, so 10_000 means ten thousand.
FIXED_BUDGETS = {"oracle": 10_000, "pdr_cegar": 256, "pdr_concrete": 256,
                 "smartaxe": 0, "bridgefuzz": 64, "scutum": 256}
BMC_DEPTHS = (4, 8, 16)
FUZZ_SEEDS = tuple(range(1, 31))
TIMEOUT_SECONDS = 30.0


# Run an external command using a list of arguments. **kwargs forwards named
# options such as cwd or env. On failure, retain both output streams for
# diagnostics.
def command_output(args, **kwargs):
    completed = subprocess.run(args, capture_output=True, text=True, **kwargs)
    if completed.returncode:
        details = completed.stdout + completed.stderr
        raise RuntimeError(f"{args[0]} exited with {completed.returncode}\n{details}")
    return completed.stdout.strip()


# Ask Isabelle which directory contains its Poly/ML tools. The nested helper
# setting reads one plain value at a time.
def poly_library_dir(isabelle, settings):
    def setting(key):
        return command_output([isabelle, "getenv", "-b", key], env=settings)

    # Isabelle2026 chooses ML_HOME in Scala. Use the distribution's full-width
    # native Poly/ML component for the standalone benchmark.
    component = Path(setting("POLYML_HOME"))
    native_platform = setting("ISABELLE_APPLE_PLATFORM64") or setting("ISABELLE_PLATFORM64")
    directory = component / native_platform
    if not (directory / "poly").is_file():
        raise RuntimeError(f"The Isabelle Poly/ML binary is missing at {directory / 'poly'}")
    return directory


# Turn the compiled Standard ML object into an executable. The macOS branch
# links the bundled GMP library explicitly. The Linux branch uses Isabelle's
# polyc linker wrapper.
def link_engine(ml_home, work, binary):
    bundled_gmp = ml_home / "libgmp.10.dylib"
    if sys.platform == "darwin" and bundled_gmp.is_file():
        # The macOS distribution packages a versioned GMP library beside poly.
        # polyc expects an unversioned link library from its original build host.
        local_gmp = work / bundled_gmp.name
        shutil.copy2(bundled_gmp, local_gmp)
        command_output(["c++", "-Wl,-headerpad_max_install_names", "-o", str(binary), "bridge-engine.o",
                        str(ml_home / "libpolymain.a"), str(ml_home / "libpolyml.a"),
                        str(local_gmp)], cwd=work)
        # The dylib records its original install name. Point the new executable
        # to the copy beside it, then refresh its signature after editing it.
        install_name = command_output(["otool", "-D", str(local_gmp)]).splitlines()[-1]
        command_output(["install_name_tool", "-change", install_name,
                        f"@loader_path/{local_gmp.name}", str(binary)])
        command_output(["codesign", "--force", "--sign", "-", str(binary)])
    else:
        command_output([str(ml_home / "polyc"), "-o", str(binary), "bridge-engine.o"], cwd=work)


# Find Isabelle, build the theory session, export its executable definitions,
# append the CLI driver, and compile the combined Standard ML into a runnable
# engine.
def build_engine(isabelle_arg, work, output):
    isabelle = shutil.which(isabelle_arg)
    if isabelle is None:
        raise RuntimeError("Isabelle executable missing. Pass its path with --isabelle.")

    # Isabelle's documented USER_HOME setting controls its private heap and cache location.
    profile = Path(os.environ.get("BRIDGE_ISABELLE_PROFILE", output / ".isabelle-profile")).resolve()
    profile.mkdir(parents=True, exist_ok=True)
    settings = dict(os.environ, USER_HOME=str(profile))
    version = command_output([isabelle, "version"], env=settings)
    print(f"Building {SESSION} with {version}", flush=True)
    started_at = time.monotonic()
    build_log = command_output([isabelle, "build", "-d", str(HERE), SESSION], env=settings)
    build_seconds = time.monotonic() - started_at
    (output / "build.log").write_text(build_log + "\n", encoding="utf-8")

    started_at = time.monotonic()
    exports = work / "export"
    command_output([isabelle, "export", "-n", "-d", str(HERE), "-x", "*:code/Bridge_Run.ML",
                    "-O", str(exports), SESSION], env=settings)
    sources = list(exports.rglob("Bridge_Run.ML"))
    if len(sources) != 1:
        raise RuntimeError(f"Expected one Bridge_Run.ML export, found {len(sources)}")

    ml_home = poly_library_dir(isabelle, settings)
    poly = ml_home / "poly"
    source = work / "engine.ML"
    source.write_text(sources[0].read_text(encoding="utf-8") + "\n"
                      + (HERE / "benchmark_driver.ML").read_text(encoding="utf-8") + "\n",
                      encoding="utf-8")
    binary = work / "bridge-engine"
    # The distribution's raw Poly/ML is also a fallback on hosts without a C linker.
    try:
        with source.open("a", encoding="utf-8") as module:
            module.write('val () = PolyML.export ("bridge-engine", Benchmark_Driver.main);\n')
        command_output([str(poly), "--script", str(source)], cwd=work)
        link_engine(ml_home, work, binary)
        engine = [str(binary)]
        runtime = "compiled Poly/ML executable"
    except (OSError, RuntimeError) as failure:
        print(f"Using Poly/ML script mode ({failure})", file=sys.stderr, flush=True)
        with source.open(encoding="utf-8") as module:
            content = module.read().split('val () = PolyML.export ("bridge-engine",', 1)[0]
        source.write_text(content + "val () = Benchmark_Driver.main ();\n", encoding="utf-8")
        engine = [str(poly), "--script", str(source)]
        runtime = "Poly/ML script, compiled at process startup"

    return engine, {
        "isabelle": version,
        "session_build_seconds": build_seconds,
        "engine_setup_seconds": time.monotonic() - started_at,
        "generated_hol_code_sha256": sha256(sources[0].read_bytes()).hexdigest(),
        "runtime": runtime,
    }


# Read the JSON manifest and combine each case family with each supported
# transfer count. The final for clauses in the list comprehension produce that
# cross product.
def load_cases():
    manifest = json.loads((HERE / "benchmark_cases.json").read_text(encoding="utf-8"))
    return [dict(family, transfers=count, key=f"{family['case']}/{count}")
            for family in manifest["families"] for count in manifest["transfer_counts"]]


# yield produces one job at a time. Start with independent reachability, then
# give bounded checking every depth and fuzzing every seed. The remaining
# methods run once per case.
def jobs(oracle_only=False):
    yield "oracle", FIXED_BUDGETS["oracle"], 0
    if oracle_only:
        return
    for method in METHODS[1:]:
        if method == "bmc":
            for depth in BMC_DEPTHS:
                yield method, depth, 0
        elif method == "bridgefuzz":
            for seed in FUZZ_SEEDS:
                yield method, FIXED_BUDGETS[method], seed
        else:
            yield method, FIXED_BUDGETS[method], 0


# Kill the process group so a timed-out invocation cannot leave its children
# running. suppress ignores the race where the group has already finished.
def stop_process(pid):
    with suppress(ProcessLookupError):
        os.killpg(pid, signal.SIGKILL)


# Poll with wait4 to collect both exit status and resource usage. WNOHANG means
# the call returns immediately if the process still runs. At the deadline, kill
# the process and then collect its final status.
def wait_for_job(process, deadline):
    try:
        while True:
            pid, status, usage = os.wait4(process.pid, os.WNOHANG)
            if pid:
                process.returncode = os.waitstatus_to_exitcode(status)
                return False, usage
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(0.001, remaining))
    except BaseException:
        stop_process(process.pid)
        _, status, _ = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
        raise

    stop_process(process.pid)
    _, status, usage = os.wait4(process.pid, 0)
    process.returncode = os.waitstatus_to_exitcode(status)
    return True, usage


# Start one engine process so each measurement has its own time and memory
# usage. Capture its streams in temporary files, decode its JSON response, and
# validate the result shape before adding it to the run log.
def run_job(engine, case, method, budget, seed, timeout):
    args = [*engine, *map(str, (case["id"], case["transfers"], METHODS.index(method), budget, seed))]
    with tempfile.TemporaryFile(mode="w+t", encoding="utf-8") as stdout, \
            tempfile.TemporaryFile(mode="w+t", encoding="utf-8") as stderr:
        started_at = time.monotonic()
        process = subprocess.Popen(args, stdout=stdout, stderr=stderr, start_new_session=True)
        expired, usage = wait_for_job(process, started_at + timeout)
        elapsed = time.monotonic() - started_at
        stdout.seek(0)
        stderr.seek(0)
        response, error = stdout.read(), stderr.read().strip()

    peak_bytes = usage.ru_maxrss if sys.platform == "darwin" else usage.ru_maxrss * 1024
    row = {"case": case["key"], "family": case["id"], "property": case["property"],
           "transfer_ids": case["transfers"], "method": method, "budget": budget, "seed": seed,
           "wall_seconds": elapsed, "peak_rss_bytes": peak_bytes}
    if expired:
        return dict(row, status="timeout")
    if process.returncode:
        return dict(row, status="error", detail=error or f"Exit code {process.returncode}")

    try:
        # Poly/ML script mode can print compiler diagnostics before the result.
        result = json.loads(response.strip().splitlines()[-1])
        code = result["status"]
        if type(code) is not int or not 0 <= code < len(STATUSES):
            raise ValueError(f"Unknown result status {code!r}")
        status = STATUSES[code]
        if status == "no_finding" and method == "smartaxe":
            status = "no_alert"
        for field in ("depth", "work", "refinements", "compute_us"):
            if type(result[field]) is not int or result[field] < 0:
                raise ValueError(f"Invalid result field {field}")
        evidence = result["evidence"]
        if not isinstance(evidence, list) or any(type(value) is not int or value < 0 for value in evidence):
            raise ValueError("Expected a list of nonnegative evidence IDs")
        if status == "violation" and len(evidence) != result["depth"] + 1:
            raise ValueError("The trace length disagrees with its depth")
        if status in {"proved", "alert"} and not evidence:
            raise ValueError(f"Missing evidence for {status}")
    except (KeyError, IndexError, TypeError, ValueError) as failure:
        return dict(row, status="error", detail=f"Invalid engine response: {failure}\n{response}")

    return dict(row, status=status, checked=status in DEFINITIVE,
                witness_depth=result["depth"] if status == "violation" else None,
                work=result["work"], refinements=result["refinements"],
                compute_us=result["compute_us"], evidence=evidence)


# Check the oracle against the manifest, then compare definitive method verdicts
# with the oracle. For bounded checking, also compare the reported finding or
# miss with the oracle's shortest depth.
def audit(case, row, oracle):
    status = row["status"]
    if status == "error":
        return f"{row['method']} on {row['case']} failed. {row['detail']}"
    if row["method"] == "oracle":
        if status != case["expected"]:
            return f"The reachability label for {row['case']} is {status}, expected {case['expected']}."
        if status == "violation" and row["witness_depth"] != case["expected_depth"]:
            return (f"The shortest depth for {row['case']} is {row['witness_depth']}, "
                    f"expected {case['expected_depth']}.")
    elif status in DEFINITIVE:
        if status != oracle["status"]:
            return f"{row['method']} disagrees with reachability on {row['case']}."
        if status == "violation" and row["witness_depth"] < oracle["witness_depth"]:
            return f"{row['method']} found a shorter trace than the oracle on {row['case']}."
        if row["method"] == "bmc" and status == "violation":
            if row["witness_depth"] != oracle["witness_depth"]:
                return f"Bounded breadth-first checking disagrees on shortest depth for {row['case']}."
            if row["witness_depth"] > row["budget"]:
                return f"Bounded checking exceeded its depth budget for {row['case']}."
    elif row["method"] == "bmc" and status == "no_finding" and oracle["status"] == "violation":
        if row["budget"] >= oracle["witness_depth"]:
            return f"Bounded checking missed a reachable violation within its bound for {row['case']}."
    return None


# Read the available measurements, convert units with scale, and print the
# median to three decimal places. Use a dot when there are no measurements.
def fmt_median(rows, key, scale):
    values = [row[key] / scale for row in rows if row.get(key) is not None]
    return f"{statistics.median(values):.3f}" if values else "·"


# Group the raw run rows into method, budget, and case summaries. Each group
# contributes counts and medians to the Markdown report.
def report(cases, rows, metadata, failures):
    by_method = defaultdict(list)
    for row in rows:
        title = f"bmc ({row['budget']})" if row["method"] == "bmc" else row["method"]
        by_method[title].append(row)
    oracle = {row["case"]: row for row in by_method.pop("oracle", [])}
    titles = [method for method in METHODS[1:-1] if method in by_method]
    titles.extend(f"bmc ({depth})" for depth in BMC_DEPTHS if f"bmc ({depth})" in by_method)
    lines = ["# Isabelle/HOL bridge comparison", "",
             f"{len(cases)} finite model/property pairs. Exhaustive reachability labeled "
             f"{sum(row['status'] in DEFINITIVE for row in oracle.values())} pairs.", "",
             f"The {metadata['runtime']} ran on {metadata['platform']}.", ""]
    if "isabelle" in metadata:
        lines.extend([f"The {metadata['isabelle']} session build command took "
                      f"{metadata['session_build_seconds']:.2f} s. Engine setup took "
                      f"{metadata['engine_setup_seconds']:.2f} s.", ""])
    if failures:
        lines.extend(["## Validation failures", "", *[f"- {failure}" for failure in failures], ""])
    lines.extend([f"The run used a {metadata['timeout_seconds']:g} s wall limit per invocation. "
                  f"BridgeFuzz sampled up to {FIXED_BUDGETS['bridgefuzz']} sequences of up to 16 steps "
                  f"per seed, with {len(FUZZ_SEEDS)} seeds per pair. "
                  "The metadata file records the finite work limits for the verifiers.", ""])

    lines.extend(["## Property support and detection", "",
                  "Support counts model/property pairs accepted by a method. A detection is a checked "
                  "violation, or a SmartAxe alert on a pair labeled as a violation. For BridgeFuzz, "
                  "a pair counts once if any seed finds it.", "",
                  "| Method | Supported pairs | Violating supported pairs found | Proved pairs | False static alerts |",
                  "| --- | ---: | ---: | ---: | ---: |"])
    for title in titles:
        group = by_method[title]
        supported = {row["case"] for row in group if row["status"] not in {"error", "unsupported"}}
        issues = {key for key in supported if oracle[key]["status"] == "violation"}
        found = {row["case"] for row in group if row["status"] in {"alert", "violation"}}
        proved = {row["case"] for row in group if row["status"] == "proved"}
        false_alerts = {row["case"] for row in group if row["status"] == "alert"
                        and oracle[row["case"]]["status"] == "proved"}
        lines.append(f"| {title} | {len(supported)}/{len(cases)} | {len(found & issues)}/{len(issues)} | "
                     f"{len(proved)} | {len(false_alerts)} |")

    lines.extend(["", "## Per-run outcomes and resources", "",
                  "Wall time includes process launch. Compute time covers model construction, analysis, "
                  "and any evidence checks in the exported HOL job. Peak RSS "
                  "includes the Poly/ML runtime. Medians use supported runs that returned a result.", "",
                  "| Method | Runs | Outcomes | Wall ms | Compute ms | Peak RSS MiB |",
                  "| --- | ---: | --- | ---: | ---: | ---: |"])
    for title in titles:
        group = by_method[title]
        outcomes = ", ".join(f"{count} {status}" for status, count in
                             sorted(Counter(row["status"] for row in group).items()))
        measured = [row for row in group if row["status"] not in {"error", "timeout", "unsupported"}]
        lines.append(f"| {title} | {len(group)} | {outcomes} | "
                     f"{fmt_median(measured, 'wall_seconds', .001)} | "
                     f"{fmt_median(measured, 'compute_us', 1000)} | "
                     f"{fmt_median(measured, 'peak_rss_bytes', 2**20)} |")

    lines.extend(["", "## Results by model and property", "",
                  "For BridgeFuzz, hit counts use completed sampling runs as the denominator. "
                  "The first-finding time is the median compute time of successful seeds for that case. "
                  "PDR/CEGAR results include the number of refinement rounds.", "",
                  "| Case | Property | Reachability label | " + " | ".join(titles) + " |",
                  "| --- | --- | --- |" + " --- |" * len(titles)])
    for case in cases:
        label = oracle.get(case["key"], {"status": "pending"})
        label_text = label["status"]
        if label_text == "violation":
            label_text += f" at depth {label['witness_depth']}"
        cells = [case["key"], case["property"], label_text]
        for title in titles:
            group = [row for row in by_method[title] if row["case"] == case["key"]]
            if not group:
                cells.append("pending")
            elif title == "bridgefuzz" and any(row["status"] in {"violation", "no_finding"} for row in group):
                complete = [row for row in group if row["status"] in {"violation", "no_finding"}]
                hits = [row for row in complete if row["status"] == "violation"]
                summary = f"{len(hits)}/{len(complete)} hits"
                if hits:
                    summary += f", {fmt_median(hits, 'compute_us', 1000)} ms"
                if len(complete) < len(group):
                    summary += f", {len(group) - len(complete)} other outcomes"
                cells.append(summary)
            else:
                row = group[0]
                summary = row["status"]
                if title == "pdr_cegar" and row.get("refinements") is not None:
                    summary += f" ({row['refinements']} refinements)"
                cells.append(summary)
        lines.append("| " + " | ".join(cells) + " |")

    if by_method.get("pdr_cegar") and by_method.get("pdr_concrete"):
        concrete = {row["case"]: row for row in by_method["pdr_concrete"]}
        paired = [(row, concrete[row["case"]]) for row in by_method["pdr_cegar"]
                  if row["case"] in concrete and row["status"] in DEFINITIVE
                  and concrete[row["case"]]["status"] in DEFINITIVE]
        reductions = sum(first["compute_us"] < second["compute_us"] for first, second in paired)
        refinements = sum(first["refinements"] for first, _ in paired)
        lines.extend(["", "## PDR ablation", "",
                      f"Both PDR configurations reached a definitive verdict in {len(paired)} pairs. "
                      f"PDR/CEGAR was faster by compute time in {reductions} of those pairs. "
                      f"It made {refinements} refinement rounds across the paired runs."])
    lines.extend(["", "## Reading the raw results", "",
                  "The raw JSON Lines records include each budget, seed, model witness depth, work count, "
                  "and timing. Evidence IDs denote states of the finite model for certificates and "
                  "traces, and zero-based rule indices for static alerts.", "",
                  "Work counts states expanded for reachability and BMC, search steps for PDR, path and "
                  "flow rows for SmartAxe, sampled steps for BridgeFuzz, and exploration rounds for "
                  "Scutum. Refinement counts record abstraction refinements for PDR/CEGAR and blocked "
                  "infeasible candidates for Scutum.", ""])
    return "\n".join(lines)


# Set up the command-line options, select cases, prepare the engine, and write
# metadata. Each case produces an oracle row first. Later rows are written
# immediately to JSON Lines so completed measurements remain available if the
# run stops.
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--isabelle", default=os.environ.get("BRIDGE_ISABELLE", "isabelle"))
    parser.add_argument("--engine", type=Path, help="Use a previously built benchmark executable")
    parser.add_argument("--output", type=Path, default=HERE / "results")
    parser.add_argument("--case", action="append", help="Run a manifest case, such as once-reference/1")
    parser.add_argument("--oracle-only", action="store_true", help="Check only the reachability labels")
    parser.add_argument("--timeout", type=float, default=TIMEOUT_SECONDS, help="Wall seconds per job")
    args = parser.parse_args()
    if args.timeout <= 0 or not math.isfinite(args.timeout):
        parser.error("--timeout must be positive and finite")
    if sys.platform != "darwin" and not sys.platform.startswith("linux"):
        parser.error("the runner uses per-process RSS reporting on macOS or Linux")
    cases = load_cases()
    if args.case:
        unknown = set(args.case) - {case["key"] for case in cases}
        if unknown:
            parser.error(f"unknown case keys {', '.join(sorted(unknown))}")
        cases = [case for case in cases if case["key"] in args.case]

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    rows, failures = [], []
    with tempfile.TemporaryDirectory(prefix="bridge-engine-") as temp:
        if args.engine:
            engine = [str(args.engine.resolve())]
            metadata = {"runtime": "prebuilt executable"}
        else:
            engine, metadata = build_engine(args.isabelle, Path(temp), output)
        runtime_platform = f"{platform.system()} {platform.release()} {platform.machine()}"
        if Path("/.dockerenv").is_file():
            runtime_platform += " inside Docker"
        metadata.update({"platform": runtime_platform,
                         "budgets": FIXED_BUDGETS, "bmc_depths": BMC_DEPTHS, "fuzz_seeds": FUZZ_SEEDS,
                         "timeout_seconds": args.timeout, "case_keys": [case["key"] for case in cases]})
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
        with (output / "runs.jsonl").open("w", encoding="utf-8", buffering=1) as raw:
            for number, case in enumerate(cases, start=1):
                print(f"[{number}/{len(cases)}] {case['key']}", flush=True)
                oracle = None
                for method, budget, seed in jobs(args.oracle_only):
                    row = run_job(engine, case, method, budget, seed, args.timeout)
                    rows.append(row)
                    raw.write(json.dumps(row, sort_keys=True) + "\n")
                    failure = audit(case, row, oracle)
                    if failure:
                        failures.append(failure)
                    if method == "oracle":
                        if failure:
                            break
                        oracle = row

    (output / "report.md").write_text(report(cases, rows, metadata, failures), encoding="utf-8")
    print(f"Recorded {len(rows)} runs in {output}")
    return int(bool(failures))


# Python sets __name__ to "__main__" when this file is run directly. Calling
# sys.exit with main's result gives the shell a success or failure status.
if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError) as error:
        sys.exit(str(error))
