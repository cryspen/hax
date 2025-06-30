#!/usr/bin/env python3

import argparse
import subprocess
import os
import sys
from pathlib import Path
import shutil
import filecmp
import difflib

CONFIG_FILE = "test_config.yaml"

def compare_and_store_outputs(target, base_dir="proofs", store_dir="snapshots", update_snapshots = False):
    actual_dir = Path(base_dir) / target / "extraction"
    expected_dir = Path(store_dir) / target

    if not actual_dir.exists():
        print(f"[WARN] Output dir not found: {actual_dir}")
        return True  # No outputs to check

    unstable = False
    
    # Only consider .v and .fst files
    valid_extensions = {".fst", ".v"}
    files_to_check = [f for f in actual_dir.rglob("*") if f.is_file() and f.suffix in valid_extensions]


    for file in files_to_check:
        if file.is_file():
            rel_path = file.relative_to(actual_dir)
            expected_file = expected_dir / rel_path

            if expected_file.exists():
                if not filecmp.cmp(file, expected_file, shallow=False):
                    if update_snapshots:
                        shutil.copy(file, expected_file)
                        print(f"✅ Stored new reference for file: {expected_file}")
                    else:
                        print(f"❌ File mismatch: {rel_path}")
                        show_file_diff(expected_file, file)
                        unstable = True
            else:
                # First time: store it
                expected_file.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(file, expected_file)
                print(f"✅ Stored new reference file: {expected_file}")

    return not unstable

def cleanup_extraction(base_dir="proofs"):
    actual_dir = Path(base_dir)

    if not actual_dir.exists():
        print(f"[WARN] Output dir not found: {actual_dir}")
        return True  # No outputs to check
    
    # Only consider .v and .fst files
    valid_extensions = {".v", ".fst"}
    files_to_delete = [f for f in actual_dir.rglob("*") if f.is_file() and f.suffix in valid_extensions]


    for file in files_to_delete:
        if file.is_file():
            os.remove(file)

def show_file_diff(file1, file2):
    with open(file1, "r") as f1, open(file2, "r") as f2:
        lines1 = f1.readlines()
        lines2 = f2.readlines()
        diff = list(difflib.unified_diff(lines1, lines2, fromfile=str(file1), tofile=str(file2)))
        if diff:
            print("".join(diff))

def load_config(file_path):
    import yaml
    with open(file_path, "r") as f:
        return yaml.safe_load(f)

def run_command(cmd):
    result = subprocess.run(
        cmd, 
        stdout=subprocess.PIPE, 
        stderr=subprocess.STDOUT,  # Redirect stderr to stdout
        shell = True,
        text=True)
    return result

def cargo_cmd(test_name, target, feature):
    feature_flag = f"--features {feature}"
    target_filter = f"-i '-** +coverage::{test_name}::**'" if test_name else ""
    return f"cargo hax -C {feature_flag} \\; into {target_filter} {target}"

def run_fstar_lax(test_name, include_negative):
    cmd = cargo_cmd(test_name, "fstar", "json" if include_negative else "fstar-lax")
    extraction = run_command(cmd)
    if extraction.returncode != 0:
        return extraction
    return run_command("OTHERFLAGS='--admit_smt_queries true' make -C proofs/fstar/extraction")

def run_json_target():
    return run_command("cargo hax -C --features json \\; json")

def write_summary(results, stability):
    from tabulate import tabulate
    headers = ["Test", "Target", "Expected", "Actual"]
    if stability:
        headers.append("Stability")
    headers.append("Result")

    rows = []
    for r in results:
        row = [r['test'], r['target'], r['expected'], r['actual']]
        if stability:
            row.append(r.get("stability", "N/A"))
        row.append(r['result'])
        rows.append(row)

    table = tabulate(rows, headers=headers, tablefmt="github")
    summary = "## 🧪 Test Summary\n\n" + table + "\n"
    path = os.getenv("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a") as f:
            f.write(summary)
    else:
        print(summary)

def run_tests(config, target, include_negative, check_stability, update_snapshots):
    results = []
    all_targets = ["coq", "fstar", "fstar-lax", "json"]

    applicable_targets = [target] if target != "all" else all_targets
    
    if "json" in applicable_targets:
        json_result = run_json_target()
        rc = json_result.returncode
        if rc != 0:
            print(json_result.stdout)   
            results.append({
                "test": "cargo-hax-json",
                "target": "json",
                "expected": "✅ Pass",
                "actual": "✅ Pass" if rc == 0 else "❌ Fail",
                "result": "✅" if rc == 0 else "❌"
            })
            return results

    
    if target == "json":
        return results

    for test_name, targets in config["tests"].items():
        for t in applicable_targets:
            is_expected_to_run = t in targets
            should_run = is_expected_to_run or include_negative

            if not should_run:
                continue

            cleanup_extraction()

            if t == "fstar-lax":
                command_result = run_fstar_lax(test_name, include_negative)
            elif t == "json":
                command_result = json_result
            else:
                cmd = cargo_cmd(test_name, t, "json" if include_negative else t)
                command_result = run_command(cmd)

            rc = min(command_result.returncode, 1)

            expected_code = 0 if is_expected_to_run else 1
            passed = (rc == expected_code)

            result = {
                "test": test_name,
                "target": t,
                "expected": "✅ Pass" if is_expected_to_run else "❌ Fail",
                "actual": "✅ Pass" if rc == 0 else "❌ Fail",
                "result": "✅" if passed else "❌"
            }

            if check_stability and t in ["fstar"]:
                is_stable = compare_and_store_outputs(t, update_snapshots = update_snapshots)
                if not is_stable:
                    # optionally mark test as failed
                    result["stability"] = "❌"
                    result["result"] = "❌"
                else:
                    result["stability"] = "✅"

            print(result)
            
            if not passed:
                print(command_result.stdout)

            results.append(result)

    return results

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("target", choices=["coq", "fstar", "fstar-lax", "json", "all"], help="Test target")
    parser.add_argument("--config", help="Path to YAML config file")
    parser.add_argument("--with-negative", action="store_true", help="Also run non-enabled tests and expect them to fail")
    parser.add_argument("--check-stability", action="store_true", help="Compare output files to reference versions, applicable only in conjunction with with-negative")
    parser.add_argument("--update-snapshots", action="store_true", help="Store new reference versions of generated files, applicable only in conjunction with with-negative and check-stability")

    args = parser.parse_args()

    os.environ["RUSTFLAGS"] = "-C instrument-coverage"

    stability = args.check_stability and args.with_negative

    config = load_config(args.config) if args.config else load_config(CONFIG_FILE) if args.with_negative else {"tests" : {"": ["coq", "fstar", "fstar-lax"]}}
    results = run_tests(config, args.target, args.with_negative, stability, args.update_snapshots)
    if args.with_negative:
        write_summary(results, stability)
    else:
        print(results)
    # Exit with non-zero if any result failed (actual != expected)
    if any(r["result"] == "❌" for r in results):
        sys.exit(1)

if __name__ == "__main__":
    main()
