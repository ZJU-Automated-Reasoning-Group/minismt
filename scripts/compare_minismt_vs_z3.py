#!/usr/bin/env python3
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SAT_RE = re.compile(r"\b(sat|unsat|unknown)\b", re.IGNORECASE)
WARN_PATTERNS = [r"warning", r"unsupported", r"not supported"]
ERROR_PATTERNS = [r"error", r"panic", r"unimplemented", r"unknown (?:command|option|logic|sort|symbol)", r"failed to", r"cannot", r"segmentation fault", r"abort"]


@dataclass
class RunResult:
    exit_code: Optional[int]
    stdout: str
    stderr: str
    timed_out: bool


@dataclass
class Analysis:
    result: Optional[str]
    has_issue: bool
    issue_kind: Optional[str]
    issue_msg: Optional[str]


def find_on_path(cmd: str) -> Optional[str]:
    return shutil.which(cmd)


def default_minismt_bin(project_root: Path) -> Optional[str]:
    if env := os.environ.get("MINISMT_BIN"):
        if Path(env).exists():
            return env
    for candidate in [project_root / "target" / "debug" / "minismt", project_root / "target" / "release" / "minismt"]:
        if candidate.exists():
            #print(candidate)
            #exit(0)
            return str(candidate)
    return None


def default_z3_bin() -> Optional[str]:
    return find_on_path("z3") or find_on_path("z3.exe")


def run_command(cmd: List[str], timeout_s: int) -> RunResult:
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s)
        return RunResult(result.returncode, result.stdout, result.stderr, False)
    except subprocess.TimeoutExpired:
        return RunResult(None, "", "", True)


def first_sat_token(text: str) -> Optional[str]:
    if match := SAT_RE.search(text):
        return match.group(1).lower()
    return None


def collect_matches(patterns: List[str], text: str) -> List[str]:
    matches = []
    for pattern in patterns:
        for match in re.finditer(pattern, text, re.IGNORECASE):
            matches.append(match.group(0))
    return matches


def analyze_output(exit_code: Optional[int], stdout: str, stderr: str, timed_out: bool) -> Analysis:
    if timed_out:
        return Analysis(None, True, "timeout", "Command timed out")
    
    if exit_code != 0:
        return Analysis(None, True, "error", f"Exit code: {exit_code}")
    
    output = stdout + stderr
    warnings = collect_matches(WARN_PATTERNS, output)
    errors = collect_matches(ERROR_PATTERNS, output)
    
    if errors:
        return Analysis(None, True, "error", "; ".join(errors))
    if warnings:
        return Analysis(None, True, "warning", "; ".join(warnings))
    
    result = first_sat_token(output)
    return Analysis(result, False, None, None)


def gather_smt2_files(tests_dir: Path) -> List[Path]:
    return list(tests_dir.rglob("*.smt2"))


def build_minismt_command(minismt_bin: str, file_path: Path) -> List[str]:
    return [minismt_bin, str(file_path)]


def build_z3_command(z3_bin: str, file_path: Path, timeout_s: int) -> List[str]:
    return [z3_bin, "-smt2", "-T:" + str(timeout_s), str(file_path)]


def process_file(args_tuple: Tuple[Path, str, str, int, Path]) -> Tuple[str, Dict]:
    file_path, minismt_bin, z3_bin, timeout, project_root = args_tuple
    
    # Run minismt
    mini_cmd = build_minismt_command(minismt_bin, file_path)
    mini_run = run_command(mini_cmd, timeout)
    mini_analysis = analyze_output(mini_run.exit_code, mini_run.stdout, mini_run.stderr, mini_run.timed_out)
    
    # Run z3
    z3_cmd = build_z3_command(z3_bin, file_path, timeout)
    z3_run = run_command(z3_cmd, timeout)
    z3_analysis = analyze_output(z3_run.exit_code, z3_run.stdout, z3_run.stderr, z3_run.timed_out)
    
    rel = str(file_path.relative_to(project_root))
    return rel, {
        "minismt": asdict(mini_analysis) | {"exit_code": mini_run.exit_code},
        "z3": asdict(z3_analysis) | {"exit_code": z3_run.exit_code},
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Compare minismt vs z3 on .smt2 files")
    parser.add_argument("--tests-dir", default="tests", help="Directory containing .smt2 tests (recursive)")
    parser.add_argument("--minismt-bin", help="Path to minismt executable")
    parser.add_argument("--z3-bin", help="Path to z3 executable")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout in seconds")
    parser.add_argument("--report-json", default="comparison_report.json", help="Output JSON report path")
    parser.add_argument("--workers", type=int, default=os.cpu_count(), help="Number of parallel workers")
    args = parser.parse_args()
    
    project_root = Path(__file__).parent.parent
    tests_dir = project_root / args.tests_dir
    
    minismt_bin = args.minismt_bin or default_minismt_bin(project_root)
    if not minismt_bin:
        print("Could not find minismt binary. Set MINISMT_BIN or --minismt-bin.", file=sys.stderr)
        return 2
    
    z3_bin = args.z3_bin or default_z3_bin()
    if not z3_bin:
        print("Could not find z3 on PATH. Set Z3_BIN or --z3-bin.", file=sys.stderr)
        return 2
    
    smt2_files = gather_smt2_files(tests_dir)
    if not smt2_files:
        print(f"No .smt2 files found under {tests_dir}")
        return 0
    
    print(f"Processing {len(smt2_files)} files with {args.workers} workers...")
    
    # Prepare arguments for parallel processing
    args_list = [(f, minismt_bin, z3_bin, args.timeout, project_root) for f in smt2_files]
    
    # Process files in parallel
    results = {}
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        future_to_file = {executor.submit(process_file, args_tuple): args_tuple for args_tuple in args_list}
        
        for future in as_completed(future_to_file):
            try:
                rel, result = future.result()
                results[rel] = result
                print(f"✓ {rel}")
            except Exception as e:
                file_path = future_to_file[future][0]
                rel = str(file_path.relative_to(project_root))
                print(f"✗ {rel}: {e}")
                results[rel] = {"error": str(e)}
    
    # Analyze results
    inconsistent = []
    z3_success_minismt_issue = []
    skipped_both_issue = []
    
    for rel, result in results.items():
        if "error" in result:
            continue
            
        # Extract only the Analysis fields, excluding exit_code
        mini_data = {k: v for k, v in result["minismt"].items() if k != "exit_code"}
        z3_data = {k: v for k, v in result["z3"].items() if k != "exit_code"}
        
        mini_analysis = Analysis(**mini_data)
        z3_analysis = Analysis(**z3_data)
        
        if mini_analysis.has_issue and z3_analysis.has_issue:
            skipped_both_issue.append(rel)
        elif mini_analysis.result and z3_analysis.result and mini_analysis.result != z3_analysis.result:
            inconsistent.append(rel)
        elif z3_analysis.result and not z3_analysis.has_issue and mini_analysis.has_issue:
            z3_success_minismt_issue.append({
                "file": rel,
                "minismt_issue_kind": mini_analysis.issue_kind or "issue",
                "minismt_issue_msg": (mini_analysis.issue_msg or "").strip(),
            })
    
    # Generate report
    report = {
        "total_files": len(smt2_files),
        "skipped_both_issue_count": len(skipped_both_issue),
        "inconsistent_count": len(inconsistent),
        "z3_success_minismt_issue_count": len(z3_success_minismt_issue),
        "skipped_both_issue": skipped_both_issue,
        "inconsistent": inconsistent,
        "z3_success_minismt_issue": z3_success_minismt_issue,
        "details": results,
    }
    
    report_path = (project_root / args.report_json).resolve()
    with open(report_path, "w", encoding="utf-8") as fp:
        json.dump(report, fp, indent=2, sort_keys=False)
    
    print(f"\nTotal .smt2 files: {len(smt2_files)}")
    print(f"Skipped (both warning/error): {len(skipped_both_issue)}")
    print(f"Inconsistent results: {len(inconsistent)}")
    print(f"Z3 success but minismt warning/error: {len(z3_success_minismt_issue)}")
    print(f"Report written to: {report_path}")
    
    return 1 if inconsistent else 0


if __name__ == "__main__":
    sys.exit(main())


