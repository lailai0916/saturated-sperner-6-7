#!/usr/bin/env bash

set -Eeuo pipefail
IFS=$'\n\t'
export LC_ALL=C

package_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
if [[ -d "$package_dir/repository" ]]; then
  artifact_root=$package_dir
else
  artifact_root=$(cd -- "$package_dir/../../.." && pwd -P)
fi
repository_dir="$artifact_root/repository"
if [[ ! -d "$repository_dir" ]]; then
  repository_dir=$artifact_root
fi

if [[ -n ${P0054_REPLAY_LOG_DIR:-} ]]; then
  log_dir=$P0054_REPLAY_LOG_DIR
  if [[ -e "$log_dir" ]]; then
    printf 'Refusing to overwrite replay output: %s\n' "$log_dir" >&2
    exit 73
  fi
  mkdir -p "$log_dir"
else
  mkdir -p "$artifact_root/replay-logs"
  log_dir=$(mktemp -d "$artifact_root/replay-logs/run.XXXXXX")
fi

main_log="$log_dir/core-replay.log"
steps_file="$log_dir/steps.ndjson"
result_file="$log_dir/result.json"
: > "$main_log"
: > "$steps_file"

run_started_epoch=$(date +%s)
run_started_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
current_step=initialization

append_step_record() {
  python3 - "$steps_file" "$1" "$2" "$3" "$4" "$5" "$6" <<'PY'
import json
import sys

path, name, command, started, ended, duration, exit_code = sys.argv[1:]
record = {
    "name": name,
    "command": command,
    "started_at_utc": started,
    "ended_at_utc": ended,
    "wall_seconds": int(duration),
    "exit_code": int(exit_code),
    "status": "PASS" if int(exit_code) == 0 else "FAIL",
}
with open(path, "a", encoding="utf-8") as handle:
    handle.write(json.dumps(record, sort_keys=True) + "\n")
PY
}

run_step() {
  local step_name=$1
  shift
  current_step=$step_name
  local started_utc ended_utc started_epoch ended_epoch command_string rc
  started_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  started_epoch=$(date +%s)
  printf -v command_string '%q ' "$@"
  command_string=${command_string% }

  set +e
  {
    printf '[P0054_STEP_START] %s\n' "$step_name"
    printf '[P0054_COMMAND] %s\n' "$command_string"
    "$@"
  } 2>&1 | tee -a "$main_log" "$log_dir/$step_name.log"
  rc=${PIPESTATUS[0]}
  set -e

  ended_epoch=$(date +%s)
  ended_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  append_step_record "$step_name" "$command_string" "$started_utc" \
    "$ended_utc" "$((ended_epoch - started_epoch))" "$rc"
  printf '[P0054_STEP_END] %s exit=%s\n' "$step_name" "$rc" | \
    tee -a "$main_log"
  return "$rc"
}

finalize_replay() {
  local original_rc=$?
  trap - EXIT
  local ended_epoch ended_utc final_rc
  ended_epoch=$(date +%s)
  ended_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  final_rc=$original_rc

  python3 - "$result_file" "$steps_file" "$main_log" "$log_dir/lake_build.log" \
    "$log_dir/lean_main.log" "$original_rc" "$current_step" \
    "$run_started_utc" "$ended_utc" "$((ended_epoch - run_started_epoch))" <<'PY' || final_rc=$?
import json
import sys
from pathlib import Path

(
    result_path,
    steps_path,
    main_log_path,
    lake_log_path,
    lean_log_path,
    exit_code,
    failed_step,
    started,
    ended,
    duration,
) = sys.argv[1:]

steps_file = Path(steps_path)
steps = [
    json.loads(line)
    for line in steps_file.read_text(encoding="utf-8").splitlines()
    if line
]
lake_text = Path(lake_log_path).read_text(encoding="utf-8") if Path(lake_log_path).is_file() else ""
lean_text = Path(lean_log_path).read_text(encoding="utf-8") if Path(lean_log_path).is_file() else ""

theorem_types = {
    "sat6": (
        "AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty : "
        "AiMathLab.SaturatedSperner.IsStableSaturationNumber 6 30"
    ),
    "sat7": (
        "AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five : "
        "AiMathLab.SaturatedSperner.IsStableSaturationNumber 7 55"
    ),
}
type_matches = {name: expected in lean_text for name, expected in theorem_types.items()}
axiom_boundary = "[propext, Classical.choice, Quot.sound]"
axiom_boundary_count = lean_text.count(axiom_boundary)
axiom_boundary_matches = axiom_boundary_count >= 2
warning_count = sum("warning:" in line.lower() for line in lake_text.splitlines())
build_targets = ["AiMathLab", "AiMathLab.P0054Sat7StableExact"]

exit_code_i = int(exit_code)
postconditions_ok = all(type_matches.values()) and axiom_boundary_matches
if exit_code_i == 0 and not postconditions_ok:
    exit_code_i = 1
    failed_step = "lean_output_postconditions"

result = {
    "schema": "mathesis.p0054.core-replay.v1",
    "status": "PASS" if exit_code_i == 0 else "FAIL",
    "exit_code": exit_code_i,
    "failed_step": None if exit_code_i == 0 else failed_step,
    "started_at_utc": started,
    "ended_at_utc": ended,
    "wall_seconds": int(duration),
    "steps": steps,
    "lean": {
        "build_targets": build_targets,
        "build_target_count": len(build_targets),
        "build_warning_count": warning_count,
        "theorem_types": theorem_types,
        "theorem_type_matches": type_matches,
        "expected_final_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "axiom_boundary_occurrences": axiom_boundary_count,
        "axiom_boundary_matches": axiom_boundary_matches,
    },
    "logs": {
        "combined": Path(main_log_path).name,
        "steps": Path(steps_path).name,
    },
}
Path(result_path).write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
raise SystemExit(exit_code_i)
PY

  printf 'P0054 core replay summary: %s\n' "$result_file"
  if [[ $final_rc -eq 0 ]]; then
    printf '%s\n' 'P0054 core replay: PASS'
  else
    printf '%s\n' 'P0054 core replay: FAIL' >&2
  fi
  exit "$final_rc"
}
trap finalize_replay EXIT

scan_forbidden_constructs() {
  if rg -n --glob '*.lean' \
    '\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b' \
    AiMathLab Problems/P0054/formal; then
    printf '%s\n' 'Forbidden Lean construct found.' >&2
    return 1
  fi

  if rg -n --glob '*.lean' \
    '\b(sorryAx|Lean\.ofReduceBool|implemented_by)\b' \
    AiMathLab Problems/P0054/formal; then
    printf '%s\n' 'Lean proof bypass found.' >&2
    return 1
  fi
}

if [[ -x "$artifact_root/verify-integrity.sh" ]]; then
  run_step package_integrity "$artifact_root/verify-integrity.sh"
fi

cd "$repository_dir"
run_step forbidden_scan scan_forbidden_constructs
run_step lake_build lake build AiMathLab AiMathLab.P0054Sat7StableExact
run_step lean_main lake env lean Problems/P0054/formal/Main.lean
run_step uv_sync uv sync --locked --python 3.12
run_step size55_verifier uv run python -m scripts.p0054_verify_candidate
run_step sat6_replay env UV_OFFLINE=1 PYTHONDONTWRITEBYTECODE=1 uv run --offline \
  python Problems/P0054/experiments/sat6-exact/search.py \
  --verify-results Problems/P0054/experiments/sat6-exact/results.json
run_step p0054_tests uv run pytest tests/test_p0054_*.py
