"""Dual finite verification and restricted CEGAR calibration for P0053.

All conclusions produced here are finite ``COMPUTED`` evidence.  In
particular, the target search is restricted to the 56 one-member deletions of
the published 56-template family; it is not a search over arbitrary families.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import platform
import re
import resource
import subprocess
import sys
import time
from collections.abc import Iterable, Sequence
from datetime import UTC, datetime
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
from typing import Any

import z3  # type: ignore[import-untyped]

CERTIFICATE_PATH = Path("Problems/P0053/experiments/published-56-certificate.json")
RESULTS_PATH = Path("Problems/P0053/experiments/calibration-results.json")
AUDIT_PATH = Path("Problems/P0053/experiments/definition-audit.md")
REPORT_PATH = Path("Problems/P0053/experiments/feasibility-report.md")
SOURCE_PACK_PATH = Path("Problems/P0053/literature/source-pack.md")
SCRIPT_PATH = Path("scripts/p0053_sat7.py")
TEST_PATH = Path("tests/test_p0053_sat7.py")

PUBLISHED_TEMPLATES: dict[str, tuple[str, ...]] = {
    "A0": ("",),
    "A1": ("2", "3", "5", "6", "7", "14H"),
    "A2_small": ("12", "23", "34", "45", "56", "67", "17"),
    "A2_large": ("357H", "146H", "257H", "136H", "247H", "135H", "246H"),
    "A3_small": ("126", "237", "134", "245", "356", "467", "157"),
    "A3_large": (
        "3457H",
        "1456H",
        "2567H",
        "1367H",
        "1247H",
        "1235H",
        "2346H",
    ),
    "A4_from_A2_small": (
        "34567H",
        "14567H",
        "12567H",
        "12367H",
        "12347H",
        "12345H",
        "23456H",
    ),
    "A4_from_A2_large": ("1246", "2357", "1346", "2457", "1356", "2467", "1357"),
    "A5": ("134567H", "124567H", "123467H", "123457H", "123456H", "23567"),
    "A6": ("1234567H",),
}

LAYER_GROUPS: tuple[tuple[str, ...], ...] = (
    ("A0",),
    ("A1",),
    ("A2_small", "A2_large"),
    ("A3_small", "A3_large"),
    ("A4_from_A2_small", "A4_from_A2_large"),
    ("A5",),
    ("A6",),
)


def mask_from_members(members: Iterable[int]) -> int:
    """Encode one-based ground-set labels as an integer bit mask."""

    mask = 0
    for member in members:
        if member < 1:
            raise ValueError("ground-set labels must be positive")
        mask |= 1 << (member - 1)
    return mask


def members_from_mask(mask: int, n: int) -> list[int]:
    """Decode a mask into increasing one-based labels."""

    return [index + 1 for index in range(n) if mask & (1 << index)]


def parse_template(template: str, homogeneous_atom: frozenset[int]) -> int:
    """Expand one faithfully transcribed template from the frozen source pack."""

    ordinary = {int(character) for character in template if character.isdigit()}
    if "H" in template:
        ordinary.update(homogeneous_atom)
    return mask_from_members(ordinary)


def published_layers(h_size: int) -> dict[str, tuple[int, ...]]:
    """Return the published layers with H={8,...,7+h_size}."""

    if h_size < 1:
        raise ValueError("H must be nonempty; formal reproduction requires h_size >= 3")
    homogeneous_atom = frozenset(range(8, 8 + h_size))
    return {
        name: tuple(parse_template(template, homogeneous_atom) for template in templates)
        for name, templates in PUBLISHED_TEMPLATES.items()
    }


def published_family(h_size: int) -> tuple[int, ...]:
    """Return the canonical 56-member published family for the chosen H size."""

    layers = published_layers(h_size)
    family = tuple(member for group in LAYER_GROUPS for name in group for member in layers[name])
    return tuple(sorted(family, key=lambda member: (member.bit_count(), member)))


def standard_family(k: int, h_size: int = 3) -> tuple[int, tuple[int, ...]]:
    """Return P(Y) union {S union H:S in P(Y)}, with |Y|=k-2."""

    if k < 2 or h_size < 1:
        raise ValueError("standard calibration requires k >= 2 and nonempty H")
    y_size = k - 2
    h_mask = mask_from_members(range(y_size + 1, y_size + h_size + 1))
    family: list[int] = []
    for subset in range(1 << y_size):
        family.extend((subset, subset | h_mask))
    return y_size + h_size, tuple(sorted(family, key=lambda member: (member.bit_count(), member)))


def _chain_from_predecessors(end: int, predecessor: dict[int, int | None]) -> list[int]:
    chain: list[int] = []
    current: int | None = end
    while current is not None:
        chain.append(current)
        current = predecessor[current]
    chain.reverse()
    return chain


def verify_bitmask(n: int, k: int, family_input: Sequence[int]) -> dict[str, Any]:
    """Verifier A: exact integer-bitmask containment DP and exhaustive saturation."""

    started = time.perf_counter()
    universe_size = 1 << n
    if n < 0 or k < 1:
        return {"valid": False, "failure_type": "invalid_parameters"}
    if len(set(family_input)) != len(family_input):
        duplicate = next(member for member in family_input if family_input.count(member) > 1)
        return {
            "valid": False,
            "failure_type": "duplicate_member",
            "witness": members_from_mask(duplicate, n),
        }
    if any(member < 0 or member >= universe_size for member in family_input):
        invalid = next(member for member in family_input if member < 0 or member >= universe_size)
        return {"valid": False, "failure_type": "member_outside_ground_set", "witness": invalid}

    family = tuple(sorted(family_input, key=lambda member: (member.bit_count(), member)))
    family_set = set(family)
    longest_end: dict[int, int] = {}
    predecessor: dict[int, int | None] = {}
    pair_comparisons = 0
    for index, member in enumerate(family):
        best_length = 1
        best_predecessor: int | None = None
        for candidate in family[:index]:
            pair_comparisons += 1
            if candidate != member and candidate & member == candidate:
                candidate_length = longest_end[candidate] + 1
                if candidate_length > best_length:
                    best_length = candidate_length
                    best_predecessor = candidate
        longest_end[member] = best_length
        predecessor[member] = best_predecessor
        if best_length >= k + 1:
            chain = _chain_from_predecessors(member, predecessor)[-(k + 1) :]
            return {
                "validator": "A_integer_bitmask_poset_dp",
                "valid": False,
                "chain_free": False,
                "saturated": False,
                "failure_type": "existing_long_chain",
                "witness": {"chain": [members_from_mask(item, n) for item in chain]},
                "family_size": len(family),
                "universe_size": universe_size,
                "external_sets_checked": 0,
                "pair_comparisons": pair_comparisons,
                "runtime_seconds": time.perf_counter() - started,
            }

    longest_start: dict[int, int] = {}
    successor: dict[int, int | None] = {}
    for reverse_index, member in enumerate(reversed(family)):
        best_length = 1
        best_successor: int | None = None
        for candidate in tuple(reversed(family))[:reverse_index]:
            pair_comparisons += 1
            if member != candidate and member & candidate == member:
                candidate_length = longest_start[candidate] + 1
                if candidate_length > best_length:
                    best_length = candidate_length
                    best_successor = candidate
        longest_start[member] = best_length
        successor[member] = best_successor

    external_checked = 0
    external_members = sorted(
        (member for member in range(universe_size) if member not in family_set),
        key=lambda member: (member.bit_count(), member),
    )
    for outside in external_members:
        external_checked += 1
        lower_candidates = [
            member for member in family if member != outside and member & outside == member
        ]
        upper_candidates = [
            member for member in family if member != outside and member & outside == outside
        ]
        lower_end = max(lower_candidates, key=lambda member: longest_end[member], default=None)
        upper_start = max(upper_candidates, key=lambda member: longest_start[member], default=None)
        lower_length = 0 if lower_end is None else longest_end[lower_end]
        upper_length = 0 if upper_start is None else longest_start[upper_start]
        if lower_length + 1 + upper_length < k + 1:
            return {
                "validator": "A_integer_bitmask_poset_dp",
                "valid": False,
                "chain_free": True,
                "saturated": False,
                "failure_type": "uncovered_external_set",
                "witness": {
                    "external_set": members_from_mask(outside, n),
                    "lower_chain_length": lower_length,
                    "upper_chain_length": upper_length,
                    "combined_length": lower_length + 1 + upper_length,
                },
                "family_size": len(family),
                "universe_size": universe_size,
                "external_sets_checked": external_checked,
                "pair_comparisons": pair_comparisons,
                "runtime_seconds": time.perf_counter() - started,
            }

    return {
        "validator": "A_integer_bitmask_poset_dp",
        "valid": True,
        "chain_free": True,
        "saturated": True,
        "failure_type": None,
        "witness": None,
        "family_size": len(family),
        "universe_size": universe_size,
        "external_sets_checked": external_checked,
        "pair_comparisons": pair_comparisons,
        "runtime_seconds": time.perf_counter() - started,
    }


def verify_frozenset_dag(n: int, k: int, family_input: Sequence[int]) -> dict[str, Any]:
    """Verifier B: independent frozenset DAG and exhaustive powerset traversal."""

    started = time.perf_counter()
    ground = frozenset(range(1, n + 1))
    decoded: list[frozenset[int]] = []
    for encoded in family_input:
        if encoded < 0:
            return {"valid": False, "failure_type": "member_outside_ground_set"}
        member = frozenset(
            index + 1 for index in range(max(n, encoded.bit_length())) if encoded >> index & 1
        )
        if not member <= ground:
            return {
                "valid": False,
                "failure_type": "member_outside_ground_set",
                "witness": sorted(member),
            }
        decoded.append(member)
    if len(set(decoded)) != len(decoded):
        duplicate = next(member for member in decoded if decoded.count(member) > 1)
        return {"valid": False, "failure_type": "duplicate_member", "witness": sorted(duplicate)}

    nodes = tuple(sorted(decoded, key=lambda member: (len(member), tuple(sorted(member)))))
    node_set = set(nodes)
    predecessors: dict[frozenset[int], tuple[frozenset[int], ...]] = {}
    successors: dict[frozenset[int], tuple[frozenset[int], ...]] = {}
    dag_edges = 0
    for node in nodes:
        predecessors[node] = tuple(candidate for candidate in nodes if candidate < node)
        successors[node] = tuple(candidate for candidate in nodes if node < candidate)
        dag_edges += len(successors[node])

    path_to: dict[frozenset[int], tuple[frozenset[int], ...]] = {}
    for node in nodes:
        incoming = predecessors[node]
        prefix = max((path_to[parent] for parent in incoming), key=len, default=())
        path_to[node] = (*prefix, node)
        if len(path_to[node]) >= k + 1:
            chain = path_to[node][-(k + 1) :]
            return {
                "validator": "B_frozenset_dag",
                "valid": False,
                "chain_free": False,
                "saturated": False,
                "failure_type": "existing_long_chain",
                "witness": {"chain": [sorted(member) for member in chain]},
                "family_size": len(nodes),
                "universe_size": 2**n,
                "external_sets_checked": 0,
                "dag_edges": dag_edges,
                "runtime_seconds": time.perf_counter() - started,
            }

    path_from: dict[frozenset[int], tuple[frozenset[int], ...]] = {}
    for node in reversed(nodes):
        outgoing = successors[node]
        suffix = max((path_from[child] for child in outgoing), key=len, default=())
        path_from[node] = (node, *suffix)

    external_checked = 0
    for subset_size in range(n + 1):
        for combination in itertools.combinations(range(1, n + 1), subset_size):
            outside = frozenset(combination)
            if outside in node_set:
                continue
            external_checked += 1
            lower_path = max(
                (path_to[node] for node in nodes if node < outside), key=len, default=()
            )
            upper_path = max(
                (path_from[node] for node in nodes if outside < node), key=len, default=()
            )
            if len(lower_path) + 1 + len(upper_path) < k + 1:
                return {
                    "validator": "B_frozenset_dag",
                    "valid": False,
                    "chain_free": True,
                    "saturated": False,
                    "failure_type": "uncovered_external_set",
                    "witness": {
                        "external_set": sorted(outside),
                        "lower_chain_length": len(lower_path),
                        "upper_chain_length": len(upper_path),
                        "combined_length": len(lower_path) + 1 + len(upper_path),
                    },
                    "family_size": len(nodes),
                    "universe_size": 2**n,
                    "external_sets_checked": external_checked,
                    "dag_edges": dag_edges,
                    "runtime_seconds": time.perf_counter() - started,
                }

    return {
        "validator": "B_frozenset_dag",
        "valid": True,
        "chain_free": True,
        "saturated": True,
        "failure_type": None,
        "witness": None,
        "family_size": len(nodes),
        "universe_size": 2**n,
        "external_sets_checked": external_checked,
        "dag_edges": dag_edges,
        "runtime_seconds": time.perf_counter() - started,
    }


def dual_verify(n: int, k: int, family: Sequence[int]) -> dict[str, Any]:
    """Run both independent validators and require verdict agreement."""

    first = verify_bitmask(n, k, family)
    second = verify_frozenset_dag(n, k, family)
    agreement = (
        first.get("valid") == second.get("valid")
        and first.get("chain_free") == second.get("chain_free")
        and first.get("saturated") == second.get("saturated")
        and first.get("failure_type") == second.get("failure_type")
    )
    if not agreement:
        raise AssertionError(f"independent validators disagree: A={first}, B={second}")
    return {"agreement": True, "validator_a": first, "validator_b": second}


def _semantic_hash(semantic: dict[str, Any]) -> str:
    encoded = json.dumps(semantic, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def family_sha256(n: int, k: int, family: Sequence[int]) -> str:
    """Hash only the finite instance's stable mathematical semantics."""

    semantic = {
        "n": n,
        "k": k,
        "canonical_family": [
            members_from_mask(member, n)
            for member in sorted(family, key=lambda item: (item.bit_count(), item))
        ],
    }
    return _semantic_hash(semantic)


def _without_runtime(result: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in result.items() if key != "runtime_seconds"}


def _dual_without_runtime(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "agreement": result["agreement"],
        "validator_a": _without_runtime(result["validator_a"]),
        "validator_b": _without_runtime(result["validator_b"]),
    }


def _peak_rss_bytes() -> int:
    raw = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(raw if sys.platform == "darwin" else raw * 1024)


def _available_memory_bytes() -> int | None:
    """Best-effort local available-memory snapshot; never contacts the network."""

    if sys.platform == "darwin":
        completed = subprocess.run(
            ["vm_stat"],
            check=True,
            capture_output=True,
            text=True,
        )
        page_match = re.search(r"page size of (\d+) bytes", completed.stdout)
        if page_match is None:
            return None
        page_size = int(page_match.group(1))
        available_pages = 0
        for name in ("Pages free", "Pages inactive", "Pages speculative", "Pages purgeable"):
            match = re.search(rf"^{name}:\s+(\d+)\.$", completed.stdout, re.MULTILINE)
            if match is not None:
                available_pages += int(match.group(1))
        return page_size * available_pages
    meminfo = Path("/proc/meminfo")
    if meminfo.exists():
        match = re.search(r"^MemAvailable:\s+(\d+) kB$", meminfo.read_text(), re.MULTILINE)
        if match is not None:
            return int(match.group(1)) * 1024
    return None


def _package_version(package: str) -> str:
    try:
        return version(package)
    except PackageNotFoundError:
        return "NOT_INSTALLED"


def environment_record() -> dict[str, Any]:
    """Return auditable runtime versions without invoking the network."""

    return {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "platform": platform.platform(),
        "z3": z3.get_version_string(),
        "pytest": _package_version("pytest"),
        "ruff": _package_version("ruff"),
        "mypy": _package_version("mypy"),
        "cpu_count": os.cpu_count(),
    }


def compact_failure(result: dict[str, Any]) -> dict[str, Any]:
    """Keep only the deterministic, shortest failure certificate."""

    return {
        "failure_type": result.get("failure_type"),
        "witness": result.get("witness"),
        "external_sets_checked_before_failure": result.get("external_sets_checked"),
    }


def cegar_template_search(
    *,
    n: int,
    k: int,
    universe: Sequence[int],
    target_size: int,
    time_limit_seconds: float,
) -> dict[str, Any]:
    """Select template subfamilies in Z3 and reject them by exact dual checks.

    The only variables indicate whether a member of ``universe`` is retained.
    This is a deliberately restricted class and says nothing about families
    containing a set outside the supplied template universe.
    """

    started = time.perf_counter()
    variables = [z3.Bool(f"retain_{index}") for index in range(len(universe))]
    solver = z3.Solver()
    timeout_ms = max(1, int(time_limit_seconds * 1000))
    solver.set(timeout=timeout_ms)
    solver.add(z3.PbEq([(variable, 1) for variable in variables], target_size))
    preprocess_seconds = time.perf_counter() - started
    rounds: list[dict[str, Any]] = []
    blocker_count = 0
    while True:
        elapsed = time.perf_counter() - started
        if elapsed >= time_limit_seconds:
            status = "UNKNOWN_TIMEOUT"
            candidate = None
            break
        solver.set(timeout=max(1, int((time_limit_seconds - elapsed) * 1000)))
        check = solver.check()
        if check == z3.unsat:
            status = "UNSAT_IN_RESTRICTED_SEARCH_CLASS"
            candidate = None
            break
        if check == z3.unknown:
            status = "UNKNOWN_Z3"
            candidate = None
            break
        model = solver.model()
        selection = tuple(
            z3.is_true(model.evaluate(variable, model_completion=True)) for variable in variables
        )
        candidate = tuple(
            member for member, retained in zip(universe, selection, strict=True) if retained
        )
        checked = dual_verify(n, k, candidate)
        rounds.append(
            {
                "round": len(rounds) + 1,
                "selected_indices": [index for index, retained in enumerate(selection) if retained],
                "validator_a": compact_failure(checked["validator_a"]),
                "validator_b": compact_failure(checked["validator_b"]),
                "valid": checked["validator_a"]["valid"],
            }
        )
        if checked["validator_a"]["valid"]:
            status = "SAT_CONSTRUCTION_IN_RESTRICTED_SEARCH_CLASS"
            break
        solver.add(
            z3.Or(
                [
                    variable != z3.BoolVal(retained)
                    for variable, retained in zip(variables, selection, strict=True)
                ]
            )
        )
        blocker_count += 1

    runtime_seconds = time.perf_counter() - started
    return {
        "status": status,
        "candidate": None if candidate is None else list(candidate),
        "rounds": rounds,
        "metrics": {
            "boolean_variables": len(variables),
            "initial_constraints": 1,
            "cegar_blocking_constraints": blocker_count,
            "final_constraint_count": 1 + blocker_count,
            "preprocess_seconds": preprocess_seconds,
            "runtime_seconds": runtime_seconds,
            "peak_rss_bytes": _peak_rss_bytes(),
        },
    }


def _find_chain_making_external(
    n: int, k: int, family: tuple[int, ...]
) -> tuple[int, dict[str, Any]]:
    family_set = set(family)
    for outside in sorted(
        (member for member in range(1 << n) if member not in family_set),
        key=lambda member: (member.bit_count(), member),
    ):
        result = verify_bitmask(n, k, (*family, outside))
        if result.get("failure_type") == "existing_long_chain":
            return outside, result
    raise AssertionError("saturated family supplied no chain-making external set")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def build_certificate() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Build and dual-verify the formal minimum H=3 and H=4 instances."""

    family_h3 = published_family(3)
    family_h4 = published_family(4)
    check_h3 = dual_verify(10, 7, family_h3)
    check_h4 = dual_verify(11, 7, family_h4)
    layers = published_layers(3)
    semantic = {
        "source": {
            "citation": "Martin--Veldt, EJC 32(1) (2025), P1.55, printed pages 7--9",
            "frozen_source_pack": str(SOURCE_PACK_PATH),
            "formal_homogeneous_atom_condition": "|H|>2",
        },
        "k": 7,
        "ground_set": list(range(1, 11)),
        "homogeneous_atom": [8, 9, 10],
        "templates_by_source_group": {
            name: list(items) for name, items in PUBLISHED_TEMPLATES.items()
        },
        "expanded_source_groups": {
            name: [members_from_mask(member, 10) for member in members]
            for name, members in layers.items()
        },
        "layer_sizes": [sum(len(layers[name]) for name in group) for group in LAYER_GROUPS],
        "family_size": len(family_h3),
        "canonical_family": [members_from_mask(member, 10) for member in family_h3],
        "family_sha256_h3_n10": family_sha256(10, 7, family_h3),
        "family_sha256_h4_n11": family_sha256(11, 7, family_h4),
        "verification_h3": _dual_without_runtime(check_h3),
        "verification_h4": _dual_without_runtime(check_h4),
        "completeness_boundary": (
            "Finite exhaustive verification only for H=3 (n=10) and H=4 (n=11); "
            "it is not a proof for every H and not a lower bound for sat(7)."
        ),
    }
    certificate = {
        "schema": "ai-math-lab.p0053.published-56-certificate.v1",
        "epistemic_labels": ["LITERATURE", "COMPUTED"],
        "command": "uv run python scripts/p0053_sat7.py calibrate --target-budget-seconds 900",
        "environment": environment_record(),
        "semantic": semantic,
        "semantic_sha256": _semantic_hash(semantic),
        "run": {
            "generated_at_utc": datetime.now(UTC).isoformat(),
            "h3_runtime_seconds": check_h3["validator_a"]["runtime_seconds"]
            + check_h3["validator_b"]["runtime_seconds"],
            "h4_runtime_seconds": check_h4["validator_a"]["runtime_seconds"]
            + check_h4["validator_b"]["runtime_seconds"],
            "peak_rss_bytes": _peak_rss_bytes(),
        },
    }
    return certificate, check_h3, check_h4


def build_calibration(target_budget_seconds: float) -> dict[str, Any]:
    """Run standards, regressions, and the exact one-deletion target class."""

    total_started = time.perf_counter()
    available_memory = _available_memory_bytes()
    memory_limit = 8 * 1024**3
    if available_memory is not None:
        memory_limit = min(memory_limit, available_memory // 2)
    standard_results: list[dict[str, Any]] = []
    model_growth: list[dict[str, Any]] = []
    for k in range(2, 6):
        n, family = standard_family(k)
        checked = dual_verify(n, k, family)
        model = cegar_template_search(
            n=n,
            k=k,
            universe=family,
            target_size=len(family),
            time_limit_seconds=min(30.0, target_budget_seconds),
        )
        standard_results.append(
            {
                "k": k,
                "n": n,
                "h_size": 3,
                "expected_family_size": 2 ** (k - 1),
                "canonical_family": [members_from_mask(member, n) for member in family],
                "family_sha256": family_sha256(n, k, family),
                "verification": _dual_without_runtime(checked),
                "model_status": model["status"],
            }
        )
        model_growth.append({"k": k, "n": n, "family_size": len(family), **model["metrics"]})

    family = published_family(3)
    deleted_family = family[1:]
    deleted = dual_verify(10, 7, deleted_family)
    added_member, _ = _find_chain_making_external(10, 7, family)
    added = dual_verify(10, 7, (*family, added_member))
    wrong_atom_family = published_family(2)
    wrong_atom = dual_verify(10, 7, wrong_atom_family)
    regressions: list[dict[str, Any]] = [
        {
            "name": "delete_empty_set_from_published_56",
            "mutation": {"deleted_member": []},
            "family_sha256": family_sha256(10, 7, deleted_family),
            "verification": _dual_without_runtime(deleted),
        },
        {
            "name": "add_external_set_that_creates_an_8_chain",
            "mutation": {"added_member": members_from_mask(added_member, 10)},
            "family_sha256": family_sha256(10, 7, (*family, added_member)),
            "verification": _dual_without_runtime(added),
        },
        {
            "name": "split_homogeneous_atom_by_using_only_8_9_and_leaving_10_outside",
            "mutation": {"incorrect_H": [8, 9], "ground_set_still": list(range(1, 11))},
            "family_sha256": family_sha256(10, 7, wrong_atom_family),
            "verification": _dual_without_runtime(wrong_atom),
        },
    ]
    if any(item["verification"]["validator_a"]["valid"] for item in regressions):
        raise AssertionError("a deliberate regression was not detected")

    target = cegar_template_search(
        n=10,
        k=7,
        universe=family,
        target_size=55,
        time_limit_seconds=target_budget_seconds,
    )
    target_semantic = {key: value for key, value in target.items() if key != "metrics"}
    semantic = {
        "standard_constructions": standard_results,
        "regressions": regressions,
        "restricted_search_class": {
            "label": "RESTRICTED_SEARCH_CLASS",
            "definition": (
                "Exactly the 55-member subfamilies obtained by deleting one member from the "
                "published H=3,n=10 56-member family. No set outside that template universe "
                "is allowed."
            ),
            "candidate_count": 56,
            "template_universe_sha256": family_sha256(10, 7, family),
            "covered_sizes": [55],
            "excluded_from_scope": [
                "arbitrary 55-member families",
                "families of size at most 54",
                "other ground-set sizes",
                "all eventual homogeneous-atom families",
            ],
            "target_result": target_semantic,
        },
        "completeness_boundary": (
            "UNSAT, if obtained, applies only to the 56 exact one-deletion candidates above. "
            "UNKNOWN or timeout is not a proof. No result implies sat(7)>=56."
        ),
        "gate_recommendation": "DO_NOT_PROMOTE",
    }
    return {
        "schema": "ai-math-lab.p0053.calibration-results.v1",
        "epistemic_label": "COMPUTED",
        "command": (
            "uv run python scripts/p0053_sat7.py calibrate "
            f"--target-budget-seconds {target_budget_seconds:g}"
        ),
        "environment": environment_record(),
        "parameters": {
            "k": 7,
            "target_size": 55,
            "target_budget_seconds": target_budget_seconds,
            "memory_limit_policy": "min(8 GiB, 50 percent of available memory at run start)",
            "memory_limit_bytes_at_run_start": memory_limit,
            "network": "FORBIDDEN_AND_NOT_USED",
        },
        "semantic": semantic,
        "semantic_sha256": _semantic_hash(semantic),
        "run": {
            "generated_at_utc": datetime.now(UTC).isoformat(),
            "total_runtime_seconds": time.perf_counter() - total_started,
            "peak_rss_bytes": _peak_rss_bytes(),
            "available_memory_bytes_at_run_start": available_memory,
            "small_model_growth": model_growth,
            "target_metrics": target["metrics"],
        },
    }


def write_markdown(certificate: dict[str, Any], results: dict[str, Any]) -> None:
    """Write the proof audit and finite feasibility report."""

    cert_hash = certificate["semantic_sha256"]
    result_hash = results["semantic_sha256"]
    target = results["semantic"]["restricted_search_class"]["target_result"]
    h3_a = certificate["semantic"]["verification_h3"]["validator_a"]
    h3_b = certificate["semantic"]["verification_h3"]["validator_b"]
    h4_a = certificate["semantic"]["verification_h4"]["validator_a"]
    h4_b = certificate["semantic"]["verification_h4"]["validator_b"]
    audit = f"""# P0053 definition audit

## Exact finite predicate

`DEFINITION`: for a finite ground set `X`, a family `F` is saturated
`k`-Sperner exactly when (i) `F` contains no strict chain of length `k+1`, and
(ii) every `S in P(X)\\F` belongs to a strict `(k+1)`-chain in `F union {{S}}`.
Both validators enumerate every external `S`; neither samples.

## DP criterion

`DEFINITION`: for external `S`, let `lower_chain_len(S)` be the maximum length
of a strict chain of members of `F` all strictly below `S`; use `0` when there
is no such member. Define `upper_chain_len(S)` analogously for chains strictly
above `S`, again using `0` for the empty side.

`PROVED`: assuming `F` is `k`-Sperner, adding `S` creates a strict
`(k+1)`-chain through `S` if and only if

```text
lower_chain_len(S) + 1 + upper_chain_len(S) >= k + 1.
```

Forward direction: remove `S` from any strict `(k+1)`-chain through it. The
members before `S` form a strict lower chain and those after it form a strict
upper chain, so the displayed sum is at least `k+1`. Reverse direction: choose
maximizing lower and upper chains. Every lower endpoint is a strict subset of
`S`, and `S` is a strict subset of every upper endpoint, so concatenating the
lower chain, the singleton endpoint `S`, and the upper chain is strict. If it
is longer than `k+1`, any consecutive `k+1` members containing `S` give the
required chain. The conventions of length `0` handle empty lower or upper
sides without inventing an endpoint. Since `S` is external, equality with a
family member cannot occur.

## Independence and coverage

`COMPUTED`: verifier A uses integer masks and two poset DPs. Verifier B decodes
fresh `frozenset` objects, builds a strict-inclusion DAG, constructs paths, and
independently enumerates the powerset by combinations. B does not call A's
normalization, DP, containment, or powerset code. Tests mechanically monkeypatch
A to fail while B continues and inspect B's referenced names.

`COMPUTED`: the faithful H=3 instance has 56 distinct members on n=10; A and B
checked {h3_a["external_sets_checked"]} and {h3_b["external_sets_checked"]}
external sets. The H=4 instance has 56 members on n=11; A and B checked
{h4_a["external_sets_checked"]} and {h4_b["external_sets_checked"]} external
sets. Both instances are chain-free and saturated in these finite universes.

`DEFINITION`: these computations do not prove the parameterized construction
for every `|H|>2`, an eventual upper bound improvement, or `sat(7)>=56`.

Certificate semantic SHA-256: `{cert_hash}`.
Results semantic SHA-256: `{result_hash}`.
"""
    AUDIT_PATH.write_text(audit, encoding="utf-8")

    growth_rows = "\n".join(
        f"| {item['k']} | {item['n']} | {item['family_size']} | "
        f"{item['boolean_variables']} | {item['initial_constraints']} | "
        f"{item['runtime_seconds']:.6f} | {item['peak_rss_bytes']} |"
        for item in results["run"]["small_model_growth"]
    )
    target_metrics = results["run"]["target_metrics"]
    report = f"""# P0053 finite feasibility calibration

## Outcome

`DEFINITION`: gate recommendation: `DO_NOT_PROMOTE`. The exact one-deletion
class is auditable, but it is too narrow to calibrate a faithful general
`size<=55` search within the required two-hour and 8 GiB promotion forecast.

`COMPUTED`: the published 56-member family was reproduced member by member and
passed both exhaustive validators for formal-minimum `H=3,n=10` and for
`H=4,n=11`. Standard `2^(k-1)` families passed both validators for
`k=2,3,4,5`, each with `|H|=3` and `n=k+1`. All three deliberate mutations
were rejected by both validators.

## Candidate model

`DEFINITION — RESTRICTED_SEARCH_CLASS`: Z3 has one Boolean retain variable per
member of the published H=3 family and requires exactly 55 of 56 variables.
Each model is checked from scratch by A and B. Every round saves the shortest
failure witness, then an exact assignment no-good clause blocks that assignment;
the witness is not used as a derived Z3 cut. Thus this run covers exactly the
56 one-member deletions and no arbitrary family, no size at most 54, and no
other ground set.

`COMPUTED`: target status is `{target["status"]}` after
{len(target["rounds"])} CEGAR rounds. The run used
{target_metrics["boolean_variables"]} Boolean variables,
{target_metrics["final_constraint_count"]} final constraints,
{target_metrics["preprocess_seconds"]:.6f} seconds preprocessing,
{target_metrics["runtime_seconds"]:.6f} seconds target wall time, and peak RSS
{target_metrics["peak_rss_bytes"]} bytes. The configured
{results["parameters"]["target_budget_seconds"]:g}-second budget was only a
maximum cap, not elapsed time; the actual target runtime was
{target_metrics["runtime_seconds"]:.6f} seconds.

| k | n | family size | variables | initial constraints | runtime (s) | peak RSS (bytes) |
|---:|---:|---:|---:|---:|---:|---:|
{growth_rows}

## Interpretation and boundary

`COMPUTED`: an UNSAT status here excludes only the published family's exact
one-deletion subfamilies. It cannot be extrapolated to all families of size 55
or less and supplies no lower bound for `sat(7)`. A timeout or `UNKNOWN` would
likewise be inconclusive. The model's 56-candidate growth is too narrow to
estimate a faithful general search, so this calibration alone does not justify
a claim that a meaningful unrestricted search fits within two hours and 8 GiB.

`UNKNOWN`: whether a family of size at most 55 exists remains unresolved by
this experiment. No novelty claim is made.

## Reproduction

```bash
uv run python scripts/p0053_sat7.py calibrate --target-budget-seconds 900
uv run pytest tests/test_p0053_sat7.py
uv run ruff check scripts/p0053_sat7.py tests/test_p0053_sat7.py
uv run mypy scripts/p0053_sat7.py tests/test_p0053_sat7.py
git diff --check
```

Certificate semantic SHA-256: `{cert_hash}`.
Results semantic SHA-256: `{result_hash}`.
"""
    REPORT_PATH.write_text(report, encoding="utf-8")


def calibrate(target_budget_seconds: float) -> tuple[dict[str, Any], dict[str, Any]]:
    """Generate all four P0053 experiment artifacts."""

    if not 0 < target_budget_seconds <= 900:
        raise ValueError("target budget must lie in (0, 900] seconds")
    certificate, _, _ = build_certificate()
    results = build_calibration(target_budget_seconds)
    _write_json(CERTIFICATE_PATH, certificate)
    _write_json(RESULTS_PATH, results)
    write_markdown(certificate, results)
    return certificate, results


def verify_saved_artifacts() -> None:
    """Check hashes and re-run the saved published certificate from scratch."""

    certificate = json.loads(CERTIFICATE_PATH.read_text(encoding="utf-8"))
    results = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
    if certificate["semantic_sha256"] != _semantic_hash(certificate["semantic"]):
        raise AssertionError("published certificate semantic hash mismatch")
    if results["semantic_sha256"] != _semantic_hash(results["semantic"]):
        raise AssertionError("calibration results semantic hash mismatch")
    family = tuple(
        mask_from_members(member) for member in certificate["semantic"]["canonical_family"]
    )
    checked = dual_verify(10, 7, family)
    if not checked["validator_a"]["valid"]:
        raise AssertionError("saved published family failed fresh dual verification")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    calibrate_parser = subparsers.add_parser("calibrate")
    calibrate_parser.add_argument("--target-budget-seconds", type=float, default=900.0)
    subparsers.add_parser("verify-artifacts")
    args = parser.parse_args()
    if args.command == "calibrate":
        certificate, results = calibrate(args.target_budget_seconds)
        status = results["semantic"]["restricted_search_class"]["target_result"]["status"]
        print(f"COMPUTED published-56 semantic_sha256={certificate['semantic_sha256']}")
        print(f"COMPUTED calibration semantic_sha256={results['semantic_sha256']}")
        print(f"RESTRICTED_SEARCH_CLASS target_status={status}")
    else:
        verify_saved_artifacts()
        print("COMPUTED saved artifacts and dual certificate verification PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
