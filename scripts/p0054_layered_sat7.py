"""Exact calibration for smaller layered saturated 7-Sperner constructions.

The search class has a finite core ``C`` and one common homogeneous atom ``H``.
Every family member is either ``A`` or ``A ∪ H`` for ``A ⊆ C``.  Seven
pairwise-disjoint saturated antichains are required, and every member of layer
``i + 1`` must strictly contain a member of layer ``i``.

Results from a timeout-bounded Z3 run are only ``COMPUTED`` evidence.  An
``unsat`` answer is not promoted to a mathematical theorem without a separately
checkable proof certificate and a proved reduction from the stated class.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import itertools
import json
import subprocess
import time
from collections.abc import Iterable, Sequence
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal

import z3  # type: ignore[import-untyped]

_p0053 = importlib.import_module(
    "scripts.p0053_sat7" if __package__ else "p0053_sat7"
)
LAYER_GROUPS = _p0053.LAYER_GROUPS
PUBLISHED_TEMPLATES = _p0053.PUBLISHED_TEMPLATES

LAYER_COUNT = 7
RESULT_PATH = Path("Problems/P0054/experiments/calibration-results.json")
CERTIFICATE_DIRECTORY = Path("Problems/P0054/experiments/certificates")

AtomState = Literal["empty", "partial", "full"]


@dataclass(frozen=True, order=True)
class Template:
    """A set template: ``core_mask`` with either none or all of ``H``."""

    core_mask: int
    uses_atom: bool


@dataclass(frozen=True, order=True)
class Signature:
    """The comparability signature of an arbitrary subset of ``C ∪ H``."""

    core_mask: int
    atom_state: AtomState


@dataclass(frozen=True)
class Candidate:
    """Seven ordered layers in the template model."""

    core_size: int
    layers: tuple[tuple[Template, ...], ...]

    @property
    def total_size(self) -> int:
        return sum(len(layer) for layer in self.layers)


def _is_subset(left: int, right: int) -> bool:
    return left & right == left


def template_subset(left: Template, right: Template) -> bool:
    """Return non-strict inclusion between two templates."""

    if left.uses_atom and not right.uses_atom:
        return False
    return _is_subset(left.core_mask, right.core_mask)


def template_strict_subset(left: Template, right: Template) -> bool:
    return left != right and template_subset(left, right)


def templates_comparable(left: Template, right: Template) -> bool:
    return template_subset(left, right) or template_subset(right, left)


def signature_exact_template(signature: Signature) -> Template | None:
    """Return the exact template represented by a non-partial signature."""

    if signature.atom_state == "partial":
        return None
    return Template(signature.core_mask, signature.atom_state == "full")


def signature_strictly_comparable(signature: Signature, template: Template) -> bool:
    """Test strict comparability without choosing the cardinality of ``H``."""

    source = signature.core_mask
    target = template.core_mask
    if not template.uses_atom:
        template_below = _is_subset(target, source) and (
            target != source or signature.atom_state != "empty"
        )
        signature_below = (
            signature.atom_state == "empty"
            and source != target
            and _is_subset(source, target)
        )
        return template_below or signature_below

    template_below = (
        signature.atom_state == "full"
        and target != source
        and _is_subset(target, source)
    )
    signature_below = _is_subset(source, target) and (
        source != target or signature.atom_state != "full"
    )
    return template_below or signature_below


def all_templates(core_size: int) -> tuple[Template, ...]:
    if core_size < 0:
        raise ValueError("core_size must be nonnegative")
    return tuple(
        Template(mask, uses_atom)
        for uses_atom in (False, True)
        for mask in range(1 << core_size)
    )


def all_signatures(core_size: int) -> tuple[Signature, ...]:
    if core_size < 0:
        raise ValueError("core_size must be nonnegative")
    states: tuple[AtomState, ...] = ("empty", "partial", "full")
    return tuple(
        Signature(mask, state) for state in states for mask in range(1 << core_size)
    )


def published56_candidate() -> Candidate:
    """Translate the frozen Martin--Veldt 56-template construction."""

    layers: list[tuple[Template, ...]] = []
    for group in LAYER_GROUPS:
        layer: list[Template] = []
        for name in group:
            for text in PUBLISHED_TEMPLATES[name]:
                mask = 0
                for character in text:
                    if character.isdigit():
                        label = int(character)
                        if not 1 <= label <= 7:
                            raise ValueError(f"unexpected core label in {text!r}")
                        mask |= 1 << (label - 1)
                layer.append(Template(mask, "H" in text))
        layers.append(tuple(sorted(layer)))
    return Candidate(7, tuple(layers))


def lift_candidate(candidate: Candidate, new_core_size: int) -> Candidate:
    """Move new core coordinates together with the distinguished block.

    This realizes the same set family with a larger actual homogeneous block,
    while keeping the original ``H`` as the distinguished block in the model.
    """

    if new_core_size < candidate.core_size:
        raise ValueError("new_core_size must not shrink the core")
    extra_mask = ((1 << new_core_size) - 1) ^ ((1 << candidate.core_size) - 1)
    return Candidate(
        new_core_size,
        tuple(
            tuple(
                Template(
                    item.core_mask | (extra_mask if item.uses_atom else 0),
                    item.uses_atom,
                )
                for item in layer
            )
            for layer in candidate.layers
        ),
    )


def verify_signature_model(candidate: Candidate) -> dict[str, Any]:
    """Verifier A: symbolic EMPTY/PARTIAL/FULL signature enumeration."""

    templates = set(all_templates(candidate.core_size))
    if len(candidate.layers) != LAYER_COUNT:
        return {"valid": False, "failure": "wrong_layer_count"}

    seen: set[Template] = set()
    for layer_index, layer in enumerate(candidate.layers):
        if len(set(layer)) != len(layer):
            return {"valid": False, "failure": "duplicate_within_layer", "layer": layer_index}
        if any(template not in templates for template in layer):
            return {"valid": False, "failure": "template_out_of_range", "layer": layer_index}
        overlap = seen.intersection(layer)
        if overlap:
            return {
                "valid": False,
                "failure": "layers_not_disjoint",
                "layer": layer_index,
                "witness": asdict(min(overlap)),
            }
        seen.update(layer)

        for left, right in itertools.combinations(layer, 2):
            if templates_comparable(left, right):
                return {
                    "valid": False,
                    "failure": "layer_not_antichain",
                    "layer": layer_index,
                    "witness": [asdict(left), asdict(right)],
                }

        layer_set = set(layer)
        for signature in all_signatures(candidate.core_size):
            exact = signature_exact_template(signature)
            if exact in layer_set:
                continue
            if not any(signature_strictly_comparable(signature, item) for item in layer):
                return {
                    "valid": False,
                    "failure": "layer_not_saturated",
                    "layer": layer_index,
                    "witness": asdict(signature),
                }

        if layer_index > 0:
            previous = candidate.layers[layer_index - 1]
            for upper in layer:
                if not any(template_strict_subset(lower, upper) for lower in previous):
                    return {
                        "valid": False,
                        "failure": "layering_failure",
                        "layer": layer_index,
                        "witness": asdict(upper),
                    }

    return {
        "valid": True,
        "verifier": "signature_model",
        "core_size": candidate.core_size,
        "family_size": candidate.total_size,
        "layer_sizes": [len(layer) for layer in candidate.layers],
        "signatures_checked": LAYER_COUNT * 3 * (1 << candidate.core_size),
    }


def _expand_template(template: Template, core_size: int, atom_size: int) -> frozenset[int]:
    core = {index for index in range(core_size) if template.core_mask >> index & 1}
    if template.uses_atom:
        core.update(range(core_size, core_size + atom_size))
    return frozenset(core)


def _powerset(elements: Sequence[int]) -> Iterable[frozenset[int]]:
    for size in range(len(elements) + 1):
        for choice in itertools.combinations(elements, size):
            yield frozenset(choice)


def verify_expanded_ground(candidate: Candidate, atom_size: int = 3) -> dict[str, Any]:
    """Verifier B: independently expand to sets and exhaust the full powerset."""

    if atom_size < 2:
        raise ValueError("atom_size must allow a genuine partial state")
    if len(candidate.layers) != LAYER_COUNT:
        return {"valid": False, "failure": "wrong_layer_count"}

    ground = tuple(range(candidate.core_size + atom_size))
    expanded_layers = tuple(
        tuple(_expand_template(item, candidate.core_size, atom_size) for item in layer)
        for layer in candidate.layers
    )
    seen: set[frozenset[int]] = set()
    external_checked = 0
    for layer_index, layer in enumerate(expanded_layers):
        if len(set(layer)) != len(layer):
            return {"valid": False, "failure": "duplicate_within_layer", "layer": layer_index}
        overlap = seen.intersection(layer)
        if overlap:
            return {"valid": False, "failure": "layers_not_disjoint", "layer": layer_index}
        seen.update(layer)
        for left, right in itertools.combinations(layer, 2):
            if left <= right or right <= left:
                return {"valid": False, "failure": "layer_not_antichain", "layer": layer_index}

        layer_set = set(layer)
        for outside in _powerset(ground):
            if outside in layer_set:
                continue
            external_checked += 1
            if not any(item < outside or outside < item for item in layer):
                return {
                    "valid": False,
                    "failure": "layer_not_saturated",
                    "layer": layer_index,
                    "witness": sorted(outside),
                }

        if layer_index > 0:
            previous = expanded_layers[layer_index - 1]
            for upper in layer:
                if not any(lower < upper for lower in previous):
                    return {
                        "valid": False,
                        "failure": "layering_failure",
                        "layer": layer_index,
                        "witness": sorted(upper),
                    }

    return {
        "valid": True,
        "verifier": "expanded_ground",
        "atom_size": atom_size,
        "ground_size": len(ground),
        "family_size": candidate.total_size,
        "layer_sizes": [len(layer) for layer in expanded_layers],
        "external_sets_checked": external_checked,
    }


@dataclass
class Encoding:
    solver: z3.Solver
    variables: dict[tuple[int, Template], z3.BoolRef]
    templates: tuple[Template, ...]
    assertion_count: int


@dataclass
class CnfEncoding:
    cnf: CnfFormula
    variables: dict[tuple[int, Template], int]
    templates: tuple[Template, ...]
    primary_variable_count: int
    auxiliary_variable_count: int


@dataclass
class CnfFormula:
    """Minimal deterministic DIMACS container with no SAT-library dependency."""

    clauses: list[list[int]]
    variable_count: int = 0

    def append(self, clause: Sequence[int]) -> None:
        copied = list(clause)
        self.clauses.append(copied)
        self.variable_count = max(
            self.variable_count, max((abs(literal) for literal in copied), default=0)
        )

    def extend(self, clauses: Iterable[Sequence[int]]) -> None:
        for clause in clauses:
            self.append(clause)

    def to_file(self, path: Path) -> None:
        with path.open("w", encoding="ascii", newline="\n") as stream:
            stream.write(f"p cnf {self.variable_count} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(str(literal) for literal in clause))
                stream.write(" 0\n")


def add_sequential_at_most(
    cnf: CnfFormula, literals: Sequence[int], bound: int, next_variable: int
) -> int:
    """Add a self-contained Sinz-style sequential counter.

    The returned integer is the first unused variable identifier.  For a
    satisfying primary assignment, auxiliary variable ``s[i,j]`` can be set to
    whether the first ``i+1`` literals contain at least ``j+1`` true values.
    """

    if bound < 0:
        cnf.append([])
        return next_variable
    if bound == 0:
        cnf.extend([[-literal] for literal in literals])
        return next_variable
    if len(literals) <= bound:
        return next_variable

    prefix_count = len(literals) - 1
    counter: list[list[int]] = []
    for _ in range(prefix_count):
        row = list(range(next_variable, next_variable + bound))
        next_variable += bound
        counter.append(row)

    cnf.append([-literals[0], counter[0][0]])
    for index in range(1, prefix_count):
        cnf.append([-literals[index], counter[index][0]])
        cnf.append([-counter[index - 1][0], counter[index][0]])
        for level in range(1, bound):
            cnf.append(
                [
                    -literals[index],
                    -counter[index - 1][level - 1],
                    counter[index][level],
                ]
            )
            cnf.append([-counter[index - 1][level], counter[index][level]])

    for index in range(1, len(literals)):
        cnf.append([-literals[index], -counter[index - 1][bound - 1]])
    return next_variable


def build_encoding(core_size: int, target_size: int, timeout_ms: int) -> Encoding:
    """Build the exact finite feasibility encoding for the stated search class."""

    if target_size < 0:
        raise ValueError("target_size must be nonnegative")
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    templates = all_templates(core_size)
    variables = {
        (layer, template): z3.Bool(
            f"x_{layer}_{'L' if template.uses_atom else 'S'}_{template.core_mask}"
        )
        for layer in range(LAYER_COUNT)
        for template in templates
    }

    for layer in range(LAYER_COUNT):
        for left, right in itertools.combinations(templates, 2):
            if templates_comparable(left, right):
                solver.add(z3.Or(z3.Not(variables[layer, left]), z3.Not(variables[layer, right])))

        for signature in all_signatures(core_size):
            witnesses: list[z3.BoolRef] = []
            exact = signature_exact_template(signature)
            if exact is not None:
                witnesses.append(variables[layer, exact])
            witnesses.extend(
                variables[layer, template]
                for template in templates
                if signature_strictly_comparable(signature, template)
            )
            solver.add(z3.Or(*witnesses))

    for template in templates:
        solver.add(z3.AtMost(*(variables[layer, template] for layer in range(LAYER_COUNT)), 1))

    for layer in range(1, LAYER_COUNT):
        for upper in templates:
            predecessors = [
                variables[layer - 1, lower]
                for lower in templates
                if template_strict_subset(lower, upper)
            ]
            solver.add(z3.Implies(variables[layer, upper], z3.Or(*predecessors)))

    solver.add(
        z3.PbLe(
            [
                (variables[layer, template], 1)
                for layer in range(LAYER_COUNT)
                for template in templates
            ],
            target_size,
        )
    )
    return Encoding(solver, variables, templates, len(solver.assertions()))


def extract_candidate(encoding: Encoding, core_size: int) -> Candidate:
    model = encoding.solver.model()
    layers = tuple(
        tuple(
            template
            for template in encoding.templates
            if z3.is_true(model.eval(encoding.variables[layer, template], model_completion=True))
        )
        for layer in range(LAYER_COUNT)
    )
    return Candidate(core_size, layers)


def build_cnf_encoding(core_size: int, target_size: int) -> CnfEncoding:
    """Build a deterministic CNF version suitable for external proof checking."""

    if target_size < 0:
        raise ValueError("target_size must be nonnegative")
    cnf = CnfFormula([])
    templates = all_templates(core_size)
    variables: dict[tuple[int, Template], int] = {}
    next_variable = 1
    for layer in range(LAYER_COUNT):
        for template in templates:
            variables[layer, template] = next_variable
            next_variable += 1
    primary_count = next_variable - 1

    for layer in range(LAYER_COUNT):
        for left, right in itertools.combinations(templates, 2):
            if templates_comparable(left, right):
                cnf.append([-variables[layer, left], -variables[layer, right]])

        for signature in all_signatures(core_size):
            witnesses: list[int] = []
            exact = signature_exact_template(signature)
            if exact is not None:
                witnesses.append(variables[layer, exact])
            witnesses.extend(
                variables[layer, template]
                for template in templates
                if signature_strictly_comparable(signature, template)
            )
            cnf.append(witnesses)

    for template in templates:
        for left_layer, right_layer in itertools.combinations(range(LAYER_COUNT), 2):
            cnf.append(
                [-variables[left_layer, template], -variables[right_layer, template]]
            )

    for layer in range(1, LAYER_COUNT):
        for upper in templates:
            predecessors = [
                variables[layer - 1, lower]
                for lower in templates
                if template_strict_subset(lower, upper)
            ]
            cnf.append([-variables[layer, upper], *predecessors])

    primary_literals = [
        variables[layer, template]
        for layer in range(LAYER_COUNT)
        for template in templates
    ]
    next_variable = add_sequential_at_most(
        cnf, primary_literals, target_size, primary_count + 1
    )
    return CnfEncoding(
        cnf=cnf,
        variables=variables,
        templates=templates,
        primary_variable_count=primary_count,
        auxiliary_variable_count=next_variable - primary_count - 1,
    )


def _candidate_from_signed_model(
    encoding: CnfEncoding, core_size: int, model: Sequence[int]
) -> Candidate:
    positive = {literal for literal in model if literal > 0}
    layers = tuple(
        tuple(
            template
            for template in encoding.templates
            if encoding.variables[layer, template] in positive
        )
        for layer in range(LAYER_COUNT)
    )
    return Candidate(core_size, layers)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def certify_one(
    core_size: int,
    target_size: int,
    output_directory: Path,
    solver_path: Path,
    solver_kind: str,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Run a supported external SAT solver and verify any returned model."""

    if solver_kind not in {"kissat", "cadical"}:
        raise ValueError(f"unsupported solver kind: {solver_kind}")

    output_directory.mkdir(parents=True, exist_ok=True)
    stem = f"core-{core_size}-target-{target_size}-selfcontained"
    cnf_path = output_directory / f"{stem}.cnf"
    proof_path = output_directory / f"{stem}-{solver_kind}.drat"
    metadata_path = output_directory / f"{stem}.json"
    encoding = build_cnf_encoding(core_size, target_size)
    encoding.cnf.to_file(cnf_path)

    started = time.perf_counter()
    command = (
        [
            str(solver_path),
            f"--time={timeout_seconds}",
            str(cnf_path),
            str(proof_path),
        ]
        if solver_kind == "kissat"
        else [
            str(solver_path),
            "-t",
            str(timeout_seconds),
            str(cnf_path),
            str(proof_path),
        ]
    )
    completed = subprocess.run(
        command,
        check=False,
        capture_output=True,
        text=True,
    )
    runtime = time.perf_counter() - started
    output = completed.stdout + completed.stderr
    is_sat = completed.returncode == 10 and "s SATISFIABLE" in output
    is_unsat = completed.returncode == 20 and "s UNSATISFIABLE" in output
    if not is_sat and not is_unsat:
        raise RuntimeError(
            f"external solver did not finish SAT/UNSAT for core {core_size}:\n{output[-4000:]}"
        )
    version = subprocess.run(
        [str(solver_path), "--version"], check=False, capture_output=True, text=True
    ).stdout.strip()

    record: dict[str, Any] = {
        "schema": "ai-math-lab.p0054.cnf-certificate.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "epistemic_label": "COMPUTED",
        "core_size": core_size,
        "target_size": target_size,
        "solver_kind": solver_kind,
        "solver": f"external {solver_kind} solver {version}",
        "solver_command": command,
        "solver_binary_sha256": _sha256_file(solver_path),
        "solver_result": "SAT" if is_sat else "UNSAT",
        "runtime_seconds": runtime,
        "primary_variable_count": encoding.primary_variable_count,
        "auxiliary_variable_count": encoding.auxiliary_variable_count,
        "clause_count": len(encoding.cnf.clauses),
        "cnf_path": str(cnf_path),
        "cnf_sha256": _sha256_file(cnf_path),
        "reduction_status": "HUMAN_PROOF_IN_PROOF_MODEL_REDUCTION_MD",
    }
    if is_sat:
        model = [
            int(token)
            for line in output.splitlines()
            if line.startswith("v ")
            for token in line[2:].split()
            if token != "0"
        ]
        if not model:
            raise AssertionError("SAT solver returned no parseable model")
        candidate = _candidate_from_signed_model(encoding, core_size, model)
        first = verify_signature_model(candidate)
        second = verify_expanded_ground(candidate)
        if not first["valid"] or not second["valid"]:
            raise AssertionError({"signature_verifier": first, "expanded_verifier": second})
        semantic = _candidate_semantic(candidate)
        record.update(
            {
                "candidate": semantic,
                "candidate_sha256": _semantic_hash(semantic),
                "signature_verifier": first,
                "expanded_verifier": second,
            }
        )
    else:
        if not proof_path.is_file() or proof_path.stat().st_size == 0:
            raise AssertionError("UNSAT solver returned no clausal proof file")
        record.update(
            {
                "proof_path": str(proof_path),
                "proof_sha256": _sha256_file(proof_path),
                "proof_bytes": proof_path.stat().st_size,
                "external_checker_status": "NOT_RUN",
                "mathematical_status": "NOT_A_THEOREM_UNTIL_REDUCTION_AND_PROOF_ARE_CHECKED",
            }
        )
    metadata_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    return record


def _candidate_semantic(candidate: Candidate) -> dict[str, Any]:
    return {
        "core_size": candidate.core_size,
        "total_size": candidate.total_size,
        "layers": [[asdict(template) for template in layer] for layer in candidate.layers],
    }


def _semantic_hash(value: object) -> str:
    canonical = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()


def run_one(core_size: int, target_size: int, timeout_ms: int) -> dict[str, Any]:
    started = time.perf_counter()
    encoding = build_encoding(core_size, target_size, timeout_ms)
    result = encoding.solver.check()
    elapsed = time.perf_counter() - started
    record: dict[str, Any] = {
        "core_size": core_size,
        "target_size": target_size,
        "timeout_ms": timeout_ms,
        "variable_count": len(encoding.variables),
        "assertion_count": encoding.assertion_count,
        "runtime_seconds": elapsed,
        "solver_result": str(result).upper(),
        "epistemic_label": "COMPUTED",
    }
    if result == z3.sat:
        candidate = extract_candidate(encoding, core_size)
        first = verify_signature_model(candidate)
        second = verify_expanded_ground(candidate)
        if not first["valid"] or not second["valid"]:
            raise AssertionError({"signature_verifier": first, "expanded_verifier": second})
        semantic = _candidate_semantic(candidate)
        record.update(
            {
                "candidate": semantic,
                "candidate_sha256": _semantic_hash(semantic),
                "signature_verifier": first,
                "expanded_verifier": second,
            }
        )
    elif result == z3.unknown:
        record["reason_unknown"] = encoding.solver.reason_unknown()
    else:
        record["proof_status"] = "NO_EXTERNAL_CERTIFICATE_NOT_A_THEOREM"
    return record


def calibrate(core_sizes: Sequence[int], target_size: int, timeout_ms: int) -> dict[str, Any]:
    known = published56_candidate()
    known_a = verify_signature_model(known)
    known_b = verify_expanded_ground(known)
    if not known_a["valid"] or not known_b["valid"]:
        raise AssertionError({"signature_verifier": known_a, "expanded_verifier": known_b})

    semantic = {
        "search_class": {
            "layer_count": LAYER_COUNT,
            "member_templates": "A or A union H over a finite core C",
            "requirements": [
                "each layer is a saturated antichain",
                "layers are pairwise disjoint",
                "every member above layer 0 strictly contains a member of the preceding layer",
            ],
            "forbidden_assumptions": [
                "complement symmetry",
                "fixed layer sizes",
                "one-deletion neighborhood",
            ],
        },
        "target_size": target_size,
        "runs": [run_one(size, target_size, timeout_ms) for size in core_sizes],
        "known_56_control": {
            "candidate_sha256": _semantic_hash(_candidate_semantic(known)),
            "signature_verifier": known_a,
            "expanded_verifier": known_b,
        },
    }
    return {
        "schema": "ai-math-lab.p0054.layered-sat7-calibration.v1",
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "epistemic_label": "COMPUTED",
        "warning": "UNSAT without an external proof certificate is not a mathematical theorem.",
        "semantic": semantic,
        "semantic_sha256": _semantic_hash(semantic),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    run = subparsers.add_parser("calibrate")
    run.add_argument("--core-sizes", nargs="+", type=int, default=[4, 5, 6, 7])
    run.add_argument("--target-size", type=int, default=55)
    run.add_argument("--timeout-seconds", type=float, default=60.0)
    run.add_argument("--output", type=Path, default=RESULT_PATH)
    certify = subparsers.add_parser("certify")
    certify.add_argument("--core-sizes", nargs="+", type=int, default=[4, 5])
    certify.add_argument("--target-size", type=int, default=55)
    certify.add_argument("--output-directory", type=Path, default=CERTIFICATE_DIRECTORY)
    certify.add_argument("--solver", type=Path, required=True)
    certify.add_argument(
        "--solver-kind", choices=("kissat", "cadical"), default="kissat"
    )
    certify.add_argument("--timeout-seconds", type=int, default=600)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    if args.command == "calibrate":
        if args.timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be positive")
        report: object = calibrate(
            core_sizes=args.core_sizes,
            target_size=args.target_size,
            timeout_ms=max(1, round(args.timeout_seconds * 1000)),
        )
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
    elif args.command == "certify":
        report = [
            certify_one(
                size,
                args.target_size,
                args.output_directory,
                args.solver,
                args.solver_kind,
                args.timeout_seconds,
            )
            for size in args.core_sizes
        ]
    else:
        raise AssertionError("unreachable")
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
