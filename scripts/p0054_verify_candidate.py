"""Independently verify the explicit P0054 size-55 construction.

The SAT solver is used only to discover the family.  This verifier reads the
saved mathematical witness, reconstructs it without solving any CNF, and runs
four exact checks: the P0054 signature and expanded-ground layer checks plus
the two older P0053 saturated-Sperner verifiers.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from scripts.p0053_sat7 import dual_verify, family_sha256
from scripts.p0054_layered_sat7 import (
    Candidate,
    Template,
    _candidate_semantic,
    _semantic_hash,
    verify_expanded_ground,
    verify_signature_model,
)

DEFAULT_INPUT = Path(
    "Problems/P0054/experiments/certificates/"
    "core-8-target-55-selfcontained.json"
)
DEFAULT_OUTPUT = Path(
    "Problems/P0054/experiments/core-8-size-55-dual-verification.json"
)


def candidate_from_record(record: dict[str, Any]) -> Candidate:
    """Decode and hash-check the solver-independent candidate payload."""

    semantic = record["candidate"]
    candidate = Candidate(
        core_size=int(semantic["core_size"]),
        layers=tuple(
            tuple(
                Template(int(item["core_mask"]), bool(item["uses_atom"]))
                for item in layer
            )
            for layer in semantic["layers"]
        ),
    )
    reconstructed = _candidate_semantic(candidate)
    if reconstructed != semantic:
        raise AssertionError("candidate payload is not canonical")
    if _semantic_hash(reconstructed) != record["candidate_sha256"]:
        raise AssertionError("candidate semantic hash mismatch")
    return candidate


def expanded_family(candidate: Candidate, atom_size: int = 3) -> tuple[int, ...]:
    """Expand templates to bit masks on ``core union H``."""

    if atom_size < 1:
        raise ValueError("atom_size must be positive")
    atom_mask = ((1 << atom_size) - 1) << candidate.core_size
    return tuple(
        template.core_mask | (atom_mask if template.uses_atom else 0)
        for layer in candidate.layers
        for template in layer
    )


def _without_runtime(result: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in result.items() if key != "runtime_seconds"}


def verify_maximal_small_free_certificate(candidate: Candidate) -> dict[str, Any]:
    """Check the human-readable maximal-small-free proof certificate."""

    full_mask = (1 << candidate.core_size) - 1
    layer_records: list[dict[str, Any]] = []
    for layer_index, layer in enumerate(candidate.layers):
        small = sorted(item.core_mask for item in layer if not item.uses_atom)
        displayed_large = sorted(item.core_mask for item in layer if item.uses_atom)
        free_masks = [
            mask
            for mask in range(full_mask + 1)
            if not any((member & mask) == member for member in small)
        ]
        maximal_free = sorted(
            mask
            for mask in free_masks
            if not any(
                mask != extension and (mask & extension) == mask
                for extension in free_masks
            )
        )
        if displayed_large != maximal_free:
            raise AssertionError(
                {
                    "layer": layer_index,
                    "displayed_large": displayed_large,
                    "maximal_small_free": maximal_free,
                }
            )
        layer_records.append(
            {
                "layer": layer_index,
                "small_count": len(small),
                "large_count": len(displayed_large),
                "small_free_core_masks": len(free_masks),
                "maximal_small_free_core_masks": maximal_free,
            }
        )

    return {
        "valid": True,
        "core_masks_checked_per_layer": 1 << candidate.core_size,
        "layers": layer_records,
    }


def verify_saved_candidate(path: Path) -> dict[str, Any]:
    """Return a stable, solver-independent verification record."""

    source = json.loads(path.read_text(encoding="utf-8"))
    candidate = candidate_from_record(source)
    family = expanded_family(candidate)
    n = candidate.core_size + 3

    signature = verify_signature_model(candidate)
    expanded = verify_expanded_ground(candidate)
    verify_maximal_small_free_certificate(candidate)
    dual = dual_verify(n, 7, family)
    if candidate.total_size != 55 or len(set(family)) != 55:
        raise AssertionError("candidate does not contain exactly 55 distinct sets")
    if not signature["valid"] or not expanded["valid"]:
        raise AssertionError({"signature": signature, "expanded": expanded})
    if not dual["validator_a"]["valid"] or not dual["validator_b"]["valid"]:
        raise AssertionError(dual)

    return {
        "schema": "ai-math-lab.p0054.explicit-construction-verification.v1",
        "epistemic_label": "COMPUTED",
        "mathematical_consequence": "EXPLICIT_WITNESS_PROVES_sat7_LE_55",
        "source_candidate_path": str(path),
        "source_candidate_sha256": source["candidate_sha256"],
        "core_size": candidate.core_size,
        "atom_size": 3,
        "ground_size": n,
        "k": 7,
        "family_size": len(family),
        "layer_sizes": [len(layer) for layer in candidate.layers],
        "family_sha256": family_sha256(n, 7, family),
        "canonical_family_masks": sorted(
            family, key=lambda member: (member.bit_count(), member)
        ),
        "signature_verifier": signature,
        "expanded_layer_verifier": expanded,
        "independent_saturated_sperner_verifiers": {
            "agreement": dual["agreement"],
            "validator_a": _without_runtime(dual["validator_a"]),
            "validator_b": _without_runtime(dual["validator_b"]),
        },
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    report = verify_saved_candidate(args.input)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
