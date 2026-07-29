#!/usr/bin/env python3
"""Exact incidence-pattern diagnostics for P0054 G4.6.

The mathematical proof is arbitrary-finite and does not depend on this
program. The search reuses the independently validated G4.3 incidence engine
with the symmetric member-size thresholds three and three.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import platform
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

REPOSITORY_ROOT = Path(__file__).resolve().parents[4]
ENGINE_PATH = (
    REPOSITORY_ROOT
    / "Problems/P0054/experiments/g4.3-stronger-lower/search.py"
)


@dataclass(frozen=True)
class Case33:
    """One orientation of a symmetric (3,3) mutual-blocker split."""

    a: int
    b: int
    orientation: str = "S"

    @property
    def rows(self) -> int:
        return self.a

    @property
    def blocker_count(self) -> int:
        return self.b

    @property
    def row_min(self) -> int:
        return 3

    @property
    def row_max(self) -> int:
        return self.b

    @property
    def blocker_min(self) -> int:
        return 3


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_engine() -> Any:
    spec = importlib.util.spec_from_file_location("p0054_g43_search", ENGINE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the frozen G4.3 search engine")
    engine: Any = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = engine
    spec.loader.exec_module(engine)
    return engine


def witness_validator(
    engine: Any, multiplicities: tuple[int, ...], case: Case33
) -> dict[str, object]:
    primary, patterns = engine.explicit_family(multiplicities, case.rows)
    blocker_a = engine.blocker_powerset(primary, len(patterns))
    blocker_b = engine.blocker_choice_minimization(primary)
    dual_a = engine.blocker_powerset(blocker_a, len(patterns))
    dual_b = engine.blocker_choice_minimization(blocker_b)
    normalize = engine.normalize_family
    return {
        "ground_size": len(patterns),
        "primary": [list(edge) for edge in normalize(primary)],
        "blocker": [list(edge) for edge in normalize(blocker_a)],
        "validators_agree": (
            normalize(blocker_a) == normalize(blocker_b)
            and normalize(dual_a) == normalize(dual_b)
        ),
        "size_constraints": {
            "primary_min_at_least_3": min(map(len, primary)) >= 3,
            "blocker_min_at_least_3": min(map(len, blocker_a)) >= 3,
            "powerset_dual_equals_primary": normalize(dual_a)
            == normalize(primary),
            "choice_dual_equals_primary": normalize(dual_b)
            == normalize(primary),
        },
    }


def clean_record(record: dict[str, object]) -> dict[str, object]:
    result = dict(record)
    result.pop("elapsed_seconds", None)
    return result


def main() -> None:
    engine = load_engine()

    def validate(
        multiplicities: tuple[int, ...], case: Case33
    ) -> dict[str, object]:
        return witness_validator(engine, multiplicities, case)

    engine.validate_witness = validate
    cases = (Case33(5, 5), Case33(5, 6))
    records: list[dict[str, object]] = []
    for case in cases:
        record = cast(dict[str, object], engine.search_case(case))
        records.append(clean_record(record))

    document = {
        "schema_version": 1,
        "epistemic_label": "COMPUTED",
        "python_version": platform.python_version(),
        "random_seed": "NONE_DETERMINISTIC_EXHAUSTIVE_ENUMERATION",
        "source_engine": str(ENGINE_PATH.relative_to(REPOSITORY_ROOT)),
        "source_engine_sha256": sha256_file(ENGINE_PATH),
        "semantic_validation": engine.cross_validate_semantics(),
        "cases": records,
        "scope": (
            "all incidence multiplicities after the proved private-witness "
            "member-size cap, modulo row permutations"
        ),
        "theorem_not_inferred": True,
    }
    print(json.dumps(document, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
