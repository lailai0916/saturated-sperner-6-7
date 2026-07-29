#!/usr/bin/env python3

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "AiMathLab" / "P0054MiddleSevenNineK4WitnessData.lean"

BASES = (
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3, 6)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4, 6), (0, 1, 3)),
    ((3, 4, 5), (2, 3, 6), (1, 4, 6), (1, 2, 5, 6),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
    ((3, 4, 5, 6), (2, 3, 6), (1, 4, 6), (1, 2, 5),
     (0, 5, 6), (0, 2, 4), (0, 1, 3)),
)

KERNEL_ROWS = ((0, 1, 3), (0, 2, 4), (1, 2, 5), (3, 4, 5))


@dataclass(frozen=True, order=True)
class TupleKey:
    base_index: int
    old_first: int
    old_second: int
    private_first: int
    private_second: int
    shared: int


def mask(row: tuple[int, ...]) -> int:
    return sum(1 << point for point in row)


def popcount(value: int) -> int:
    return bin(value).count("1")


def powerset_masks(width: int) -> list[int]:
    values = [0]
    for point in reversed(range(width)):
        values += [value | (1 << point) for value in values]
    return values


def old_pairs(base: tuple[tuple[int, ...], ...]) -> list[tuple[int, int]]:
    subsets = powerset_masks(7)
    base_degrees = [sum(point in row for row in base) for point in range(7)]
    return [
        (first, second)
        for first in subsets
        for second in subsets
        if all(
            base_degrees[point]
            + bool(first & (1 << point))
            + bool(second & (1 << point))
            <= 4
            for point in range(7)
        )
    ]


def old_pair_kernel_hit(first: int, second: int) -> bool:
    return all(mask(row) & first and mask(row) & second for row in KERNEL_ROWS)


def fresh_block(start: int, count: int) -> int:
    return ((1 << count) - 1) << start


def first_extra(old: int, private: int, shared: int) -> int:
    return old | fresh_block(7, private) | fresh_block(21, shared)


def second_extra(old: int, private: int, shared: int) -> int:
    return old | fresh_block(14, private) | fresh_block(21, shared)


def subset(left: int, right: int) -> bool:
    return left & ~right == 0


def clutter(rows: tuple[int, ...]) -> bool:
    return all(
        left == right or not subset(left, right)
        for left in rows
        for right in rows
    )


def candidate_structure(
    base: tuple[int, ...],
    old_first: int,
    old_second: int,
    private_first: int,
    private_second: int,
    shared: int,
) -> bool:
    first = first_extra(old_first, private_first, shared)
    second = second_extra(old_second, private_second, shared)
    rows = (second, first, *base)
    return (
        old_first * 8 + private_first <= old_second * 8 + private_second
        and 3 <= popcount(first) <= 7
        and 3 <= popcount(second) <= 7
        and len(set(rows)) == 9
        and clutter(rows)
    )


def minimize(rows: set[int]) -> set[int]:
    ordered = sorted(rows, key=lambda row: (popcount(row), row))
    result: list[int] = []
    for row in ordered:
        if not any(subset(other, row) for other in result):
            result.append(row)
    return set(result)


def blocker(rows: tuple[int, ...]) -> set[int]:
    candidates = {0}
    for row in reversed(rows):
        expanded: set[int] = set()
        for candidate in candidates:
            if candidate & row:
                expanded.add(candidate)
            else:
                point_bits = row
                while point_bits:
                    point = point_bits & -point_bits
                    expanded.add(candidate | point)
                    point_bits -= point
        candidates = minimize(expanded)
    return candidates


def private_blocker_certificate(rows: tuple[int, ...], witness: int) -> bool:
    return (
        all(witness & row for row in rows)
        and all(
            any(witness & row == point for row in rows)
            for point in (1 << index for index in range(28))
            if witness & point
        )
    )


def hard_tuples() -> dict[tuple[int, int, int], list[tuple[TupleKey, tuple[int, ...]]]]:
    grouped: dict[
        tuple[int, int, int], list[tuple[TupleKey, tuple[int, ...]]]
    ] = defaultdict(list)
    for base_index, base_rows in enumerate(BASES):
        base = tuple(map(mask, base_rows))
        for old_first, old_second in old_pairs(base_rows):
            if not old_pair_kernel_hit(old_first, old_second):
                continue
            for private_first in range(8):
                for shared in range(8):
                    for private_second in range(8):
                        if not candidate_structure(
                            base,
                            old_first,
                            old_second,
                            private_first,
                            private_second,
                            shared,
                        ):
                            continue
                        key = TupleKey(
                            base_index,
                            old_first,
                            old_second,
                            private_first,
                            private_second,
                            shared,
                        )
                        rows = (
                            second_extra(old_second, private_second, shared),
                            first_extra(old_first, private_first, shared),
                            *base,
                        )
                        grouped[(base_index, old_first, old_second)].append((key, rows))
    return grouped


def choose_witnesses(
    grouped: dict[tuple[int, int, int], list[tuple[TupleKey, tuple[int, ...]]]],
) -> tuple[
    list[tuple[int, int, int, list[int]]],
    list[tuple[TupleKey, int]],
]:
    universal: list[tuple[int, int, int, list[int]]] = []
    exceptions: list[tuple[TupleKey, int]] = []
    for pair_key in sorted(grouped):
        tuples = grouped[pair_key]
        tuple_blockers = [(key, rows, blocker(rows)) for key, rows in tuples]
        common = set.intersection(*(values for _key, _rows, values in tuple_blockers))
        common_codes = sorted(common, key=lambda row: (popcount(row), row))[:8]
        universal.append((*pair_key, common_codes))
        if len(common_codes) == 8:
            continue
        if len(common_codes) != 7:
            raise ValueError(
                f"pair {pair_key} has {len(common)} common blocker rows, expected 7 or at least 8"
            )
        common_set = set(common_codes)
        for key, rows, values in tuple_blockers:
            extra = min(
                values - common_set,
                key=lambda row: (popcount(row), row),
            )
            exceptions.append((key, extra))
            witnesses = (*common_codes, extra)
            if len(set(witnesses)) != 8:
                raise ValueError(f"duplicate witnesses for {key}")
            if not all(private_blocker_certificate(rows, witness) for witness in witnesses):
                raise ValueError(f"invalid private-blocker witness for {key}")
    return universal, exceptions


def validate_lookup_coverage(
    grouped: dict[tuple[int, int, int], list[tuple[TupleKey, tuple[int, ...]]]],
    universal: list[tuple[int, int, int, list[int]]],
    exceptions: list[tuple[TupleKey, int]],
) -> None:
    common_by_pair = {
        (base_index, old_first, old_second): codes
        for base_index, old_first, old_second, codes in universal
    }
    extra_by_tuple = dict(exceptions)
    if len(common_by_pair) != len(universal):
        raise ValueError("duplicate universal witness key")
    if len(extra_by_tuple) != len(exceptions):
        raise ValueError("duplicate exceptional witness key")

    for pair_key, tuples in grouped.items():
        common = common_by_pair[pair_key]
        for key, rows in tuples:
            witnesses = list(common)
            if key in extra_by_tuple:
                witnesses.append(extra_by_tuple[key])
            if len(witnesses) != 8 or len(set(witnesses)) != 8:
                raise ValueError(f"lookup does not return eight distinct rows for {key}")
            if not all(
                private_blocker_certificate(rows, witness)
                for witness in witnesses
            ):
                raise ValueError(f"lookup returns an invalid certificate for {key}")


def lean_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def render_universal(values: list[tuple[int, int, int, list[int]]]) -> str:
    return "\n".join(
        "  { baseIndex := "
        f"{base_index}, oldFirstCode := {old_first}, "
        f"oldSecondCode := {old_second}, codes := {lean_nat_list(codes)} }}"
        + ("," if index + 1 < len(values) else "")
        for index, (base_index, old_first, old_second, codes) in enumerate(values)
    )


def render_exceptions(values: list[tuple[TupleKey, int]]) -> str:
    return "\n".join(
        "  { baseIndex := "
        f"{key.base_index}, oldFirstCode := {key.old_first}, "
        f"oldSecondCode := {key.old_second}, privateFirst := {key.private_first}, "
        f"privateSecond := {key.private_second}, shared := {key.shared}, "
        f"code := {code} }}"
        + ("," if index + 1 < len(values) else "")
        for index, (key, code) in enumerate(values)
    )


def render_universal_cases(
    values: list[tuple[int, int, int, list[int]]],
) -> str:
    return "\n".join(
        f"  | {base_index}, {old_first}, {old_second} => {lean_nat_list(codes)}"
        for base_index, old_first, old_second, codes in values
    )


def render_exception_cases(values: list[tuple[TupleKey, int]]) -> str:
    return "\n".join(
        "  | "
        f"{key.base_index}, {key.old_first}, {key.old_second}, "
        f"{key.private_first}, {key.private_second}, {key.shared} => some {code}"
        for key, code in values
    )


def render(
    universal: list[tuple[int, int, int, list[int]]],
    exceptions: list[tuple[TupleKey, int]],
) -> str:
    return f"""import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

/-!
# Generated blocker-witness data for the seven-plus-nine K4 certificate

The table contains untrusted row-mask candidates.  Its consumers must check
each decoded row with `supportPrivateBlockerCertificate`; no theorem depends
on the Python generator's blocker computation.
-/

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

abbrev SevenNineK4WitnessPoint := Fin 28

def sevenNineK4UniversalWitnessCodes
    (baseIndex oldFirstCode oldSecondCode : Nat) : List Nat :=
  match baseIndex, oldFirstCode, oldSecondCode with
{render_universal_cases(universal)}
  | _, _, _ => []

def sevenNineK4ExceptionalWitnessCode?
    (baseIndex oldFirstCode oldSecondCode privateFirst privateSecond shared : Nat) :
    Option Nat :=
  match baseIndex, oldFirstCode, oldSecondCode,
      privateFirst, privateSecond, shared with
{render_exception_cases(exceptions)}
  | _, _, _, _, _, _ => none

def sevenNineK4WitnessCodes
    (baseIndex oldFirstCode oldSecondCode privateFirst privateSecond shared : Nat) :
    List Nat :=
  let common := sevenNineK4UniversalWitnessCodes
    baseIndex oldFirstCode oldSecondCode
  if common.length = 8 then
    common
  else
    match sevenNineK4ExceptionalWitnessCode?
        baseIndex oldFirstCode oldSecondCode privateFirst privateSecond shared with
    | some code => common ++ [code]
    | none => common

def sevenNineK4DecodeWitnessRow (code : Nat) :
    Finset SevenNineK4WitnessPoint :=
  Finset.univ.filter fun point => Nat.testBit code point.val = true

def sevenNineK4WitnessRows
    (baseIndex oldFirstCode oldSecondCode privateFirst privateSecond shared : Nat) :
    List (Finset SevenNineK4WitnessPoint) :=
  (sevenNineK4WitnessCodes baseIndex oldFirstCode oldSecondCode
    privateFirst privateSecond shared).map sevenNineK4DecodeWitnessRow

end AiMathLab.P0054.MiddleSevenNineK4Finite
"""


def main() -> None:
    grouped = hard_tuples()
    universal, exceptions = choose_witnesses(grouped)
    validate_lookup_coverage(grouped, universal, exceptions)
    hard_count = sum(len(values) for values in grouped.values())
    universal_mask_count = sum(len(codes) for *_key, codes in universal)
    total_mask_count = universal_mask_count + len(exceptions)

    if hard_count != 7440:
        raise ValueError(f"unexpected hard-tuple count {hard_count}, expected 7440")
    if len(grouped) != 120:
        raise ValueError(f"unexpected hard-pair count {len(grouped)}, expected 120")
    if len(exceptions) != 960:
        raise ValueError(
            f"unexpected exceptional-tuple count {len(exceptions)}, expected 960"
        )
    exceptional_pairs = {
        (entry.base_index, entry.old_first, entry.old_second)
        for entry, _code in exceptions
    }
    expected_exceptional_pairs = {
        (base_index, old_first, old_second)
        for base_index in range(1, 5)
        for old_first, old_second in ((12, 18), (12, 33), (18, 33))
    }
    if exceptional_pairs != expected_exceptional_pairs:
        raise ValueError(
            f"unexpected exceptional old pairs {sorted(exceptional_pairs)}"
        )
    if total_mask_count != 1908:
        raise ValueError(f"unexpected stored-mask count {total_mask_count}, expected 1908")

    content = render(universal, exceptions)
    if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != content:
        OUTPUT.write_text(content, encoding="utf-8")

    print(f"hard tuples: {hard_count}")
    print(f"hard old pairs: {len(grouped)}")
    print(f"universal masks: {universal_mask_count}")
    print(f"exception masks: {len(exceptions)}")
    print(f"stored masks: {total_mask_count}")
    print(f"output: {OUTPUT}")


if __name__ == "__main__":
    main()
