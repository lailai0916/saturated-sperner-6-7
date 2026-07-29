#!/usr/bin/env python3
"""Generate the split Lean certificate for the G4.17 six-row support multigraph."""

from __future__ import annotations

import itertools
import math
from pathlib import Path

VERTICES = 6
SUPPORTS = tuple((v,) for v in range(VERTICES)) + tuple(
    itertools.combinations(range(VERTICES), 2)
)
SUPPORT_MASKS = tuple(sum(1 << v for v in support) for support in SUPPORTS)
FULL_MASK = (1 << VERTICES) - 1

SUPPORT_ORDERS = {
    4: (9, 10, 13, 14, 16, 17, 18, 19, 6, 7, 8, 11, 12, 15, 0, 1, 2, 3),
    5: (10, 14, 17, 19, 20, 6, 7, 8, 9, 11, 12, 13, 15, 16, 18, 0, 1, 2, 3, 4),
    6: (0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 15, 16, 17, 2, 18, 19, 3, 20, 4, 5),
}

PREFIX_DEPTHS = {4: 2, 5: 4, 6: 7}


def minimal_support_covers() -> tuple[tuple[int, ...], ...]:
    covers: list[tuple[int, ...]] = []
    for size in range(1, VERTICES + 1):
        for cover in itertools.combinations(range(len(SUPPORTS)), size):
            union = 0
            for index in cover:
                union |= SUPPORT_MASKS[index]
            if union != FULL_MASK:
                continue
            if all(
                any(
                    SUPPORT_MASKS[index] & (1 << vertex)
                    and all(
                        other == index
                        or not SUPPORT_MASKS[other] & (1 << vertex)
                        for other in cover
                    )
                    for vertex in range(VERTICES)
                )
                for index in cover
            ):
                covers.append(cover)
    return tuple(covers)


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def lean_wrapped_list(values: tuple[str, ...], width: int = 12) -> str:
    rows = [", ".join(values[start : start + width]) for start in range(0, len(values), width)]
    return "[\n" + ",\n".join(f"    {row}" for row in rows) + "\n  ]"


def generate_finite(covers: tuple[tuple[int, ...], ...]) -> str:
    support_cases = []
    for index, support in enumerate(SUPPORTS):
        support_cases.append(f"  | ⟨{index}, _⟩ => " + "{" + ", ".join(map(str, support)) + "}")
    support_cases.append("  | ⟨n + 21, h⟩ => by omega")
    cover_lines = ",\n".join(f"    {lean_list(cover)}" for cover in covers)
    mask_cases = "\n".join(
        f"  | {index} => {mask}" for index, mask in enumerate(SUPPORT_MASKS)
    )
    return f"""import Mathlib

namespace AiMathLab.P0054.G417

open scoped BigOperators

abbrev SixVertex := Fin 6
abbrev SixSupportIndex := Fin 21
abbrev SixMultiplicity := Array Nat
abbrev SixDegreeState := Array Nat

def sixMultiplicityDigit (m : SixMultiplicity) (s : Nat) : Nat :=
  m.getD s 0

def sixSupport : SixSupportIndex → Finset SixVertex
{chr(10).join(support_cases)}

def sixSupportCovers (C : Finset SixSupportIndex) : Prop :=
  ∀ v : SixVertex, ∃ s ∈ C, v ∈ sixSupport s

def sixMinimalSupportCover (C : Finset SixSupportIndex) : Prop :=
  sixSupportCovers C ∧ ∀ s ∈ C, ¬sixSupportCovers (C.erase s)

instance (C : Finset SixSupportIndex) : Decidable (sixSupportCovers C) := by
  unfold sixSupportCovers
  infer_instance

instance (C : Finset SixSupportIndex) : Decidable (sixMinimalSupportCover C) := by
  unfold sixMinimalSupportCover
  infer_instance

def sixMinimalSupportCovers : List (List SixSupportIndex) :=
  [
{cover_lines}
  ]

def sixWeightedCoverCount (m : SixMultiplicity) : Nat :=
  (sixMinimalSupportCovers.map fun C ↦
    (C.map fun s ↦ sixMultiplicityDigit m s).prod).sum

def sixSupportDegree (m : SixMultiplicity) (v : SixVertex) : Nat :=
  ∑ s : SixSupportIndex,
    if v ∈ sixSupport s then sixMultiplicityDigit m s.val else 0

def sixSupportTouchesLow (lowCount : Nat) (s : SixSupportIndex) : Prop :=
  ∃ v ∈ sixSupport s, v.val < lowCount

instance (lowCount : Nat) (s : SixSupportIndex) :
    Decidable (sixSupportTouchesLow lowCount s) := by
  unfold sixSupportTouchesLow
  infer_instance

def SixMultiplicityValid (lowCount : Nat) (m : SixMultiplicity) : Prop :=
  (∀ v : SixVertex, if v.val < lowCount then sixSupportDegree m v = 3
    else 4 ≤ sixSupportDegree m v) ∧
  ∀ s : SixSupportIndex, 0 < sixMultiplicityDigit m s.val →
    sixSupportTouchesLow lowCount s

instance (lowCount : Nat) (m : SixMultiplicity) :
    Decidable (SixMultiplicityValid lowCount m) := by
  unfold SixMultiplicityValid
  infer_instance

def sixMultiplicityZero : SixMultiplicity := Array.replicate 21 0
def sixDegreeStateZero : SixDegreeState := Array.replicate 6 0

def sixSupportMask : Nat → Nat
{mask_cases}
  | _ => 0

def sixSupportContains (s v : Nat) : Bool :=
  (sixSupportMask s).testBit v

def sixSupportTouchesLowBool (lowCount s : Nat) : Bool :=
  (List.range lowCount).any fun v ↦ sixSupportContains s v

def addSixSupportDegree
    (degrees : SixDegreeState) (s k : Nat) : SixDegreeState :=
  Array.ofFn fun v : SixVertex ↦
    degrees.getD v.val 0 + if sixSupportContains s v.val then k else 0

def sixDegreeStateValidBool (lowCount : Nat) (degrees : SixDegreeState) : Bool :=
  (List.range 6).all fun v ↦
    if v < lowCount then decide (degrees.getD v 0 = 3)
    else decide (4 ≤ degrees.getD v 0)

def sixMultiplicityChoices
    (lowCount : Nat) (degrees : SixDegreeState) (s : Nat) : List Nat :=
  (List.range 4).filter fun k ↦
    (decide (k = 0) || sixSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !sixSupportContains s v || decide (degrees.getD v 0 + k ≤ 3)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed 562-entry support-cover certificate is checked by kernel reduction.
theorem six_minimal_support_covers_length : sixMinimalSupportCovers.length = 562 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed 562-entry support-cover certificate is checked by kernel reduction.
theorem six_minimal_support_covers_sound_check :
    sixMinimalSupportCovers.all (fun C ↦ decide (sixMinimalSupportCover C.toFinset)) =
      true := by
  decide

theorem six_minimal_support_covers_sound {{C : List SixSupportIndex}}
    (hC : C ∈ sixMinimalSupportCovers) : sixMinimalSupportCover C.toFinset := by
  have hCheck := six_minimal_support_covers_sound_check
  simp only [List.all_eq_true, decide_eq_true_eq] at hCheck
  exact hCheck C hC

def sixSupportMultigraphCheckAux
    (lowCount minimum : Nat) : List Nat → SixMultiplicity → SixDegreeState → Bool
  | [], m, degrees =>
      if sixDegreeStateValidBool lowCount degrees then
        decide (minimum ≤ sixWeightedCoverCount m)
      else true
  | s :: supports, m, degrees =>
      (sixMultiplicityChoices lowCount degrees s).all fun k ↦
        sixSupportMultigraphCheckAux lowCount minimum supports (m.set! s k)
          (addSixSupportDegree degrees s k)

def sixMultiplicityAfterFour (a b c d : Nat) : SixMultiplicity :=
  (((sixMultiplicityZero.set! 0 a).set! 1 b).set! 2 c).set! 3 d

def sixDegreeStateAfterFour (a b c d : Nat) : SixDegreeState :=
  #[(a : Nat), b, c, d, 0, 0]

def sixSupportMultigraphSubcheck (lowCount a b c d : Nat) : Bool :=
  sixSupportMultigraphCheckAux lowCount 15 ((List.range 21).drop 4)
    (sixMultiplicityAfterFour a b c d) (sixDegreeStateAfterFour a b c d)

end AiMathLab.P0054.G417
"""


def completion_groups(
    covers: tuple[tuple[int, ...], ...], order: tuple[int, ...]
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    positions = {support: position for position, support in enumerate(order)}
    groups: list[list[tuple[int, ...]]] = [[] for _ in order]
    for cover in covers:
        if not all(support in positions for support in cover):
            continue
        groups[max(positions[support] for support in cover)].append(cover)
    return tuple(tuple(group) for group in groups)


def completion_stages(
    covers: tuple[tuple[int, ...], ...], order: tuple[int, ...]
) -> tuple[int | None, ...]:
    positions = {support: position for position, support in enumerate(order)}
    return tuple(
        max(positions[support] for support in cover)
        if all(support in positions for support in cover)
        else None
        for cover in covers
    )


SearchState = tuple[tuple[int, ...], tuple[int, ...], int]


def advance_search_state(
    low_count: int,
    order: tuple[int, ...],
    groups: tuple[tuple[tuple[int, ...], ...], ...],
    position: int,
    state: SearchState,
    value: int,
) -> tuple[SearchState | None, str]:
    multiplicities, degrees, count = state
    support = order[position]
    if value and not any(vertex < low_count for vertex in SUPPORTS[support]):
        return None, "choice"
    if any(
        degrees[vertex] + value > 3
        for vertex in SUPPORTS[support]
        if vertex < low_count
    ):
        return None, "choice"

    next_multiplicities = list(multiplicities)
    next_multiplicities[support] = value
    next_degrees = list(degrees)
    for vertex in SUPPORTS[support]:
        next_degrees[vertex] += value
    next_count = count + sum(
        math.prod(next_multiplicities[index] for index in cover)
        for cover in groups[position]
    )
    if next_count >= 15:
        return None, "count"

    remaining = order[position + 1 :]
    completion_possible = all(
        (3 if vertex < low_count else 4)
        <= next_degrees[vertex]
        + 3 * sum(vertex in SUPPORTS[index] for index in remaining)
        for vertex in range(VERTICES)
    )
    if not completion_possible:
        return None, "completion"
    return (tuple(next_multiplicities), tuple(next_degrees), next_count), "active"


def active_prefixes(
    covers: tuple[tuple[int, ...], ...], low_count: int, depth: int
) -> tuple[tuple[int, ...], ...]:
    order = SUPPORT_ORDERS[low_count]
    groups = completion_groups(covers, order)
    initial_state: SearchState = ((0,) * len(SUPPORTS), (0,) * VERTICES, 0)
    states: list[tuple[SearchState, tuple[int, ...]]] = [(initial_state, ())]
    for position in range(depth):
        next_states: list[tuple[SearchState, tuple[int, ...]]] = []
        for state, prefix in states:
            for value in range(4):
                next_state, reason = advance_search_state(
                    low_count, order, groups, position, state, value
                )
                if reason == "active" and next_state is not None:
                    next_states.append((next_state, prefix + (value,)))
        states = next_states
    return tuple(prefix for _, prefix in states)


def cover_code(cover: tuple[int, ...]) -> int:
    return sum((support + 1) << (5 * position) for position, support in enumerate(cover))


def lean_encoded_groups(groups: tuple[tuple[tuple[int, ...], ...], ...]) -> str:
    lines = []
    for group in groups:
        lines.append("    [" + ", ".join(str(cover_code(cover)) for cover in group) + "]")
    return "[\n" + ",\n".join(lines) + "\n  ]"


def generate_early(covers: tuple[tuple[int, ...], ...]) -> str:
    data = []
    for low_count, order in SUPPORT_ORDERS.items():
        groups = completion_groups(covers, order)
        stages = completion_stages(covers, order)
        lean_stages = lean_wrapped_list(
            tuple("none" if stage is None else f"some {stage}" for stage in stages)
        )
        data.append(
            f"def sixSupportOrder{low_count} : List Nat := {lean_list(order)}\n\n"
            f"def sixCompletionGroups{low_count} : List (List Nat) :=\n"
            f"  {lean_encoded_groups(groups)}\n\n"
            f"def sixCompletionStages{low_count} : List (Option Nat) :=\n"
            f"  {lean_stages}"
        )
    encoded_covers = lean_wrapped_list(tuple(str(cover_code(cover)) for cover in covers))
    multiplicity_weights = "\n".join(
        f"  | {support} => {4**support}" for support in range(len(SUPPORTS))
    )
    degree_updates = []
    for support, vertices in enumerate(SUPPORTS):
        updates = ", ".join(
            f"d{vertex} := degrees.d{vertex} + k" for vertex in vertices
        )
        degree_updates.append(f"  | {support} => {{ degrees with {updates} }}")
    degree_update_cases = "\n".join(degree_updates)
    return f"""import AiMathLab.P0054G417.SixSupportMultigraphFinite

namespace AiMathLab.P0054.G417

set_option linter.style.longLine false
def sixEncodedMinimalSupportCovers : List Nat :=
  {encoded_covers}

{chr(10).join(data)}

def sixCompactMultiplicityWeight : Nat → Nat
{multiplicity_weights}
  | _ => 0

def sixCompactMultiplicityDigit (m s : Nat) : Nat :=
  Nat.land (Nat.shiftRight m (2 * s)) 3

def sixCompactSetMultiplicity (m s k : Nat) : Nat :=
  m + k * sixCompactMultiplicityWeight s

structure SixCompactDegrees where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  d4 : Nat
  d5 : Nat
  deriving DecidableEq

def sixCompactDegreesZero : SixCompactDegrees := ⟨0, 0, 0, 0, 0, 0⟩

def sixCompactDegree (degrees : SixCompactDegrees) : Nat → Nat
  | 0 => degrees.d0
  | 1 => degrees.d1
  | 2 => degrees.d2
  | 3 => degrees.d3
  | 4 => degrees.d4
  | 5 => degrees.d5
  | _ => 0

def sixCompactAddSupportDegree
    (degrees : SixCompactDegrees) (s k : Nat) : SixCompactDegrees :=
  match s with
{degree_update_cases}
  | _ => degrees

def sixCompactCoverSlotValue (m slot : Nat) : Nat :=
  if slot = 0 then 1 else sixCompactMultiplicityDigit m (slot - 1)

def sixCompactCoverValue (m code : Nat) : Nat :=
  sixCompactCoverSlotValue m (Nat.land code 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 5) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 10) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 15) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 20) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 25) 31)

def sixCompactCoverGroupValue (m : Nat) (group : List Nat) : Nat :=
  (group.map fun code ↦ sixCompactCoverValue m code).sum

def sixRemainingCapacity (supports : List Nat) (v : Nat) : Nat :=
  3 * (supports.filter fun s ↦ sixSupportContains s v).length

def sixCompactDegreeStateValidBool
    (lowCount : Nat) (degrees : SixCompactDegrees) : Bool :=
  (List.range 6).all fun v ↦
    if v < lowCount then decide (sixCompactDegree degrees v = 3)
    else decide (4 ≤ sixCompactDegree degrees v)

def sixCompactMultiplicityChoices
    (lowCount : Nat) (degrees : SixCompactDegrees) (s : Nat) : List Nat :=
  (List.range 4).filter fun k ↦
    (decide (k = 0) || sixSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !sixSupportContains s v || decide (sixCompactDegree degrees v + k ≤ 3)

def sixCompactDegreeCompletionPossibleBool
    (lowCount : Nat) (supports : List Nat) (degrees : SixCompactDegrees) : Bool :=
  (List.range 6).all fun v ↦
    let target := if v < lowCount then 3 else 4
    decide (target ≤ sixCompactDegree degrees v + sixRemainingCapacity supports v)

def sixSupportMultigraphEarlyCheckAux
    (lowCount minimum : Nat) : List Nat → List (List Nat) →
      Nat → SixCompactDegrees → Nat → Bool
  | [], [], _, degrees, count =>
      if sixCompactDegreeStateValidBool lowCount degrees then decide (minimum ≤ count) else true
  | s :: supports, group :: groups, m, degrees, count =>
      (sixCompactMultiplicityChoices lowCount degrees s).all fun k ↦
        let nextM := sixCompactSetMultiplicity m s k
        let nextDegrees := sixCompactAddSupportDegree degrees s k
        let nextCount := count + sixCompactCoverGroupValue nextM group
        decide (minimum ≤ nextCount) ||
          !sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees ||
          sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups
            nextM nextDegrees nextCount
  | _, _, _, _, _ => false

def sixSupportMultigraphEarlyCheck (lowCount : Nat) : Bool :=
  match lowCount with
  | 4 => sixSupportMultigraphEarlyCheckAux 4 15 sixSupportOrder4 sixCompletionGroups4
      0 sixCompactDegreesZero 0
  | 5 => sixSupportMultigraphEarlyCheckAux 5 15 sixSupportOrder5 sixCompletionGroups5
      0 sixCompactDegreesZero 0
  | 6 => sixSupportMultigraphEarlyCheckAux 6 15 sixSupportOrder6 sixCompletionGroups6
      0 sixCompactDegreesZero 0
  | _ => false

def sixSupportMultigraphEarlySubcheckTwo (lowCount a b : Nat) : Bool :=
  let data := match lowCount with
    | 4 => some (sixSupportOrder4, sixCompletionGroups4)
    | 5 => some (sixSupportOrder5, sixCompletionGroups5)
    | 6 => some (sixSupportOrder6, sixCompletionGroups6)
    | _ => none
  match data with
  | some (s0 :: s1 :: supports, group0 :: group1 :: groups) =>
      let m0 := sixCompactSetMultiplicity 0 s0 a
      let degrees0 := sixCompactAddSupportDegree sixCompactDegreesZero s0 a
      let count0 := sixCompactCoverGroupValue m0 group0
      let m1 := sixCompactSetMultiplicity m0 s1 b
      let degrees1 := sixCompactAddSupportDegree degrees0 s1 b
      let count1 := count0 + sixCompactCoverGroupValue m1 group1
      decide (15 ≤ count1) ||
        !sixCompactDegreeCompletionPossibleBool lowCount supports degrees1 ||
        sixSupportMultigraphEarlyCheckAux lowCount 15 supports groups m1 degrees1 count1
  | _ => false

end AiMathLab.P0054.G417
"""


def prefix_theorem_name(low_count: int, prefix: tuple[int, ...]) -> str:
    return "six_support_multigraph_early_prefix_check_" + str(low_count) + "_" + "_".join(
        map(str, prefix)
    )


def prefix_check_expression(low_count: int, values: tuple[str, ...]) -> str:
    return (
        f"sixSupportMultigraphEarlyCheckValues {low_count} 15 "
        f"[{', '.join(values)}] sixSupportOrder{low_count} sixCompletionGroups{low_count} "
        "0 sixCompactDegreesZero 0"
    )


def check_module_name(low_count: int, prefix: tuple[int, ...]) -> str:
    return "SixSupportMultigraphCheck" + str(low_count) + "".join(map(str, prefix))


def generate_early_check(
    low_count: int, prefix: tuple[int, ...]
) -> str:
    return f"""import AiMathLab.P0054G417.SupportMultigraphEarlyPrefix

namespace AiMathLab.P0054.G417

set_option linter.style.longLine false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This bounded prefix leaves a kernel-reducible residual search.
theorem {prefix_theorem_name(low_count, prefix)} :
    {prefix_check_expression(low_count, tuple(map(str, prefix)))} = true := by
  rfl

end AiMathLab.P0054.G417
"""


def generate_prefix_tree(
    low_count: int, depth: int, prefixes: tuple[tuple[int, ...], ...]
) -> str:
    prefix_set = {
        candidate[:length]
        for candidate in prefixes
        for length in range(1, len(candidate) + 1)
    }
    lines = ["  fin_cases k0"]

    def admissibility_expression(prefix: tuple[int, ...]) -> str:
        values = tuple(map(str, prefix)) + tuple(
            f"k{position}.val" for position in range(len(prefix), depth)
        )
        return (
            f"sixSupportMultigraphEarlyValuesAdmissible {low_count} 15 "
            f"[{', '.join(values)}] sixSupportOrder{low_count} "
            f"sixCompletionGroups{low_count} 0 sixCompactDegreesZero 0"
        )

    def emit_cases(prefix: tuple[int, ...], position: int, indent: str) -> None:
        for value in range(4):
            child = prefix + (value,)
            descendants = child in prefix_set
            if not descendants:
                lines.extend(
                    [
                        f"{indent}· have hFalse :",
                        f"{indent}    {admissibility_expression(child)} = false := by",
                        f"{indent}      rfl",
                        f"{indent}  rw [hFalse] at hAdmissible",
                        f"{indent}  contradiction",
                    ]
                )
            elif position + 1 == depth:
                lines.append(f"{indent}· exact {prefix_theorem_name(low_count, child)}")
            else:
                lines.append(f"{indent}· fin_cases k{position + 1}")
                emit_cases(child, position + 1, indent + "  ")

    emit_cases((), 0, "  ")
    return "\n".join(lines)


def generate_checks(active_by_low: dict[int, tuple[tuple[int, ...], ...]]) -> str:
    imports = "\n".join(
        f"import AiMathLab.P0054G417.{check_module_name(low_count, prefix)}"
        for low_count in SUPPORT_ORDERS
        for prefix in active_by_low[low_count]
    )
    prefix_theorems = []
    list_theorems = []
    check_theorems = []
    for low_count in SUPPORT_ORDERS:
        depth = PREFIX_DEPTHS[low_count]
        argument_names = tuple(f"k{position}" for position in range(depth))
        argument_values = tuple(f"{name}.val" for name in argument_names)
        prefix_theorems.append(
            "set_option maxRecDepth 1000000 in\n"
            "set_option maxHeartbeats 0 in\n"
            "-- Inadmissible branches close before importing a residual certificate.\n"
            f"theorem six_support_multigraph_early_prefix_check_{low_count}\n"
            f"    ({' '.join(argument_names)} : Fin 4)\n"
            "    (hAdmissible :\n"
            f"      sixSupportMultigraphEarlyValuesAdmissible {low_count} 15 "
            f"[{', '.join(argument_values)}] sixSupportOrder{low_count}\n"
            f"        sixCompletionGroups{low_count} 0 sixCompactDegreesZero 0 = true) :\n"
            f"    {prefix_check_expression(low_count, argument_values)} = true := by\n"
            + generate_prefix_tree(low_count, depth, active_by_low[low_count])
        )

        destruct_lines = []
        for name in argument_names:
            destruct_lines.extend(
                [
                    f"  rcases values with ⟨⟩ | ⟨{name}, values⟩",
                    "  · simp at hLength",
                ]
            )
        list_expression = prefix_check_expression(low_count, ("values",)).replace(
            "[values]", "values"
        )
        bounded_arguments = " ".join(
            f"⟨{name}, hValues {name} (by simp)⟩" for name in argument_names
        )
        list_theorems.append(
            f"theorem six_support_multigraph_early_prefix_check_{low_count}_list\n"
            "    (values : List Nat)\n"
            f"    (hLength : values.length = {depth})\n"
            "    (hValues : ∀ k ∈ values, k < 4) :\n"
            f"    sixSupportMultigraphEarlyValuesAdmissible {low_count} 15 values\n"
            f"      sixSupportOrder{low_count} sixCompletionGroups{low_count}\n"
            "      0 sixCompactDegreesZero 0 = true →\n"
            f"    {list_expression} = true := by\n"
            "  intro hAdmissible\n"
            + "\n".join(destruct_lines)
            + "\n  cases values with\n"
            "  | cons extra values => simp at hLength\n"
            "  | nil =>\n"
            f"      exact six_support_multigraph_early_prefix_check_{low_count}\n"
            f"        {bounded_arguments}\n"
            "        hAdmissible"
        )

        check_theorems.append(
            f"theorem six_support_multigraph_early_check_{low_count} :\n"
            f"    sixSupportMultigraphEarlyCheck {low_count} = true := by\n"
            f"  change sixSupportMultigraphEarlyCheckAux {low_count} 15 "
            f"sixSupportOrder{low_count}\n"
            f"    sixCompletionGroups{low_count} 0 sixCompactDegreesZero 0 = true\n"
            f"  apply sixSupportMultigraphEarlyCheckAux_of_prefix {depth}\n"
            "  · decide\n"
            "  · rfl\n"
            f"  · exact six_support_multigraph_early_prefix_check_{low_count}_list"
        )
    return f"""{imports}

namespace AiMathLab.P0054.G417

set_option linter.style.longLine false

{chr(10).join(prefix_theorems)}

{chr(10).join(list_theorems)}

{chr(10).join(check_theorems)}

end AiMathLab.P0054.G417
"""


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    output = root / "AiMathLab" / "P0054G417"
    output.mkdir(parents=True, exist_ok=True)
    covers = minimal_support_covers()
    if len(covers) != 562:
        raise AssertionError(len(covers))
    (output / "SixSupportMultigraphFinite.lean").write_text(
        generate_finite(covers), encoding="utf-8"
    )
    (output / "SixSupportMultigraphEarly.lean").write_text(
        generate_early(covers), encoding="utf-8"
    )
    active_by_low = {
        low_count: active_prefixes(covers, low_count, PREFIX_DEPTHS[low_count])
        for low_count in SUPPORT_ORDERS
    }
    for path in output.glob("SixSupportMultigraphCheck*.lean"):
        path.unlink()
    for low_count in SUPPORT_ORDERS:
        for prefix in active_by_low[low_count]:
            (output / f"{check_module_name(low_count, prefix)}.lean").write_text(
                generate_early_check(low_count, prefix),
                encoding="utf-8",
            )
    (output / "SixSupportMultigraphChecks.lean").write_text(
        generate_checks(active_by_low), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
