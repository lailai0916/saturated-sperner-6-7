import AiMathLab.P0054G419.KernelAActualProper

namespace AiMathLab.P0054.G419

open scoped BigOperators

def fourSupportCovers (C : Finset FourSupportIndex) : Prop :=
  ∀ row : FourVertex, ∃ s ∈ C, row ∈ fourSupport s

def fourMinimalSupportCover (C : Finset FourSupportIndex) : Prop :=
  fourSupportCovers C ∧ ∀ s ∈ C, ¬fourSupportCovers (C.erase s)

instance (C : Finset FourSupportIndex) : Decidable (fourSupportCovers C) := by
  unfold fourSupportCovers
  infer_instance

instance (C : Finset FourSupportIndex) : Decidable (fourMinimalSupportCover C) := by
  unfold fourMinimalSupportCover
  infer_instance

def fourMinimalSupportIndexCovers : List (List FourSupportIndex) :=
  [[0, 13], [1, 12], [2, 11], [2, 12], [2, 13], [3, 10], [4, 9],
    [4, 10], [4, 13], [5, 8], [5, 10], [5, 12], [6, 7], [6, 8],
    [6, 9], [6, 10], [6, 11], [6, 12], [6, 13], [8, 13], [9, 12],
    [10, 11], [10, 12], [10, 13], [12, 13], [0, 1, 11], [0, 3, 9],
    [0, 5, 7], [0, 5, 9], [0, 5, 11], [0, 9, 11], [1, 3, 8],
    [1, 4, 7], [1, 4, 8], [1, 4, 11], [1, 8, 11], [2, 3, 7],
    [2, 3, 8], [2, 3, 9], [2, 4, 7], [2, 4, 8], [2, 5, 7],
    [2, 5, 9], [3, 8, 9], [4, 5, 7], [4, 5, 11], [8, 9, 11],
    [0, 1, 3, 7]]

set_option maxRecDepth 100000 in
theorem four_minimal_support_index_covers_nodup :
    fourMinimalSupportIndexCovers.Nodup := by
  decide

set_option maxRecDepth 100000 in
theorem four_minimal_support_index_covers_each_sorted :
    ∀ C ∈ fourMinimalSupportIndexCovers, C.Pairwise (· < ·) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Exhaustive reduction over all support covers needs more than the default budget.
theorem four_minimal_support_index_covers_sound :
    ∀ C ∈ fourMinimalSupportIndexCovers,
      fourMinimalSupportCover C.toFinset := by
  decide

theorem four_minimal_support_index_covers_toFinset_injective :
    Set.InjOn List.toFinset
      (↑fourMinimalSupportIndexCovers.toFinset : Set (List FourSupportIndex)) := by
  intro C hC D hD hSets
  have hCSorted := four_minimal_support_index_covers_each_sorted C
    (List.mem_toFinset.mp hC)
  have hDSorted := four_minimal_support_index_covers_each_sorted D
    (List.mem_toFinset.mp hD)
  have hPerm := List.perm_of_nodup_nodup_toFinset_eq
    hCSorted.nodup hDSorted.nodup hSets
  exact hPerm.eq_of_pairwise' hCSorted hDSorted

def fourCoverCodeSlots (code : Nat) : List Nat :=
  [Nat.land code 15,
    Nat.land (Nat.shiftRight code 4) 15,
    Nat.land (Nat.shiftRight code 8) 15,
    Nat.land (Nat.shiftRight code 12) 15]

def fourCoverCodeSupports (code : Nat) : List Nat :=
  (fourCoverCodeSlots code).filterMap fun slot ↦
    if slot = 0 then none else some (slot - 1)

theorem four_cover_slot_values_filterMap_prod
    (m : FourMultiplicity) (slots : List Nat) :
    ((slots.filterMap fun slot ↦
        if slot = 0 then none else some (slot - 1)).map
      (fourMultiplicityDigit m)).prod =
        (slots.map (fourCoverSlotValue m)).prod := by
  induction slots with
  | nil => simp
  | cons slot slots ih =>
      by_cases hslot : slot = 0
      · simp [hslot, fourCoverSlotValue, ih]
      · simp [hslot, fourCoverSlotValue, ih]

theorem four_cover_code_value_eq_support_product
    (m : FourMultiplicity) (code : Nat) :
    ((fourCoverCodeSupports code).map (fourMultiplicityDigit m)).prod =
      fourCoverCodeValue m code := by
  rw [fourCoverCodeSupports, four_cover_slot_values_filterMap_prod]
  simp [fourCoverCodeSlots, fourCoverCodeValue, Nat.mul_assoc]

set_option maxRecDepth 100000 in
theorem four_minimal_support_index_covers_values :
    (fourMinimalSupportIndexCovers.map fun C ↦
      C.map fun s ↦ s.val) = fourMinimalSupportCovers := by
  decide

set_option maxRecDepth 100000 in
theorem four_minimal_support_cover_codes_supports :
    fourMinimalSupportCoverCodes.map fourCoverCodeSupports =
      fourMinimalSupportCovers := by
  decide

theorem four_weighted_cover_count_eq_index_covers (m : FourMultiplicity) :
    (fourMinimalSupportIndexCovers.map fun C ↦
      (C.map fun s ↦ fourMultiplicityDigit m s.val).prod).sum =
        fourWeightedCoverCount m := by
  calc
    (fourMinimalSupportIndexCovers.map fun C ↦
        (C.map fun s ↦ fourMultiplicityDigit m s.val).prod).sum =
        ((fourMinimalSupportIndexCovers.map fun C ↦
          C.map fun s ↦ s.val).map fun C ↦
            (C.map (fourMultiplicityDigit m)).prod).sum := by
      simp only [List.map_map, Function.comp_def]
    _ = (fourMinimalSupportCovers.map fun C ↦
          (C.map (fourMultiplicityDigit m)).prod).sum := by
      rw [four_minimal_support_index_covers_values]
    _ = ((fourMinimalSupportCoverCodes.map fourCoverCodeSupports).map fun C ↦
          (C.map (fourMultiplicityDigit m)).prod).sum := by
      rw [four_minimal_support_cover_codes_supports]
    _ = (fourMinimalSupportCoverCodes.map (fourCoverCodeValue m)).sum := by
      simp only [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro code _hcode
      exact four_cover_code_value_eq_support_product m code
    _ = fourWeightedCoverCount m := rfl

end AiMathLab.P0054.G419
