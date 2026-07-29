import AiMathLab.P0054G419.KernelAActualValid
import Mathlib.Combinatorics.Colex

namespace AiMathLab.P0054.G419

open scoped BigOperators

def fourActiveSupportFinset (m : FourMultiplicity) : Finset Nat :=
  (Finset.range 14).filter fun s ↦ 0 < fourMultiplicityDigit m s

def fourMultiplicityMask (m : FourMultiplicity) : Nat :=
  ∑ s ∈ fourActiveSupportFinset m, 2 ^ s

theorem fourMultiplicityMask_bitIndices (m : FourMultiplicity) :
    (fourMultiplicityMask m).bitIndices.toFinset = fourActiveSupportFinset m := by
  simp [fourMultiplicityMask]

theorem fourMultiplicityMask_testBit_true_iff
    (m : FourMultiplicity) {s : Nat} (hs : s < 14) :
    (fourMultiplicityMask m).testBit s = true ↔
      0 < fourMultiplicityDigit m s := by
  calc
    (fourMultiplicityMask m).testBit s = true ↔
        (fourMultiplicityMask m).testBit s := by simp
    _ ↔ s ∈ (fourMultiplicityMask m).bitIndices := Nat.mem_bitIndices.symm
    _ ↔ s ∈ (fourMultiplicityMask m).bitIndices.toFinset := by simp
    _ ↔ s ∈ fourActiveSupportFinset m := by rw [fourMultiplicityMask_bitIndices]
    _ ↔ 0 < fourMultiplicityDigit m s := by
      simp [fourActiveSupportFinset, hs]

theorem fourMultiplicityMask_lt (m : FourMultiplicity) :
    fourMultiplicityMask m < 16384 := by
  have hSubset : fourActiveSupportFinset m ⊆ Finset.range 14 :=
    Finset.filter_subset _ _
  calc
    fourMultiplicityMask m ≤ ∑ s ∈ Finset.range 14, 2 ^ s := by
      exact Finset.sum_le_sum_of_subset hSubset
    _ < 16384 := by norm_num [Finset.sum_range_succ]

theorem fourMaskSupports_multiplicityMask (m : FourMultiplicity) :
    fourMaskSupports (fourMultiplicityMask m) =
      (List.range 14).filter fun s ↦ decide (0 < fourMultiplicityDigit m s) := by
  unfold fourMaskSupports fourMaskContains
  apply List.filter_congr
  intro s hs
  apply Bool.eq_iff_iff.mpr
  simpa using fourMultiplicityMask_testBit_true_iff m (List.mem_range.mp hs)

theorem fourMultiplicityForMask_multiplicityMask_digit
    (m : FourMultiplicity) {s : Nat} (hs : s < 14) :
    fourMultiplicityDigit (fourMultiplicityForMask (fourMultiplicityMask m)) s =
      if 0 < fourMultiplicityDigit m s then 1 else 0 := by
  rw [fourMultiplicityDigit, fourMultiplicityForMask]
  simp only [Array.getD_eq_getD_getElem?]
  simp [hs, fourMultiplicityMask_testBit_true_iff m hs]

end AiMathLab.P0054.G419
