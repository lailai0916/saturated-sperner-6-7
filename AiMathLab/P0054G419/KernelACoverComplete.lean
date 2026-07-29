import AiMathLab.P0054G419.KernelACovers
import Mathlib.Combinatorics.Colex

namespace AiMathLab.P0054.G419

def fourSupportIndexFinsetForMask (mask : Nat) : Finset FourSupportIndex :=
  Finset.univ.filter fun s ↦ mask.testBit s.val

def fourMinimalSupportCoverMaskCheck (mask : Nat) : Bool :=
  !decide (fourMinimalSupportCover (fourSupportIndexFinsetForMask mask)) ||
    fourMinimalSupportIndexCovers.any fun C ↦
      decide (C.toFinset = fourSupportIndexFinsetForMask mask)

def fourMinimalSupportCoverChunkCheck (chunk : Nat) : Bool :=
  ((List.range 64).map fun offset ↦ chunk * 64 + offset).all
    fourMinimalSupportCoverMaskCheck

def fourSupportIndexMask (C : Finset FourSupportIndex) : Nat :=
  ∑ s ∈ C.image Fin.val, 2 ^ s

theorem fourSupportIndexFinsetForMask_indexMask
    (C : Finset FourSupportIndex) :
    fourSupportIndexFinsetForMask (fourSupportIndexMask C) = C := by
  ext s
  simp only [fourSupportIndexFinsetForMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [show (fourSupportIndexMask C).testBit s.val = true ↔
      s.val ∈ (fourSupportIndexMask C).bitIndices from Nat.mem_bitIndices.symm]
  rw [show s.val ∈ (fourSupportIndexMask C).bitIndices ↔
      s.val ∈ (fourSupportIndexMask C).bitIndices.toFinset by simp]
  rw [show (fourSupportIndexMask C).bitIndices.toFinset = C.image Fin.val by
    simp [fourSupportIndexMask]]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hiC, hi⟩
    exact Fin.ext hi ▸ hiC
  · intro hsC
    exact ⟨s, hsC, rfl⟩

theorem fourSupportIndexMask_lt (C : Finset FourSupportIndex) :
    fourSupportIndexMask C < 16384 := by
  have hSubset : C.image Fin.val ⊆ Finset.range 14 := by
    intro s hs
    obtain ⟨i, _hiC, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_range.mpr i.isLt
  calc
    fourSupportIndexMask C ≤ ∑ s ∈ Finset.range 14, 2 ^ s := by
      exact Finset.sum_le_sum_of_subset hSubset
    _ < 16384 := by norm_num [Finset.sum_range_succ]

end AiMathLab.P0054.G419
