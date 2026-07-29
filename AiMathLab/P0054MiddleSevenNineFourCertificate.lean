import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenEightFiniteCore
import AiMathLab.P0054G420.MiddleFourCertificate

/-!
# The exact four-row certificate for the seven-plus-nine split

The executable classifier retains 136 labelled multiplicity vectors.  This
module checks, inside Lean, their four possible blocker/pair-count profiles
and their reduction to eleven row-permutation classes.
-/

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

def middleSevenNineFourCanonicalRepresentatives : List (List Nat) :=
  [
    [1, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0],
    [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [1, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0],
    [1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0],
    [1, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0],
    [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0],
    [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]
  ]

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_profile :
    ∀ values ∈ middleFourMultiplicityCertificate,
      (fourWeightedCoverCount values.toArray = 7 ∧
          fourPairCoverCount values.toArray = 3) ∨
      (fourWeightedCoverCount values.toArray = 8 ∧
          fourPairCoverCount values.toArray = 4) ∨
      (fourWeightedCoverCount values.toArray = 9 ∧
          fourPairCoverCount values.toArray = 3) ∨
      (fourWeightedCoverCount values.toArray = 9 ∧
          fourPairCoverCount values.toArray = 4) := by
  decide

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_canonical :
    ∀ values ∈ middleFourMultiplicityCertificate,
      middleSevenNineFourCanonicalRepresentatives.any fun representative ↦
        fourRowPermutationEquivalent values representative := by
  decide

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_supports_length :
    ∀ values ∈ middleFourMultiplicityCertificate,
      (middleFourModelSupports values).length ≤ 8 := by
  decide

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_k4_of_seven :
    ∀ values ∈ middleFourMultiplicityCertificate,
      fourWeightedCoverCount values.toArray = 7 →
      fourPairCoverCount values.toArray = 3 →
      values = MiddleSevenEightFinite.sevenEightK4Values := by
  decide

end AiMathLab.P0054.MiddleSevenNineFinite
