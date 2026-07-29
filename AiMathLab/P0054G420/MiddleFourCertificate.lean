import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

open G419

def fourRowPermutations : List (List Nat) :=
  [
    [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1],
    [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2],
    [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
    [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0],
    [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1],
    [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]
  ]

def fourPermuteSupportMask (permutation : List Nat) (mask : Nat) : Nat :=
  ((List.range 4).map fun row ↦
    if mask.testBit (permutation.getD row 0) then 2 ^ row else 0).sum

def fourPermuteMultiplicityValues (permutation : List Nat)
    (values : List Nat) : List Nat :=
  (List.range 14).map fun support ↦
    values.getD (fourPermuteSupportMask permutation (support + 1) - 1) 0

def fourRowPermutationEquivalent (left right : List Nat) : Bool :=
  fourRowPermutations.any fun permutation ↦
    decide (fourPermuteMultiplicityValues permutation left = right)

def middleFourCanonicalRepresentatives : List (List Nat) :=
  [
    [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0],
    [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0],
    [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0]
  ]

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_profile :
    ∀ values ∈ middleFourMultiplicityCertificate,
      (fourWeightedCoverCount values.toArray = 8 ∧
          fourPairCoverCount values.toArray = 4) ∨
        (fourWeightedCoverCount values.toArray = 7 ∧
          fourPairCoverCount values.toArray = 3) := by
  decide

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_canonical :
    ∀ values ∈ middleFourMultiplicityCertificate,
      middleFourCanonicalRepresentatives.any fun representative ↦
        fourRowPermutationEquivalent values representative := by
  decide

end AiMathLab.P0054.G420
