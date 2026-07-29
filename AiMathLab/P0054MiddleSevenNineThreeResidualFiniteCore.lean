import AiMathLab.P0054MiddleSevenNineSevenSideBasics

/-!
# Finite classification of a three-row residual marginal

The six coordinates are the multiplicities of supports
`1, 2, 4, 3, 5, 6`, written mathematically as
`(p, q, r, x12, x13, x23)`.  In the stored list they occur in mask order
`[p, q, x12, r, x13, x23]`.
-/

namespace AiMathLab.P0054.MiddleSevenNineThreeResidualFinite

def threeRowPermutations : List (List Nat) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2],
   [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def threePermuteSupportMask (permutation : List Nat) (mask : Nat) : Nat :=
  ((List.range 3).map fun row ↦
    if mask.testBit (permutation.getD row 0) then 2 ^ row else 0).sum

def threePermuteMultiplicityValues (permutation values : List Nat) : List Nat :=
  (List.range 6).map fun support ↦
    values.getD (threePermuteSupportMask permutation (support + 1) - 1) 0

def threeResidualCanonicalMultiplicities : List (List Nat) :=
  [[2, 1, 0, 1, 0, 1],
   [2, 1, 0, 0, 1, 1],
   [1, 1, 1, 1, 1, 0],
   [1, 1, 0, 0, 1, 1],
   [1, 0, 1, 0, 1, 1],
   [0, 0, 1, 0, 1, 1]]

def threeResidualMultiplicityValues
    (p q r x12 x13 x23 : Nat) : List Nat :=
  [p, q, x12, r, x13, x23]

def threeResidualMarginalValid
    (p q r x12 x13 x23 : Nat) : Bool :=
  decide (
    2 ≤ p + x12 + x13 ∧ p + x12 + x13 ≤ 5 ∧
    2 ≤ q + x12 + x23 ∧ q + x12 + x23 ≤ 5 ∧
    2 ≤ r + x13 + x23 ∧ r + x13 + x23 ≤ 5 ∧
    0 < p + x13 ∧ 0 < q + x23 ∧
    0 < p + x12 ∧ 0 < r + x23 ∧
    0 < q + x12 ∧ 0 < r + x13 ∧
    x12 * x13 + x12 * x23 + x13 * x23 +
      x12 * r + x13 * q + x23 * p + p * q * r ≤ 4)

def threeResidualMarginalAccepted
    (p q r x12 x13 x23 : Nat) : Bool :=
  let values := threeResidualMultiplicityValues p q r x12 x13 x23
  threeResidualCanonicalMultiplicities.any fun representative ↦
    threeRowPermutations.any fun permutation ↦
      decide (threePermuteMultiplicityValues permutation values = representative)

def threeResidualMarginalPrefixCheck (p : Nat) : Bool :=
  (List.range 6).all fun q ↦
    (List.range 6).all fun r ↦
      (List.range 6).all fun x12 ↦
        (List.range 6).all fun x13 ↦
          (List.range 6).all fun x23 ↦
            !threeResidualMarginalValid p q r x12 x13 x23 ||
              threeResidualMarginalAccepted p q r x12 x13 x23

def threeResidualMarginalCertificateCheck : Bool :=
  (List.range 6).all threeResidualMarginalPrefixCheck

theorem threeResidualMarginalPrefixCheck_sound
    {p q r x12 x13 x23 : Nat}
    (hq : q < 6) (hr : r < 6) (hx12 : x12 < 6)
    (hx13 : x13 < 6) (hx23 : x23 < 6)
    (hCheck : threeResidualMarginalPrefixCheck p = true)
    (hValid : threeResidualMarginalValid p q r x12 x13 x23 = true) :
    threeResidualMarginalAccepted p q r x12 x13 x23 = true := by
  have hqAll := List.all_eq_true.mp hCheck q (List.mem_range.mpr hq)
  have hrAll := List.all_eq_true.mp hqAll r (List.mem_range.mpr hr)
  have hx12All := List.all_eq_true.mp hrAll x12 (List.mem_range.mpr hx12)
  have hx13All := List.all_eq_true.mp hx12All x13 (List.mem_range.mpr hx13)
  have hx23Check := List.all_eq_true.mp hx13All x23 (List.mem_range.mpr hx23)
  simpa [hValid] using hx23Check

theorem threeResidualMarginalCertificateCheck_sound
    {p q r x12 x13 x23 : Nat}
    (hp : p < 6) (hq : q < 6) (hr : r < 6)
    (hx12 : x12 < 6) (hx13 : x13 < 6) (hx23 : x23 < 6)
    (hCheck : threeResidualMarginalCertificateCheck = true)
    (hValid : threeResidualMarginalValid p q r x12 x13 x23 = true) :
    threeResidualMarginalAccepted p q r x12 x13 x23 = true := by
  have hPrefix : threeResidualMarginalPrefixCheck p = true := by
    exact List.all_eq_true.mp (by
      simpa [threeResidualMarginalCertificateCheck] using hCheck)
      p (List.mem_range.mpr hp)
  exact threeResidualMarginalPrefixCheck_sound hq hr hx12 hx13 hx23
    hPrefix hValid

theorem threeResidualMarginalAccepted_iff_certificate
    {p q r x12 x13 x23 : Nat} :
    threeResidualMarginalAccepted p q r x12 x13 x23 = true ↔
      ∃ representative ∈ threeResidualCanonicalMultiplicities,
        ∃ permutation ∈ threeRowPermutations,
          threePermuteMultiplicityValues permutation
            (threeResidualMultiplicityValues p q r x12 x13 x23) =
              representative := by
  constructor
  · intro hAccepted
    unfold threeResidualMarginalAccepted at hAccepted
    obtain ⟨representative, hRepresentative, hPermutationCheck⟩ :=
      List.any_eq_true.mp hAccepted
    obtain ⟨permutation, hPermutation, hValues⟩ :=
      List.any_eq_true.mp hPermutationCheck
    exact ⟨representative, hRepresentative, permutation, hPermutation,
      of_decide_eq_true hValues⟩
  · rintro ⟨representative, hRepresentative, permutation, hPermutation,
      hValues⟩
    unfold threeResidualMarginalAccepted
    apply List.any_eq_true.mpr
    refine ⟨representative, hRepresentative, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨permutation, hPermutation, decide_eq_true hValues⟩

end AiMathLab.P0054.MiddleSevenNineThreeResidualFinite
