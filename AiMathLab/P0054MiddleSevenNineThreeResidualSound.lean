import AiMathLab.P0054MiddleSevenNineSixResidualSound
import AiMathLab.P0054MiddleSevenNineThreeResidualCertificate
import AiMathLab.P0054MiddleSevenNineSixCouplingFiniteCore

/-!
# Arbitrary-finite soundness for the three-row residual certificate

This module connects a genuine three-row clutter on an arbitrary finite type
to the six multiplicities checked by the finite certificate.
-/

namespace AiMathLab.P0054.MiddleSevenNineThreeResidualSound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.MiddleSevenNineThreeResidualFinite
open AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

def threeMultiplicitySupportList (values : List Nat) : List Nat :=
  List.replicate (values.getD 0 0) 1 ++
    List.replicate (values.getD 1 0) 2 ++
    List.replicate (values.getD 2 0) 3 ++
    List.replicate (values.getD 3 0) 4 ++
    List.replicate (values.getD 4 0) 5 ++
    List.replicate (values.getD 5 0) 6

theorem canonical_multiplicity_has_residual_profile
    {values : List Nat}
    (hValues : values ∈ threeResidualCanonicalMultiplicities) :
    ∃ index, index < 6 ∧
      threeMultiplicitySupportList values = sixResidualProfile index := by
  simp only [threeResidualCanonicalMultiplicities, List.mem_cons,
    List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨3, by omega, rfl⟩
  · exact ⟨4, by omega, rfl⟩
  · exact ⟨5, by omega, rfl⟩

theorem accepted_has_residual_profile
    {p q r x12 x13 x23 : Nat}
    (hAccepted :
      threeResidualMarginalAccepted p q r x12 x13 x23 = true) :
    ∃ representative ∈ threeResidualCanonicalMultiplicities,
      ∃ permutation ∈ threeRowPermutations,
        ∃ index, index < 6 ∧
          threePermuteMultiplicityValues permutation
              (threeResidualMultiplicityValues p q r x12 x13 x23) =
            representative ∧
          threeMultiplicitySupportList representative =
            sixResidualProfile index := by
  obtain ⟨representative, hRepresentative, permutation, hPermutation,
      hValues⟩ :=
    threeResidualMarginalAccepted_iff_certificate.mp hAccepted
  obtain ⟨index, hIndex, hProfile⟩ :=
    canonical_multiplicity_has_residual_profile hRepresentative
  exact ⟨representative, hRepresentative, permutation, hPermutation,
    index, hIndex, hValues, hProfile⟩

theorem threeRow_residual_marginal_accepted
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 3)
    (hHRowsLower : RowsCardAtLeast H 2)
    (hHRowsUpper : ∀ R ∈ H, R.card ≤ 5)
    (hNoCommon : ∀ point, ∃ R ∈ H, point ∉ R)
    (hBlockerUpper : (blocker H).card ≤ 4) :
    ∃ A B C,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ H = {A, B, C} ∧
      threeResidualMarginalAccepted
        (privatePart A B C).card
        (privatePart B A C).card
        (privatePart C A B).card
        (sharedPart A B C).card
        (sharedPart A C B).card
        (sharedPart B C A).card = true := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hH⟩ :=
    Finset.card_eq_three.mp hHCard
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hNoCommonABC : ∀ point, ¬(point ∈ A ∧ point ∈ B ∧ point ∈ C) := by
    intro point hPoint
    obtain ⟨R, hRH, hPointR⟩ := hNoCommon point
    rw [hH] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with rfl | rfl | rfl
    · exact hPointR hPoint.1
    · exact hPointR hPoint.2.1
    · exact hPointR hPoint.2.2
  let p := (privatePart A B C).card
  let q := (privatePart B A C).card
  let r := (privatePart C A B).card
  let x12 := (sharedPart A B C).card
  let x13 := (sharedPart A C B).card
  let x23 := (sharedPart B C A).card
  have hACard : A.card = p + x12 + x13 := by
    simpa [p, x12, x13] using threePart_union_card hNoCommonABC
  have hBCard : B.card = q + x12 + x23 := by
    simpa [q, x12, x23] using threePart_union_card_second hNoCommonABC
  have hCCard : C.card = r + x13 + x23 := by
    simpa [r, x13, x23] using threePart_union_card_third hNoCommonABC
  have hALower := hHRowsLower A hAH
  have hBLower := hHRowsLower B hBH
  have hCLower := hHRowsLower C hCH
  have hAUpper := hHRowsUpper A hAH
  have hBUpper := hHRowsUpper B hBH
  have hCUpper := hHRowsUpper C hCH
  have hAnotB : ¬ A ⊆ B := by
    intro hSubset
    exact hAB (hHClutter hAH hBH hSubset)
  have hBnotA : ¬ B ⊆ A := by
    intro hSubset
    exact hAB (hHClutter hBH hAH hSubset).symm
  have hAnotC : ¬ A ⊆ C := by
    intro hSubset
    exact hAC (hHClutter hAH hCH hSubset)
  have hCnotA : ¬ C ⊆ A := by
    intro hSubset
    exact hAC (hHClutter hCH hAH hSubset).symm
  have hBnotC : ¬ B ⊆ C := by
    intro hSubset
    exact hBC (hHClutter hBH hCH hSubset)
  have hCnotB : ¬ C ⊆ B := by
    intro hSubset
    exact hBC (hHClutter hCH hBH hSubset).symm
  have hPY : 0 < p + x13 := by
    obtain ⟨point, hPointA, hPointB⟩ := Finset.not_subset.mp hAnotB
    by_cases hPointC : point ∈ C
    · have hPointY : point ∈ sharedPart A C B :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointA, hPointC⟩, hPointB⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointY⟩
      dsimp [x13]
      omega
    · have hPointP : point ∈ privatePart A B C :=
        Finset.mem_sdiff.mpr ⟨hPointA, by simp [hPointB, hPointC]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointP⟩
      dsimp [p]
      omega
  have hQZ : 0 < q + x23 := by
    obtain ⟨point, hPointB, hPointA⟩ := Finset.not_subset.mp hBnotA
    by_cases hPointC : point ∈ C
    · have hPointZ : point ∈ sharedPart B C A :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointB, hPointC⟩, hPointA⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointZ⟩
      dsimp [x23]
      omega
    · have hPointQ : point ∈ privatePart B A C :=
        Finset.mem_sdiff.mpr ⟨hPointB, by simp [hPointA, hPointC]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointQ⟩
      dsimp [q]
      omega
  have hPX : 0 < p + x12 := by
    obtain ⟨point, hPointA, hPointC⟩ := Finset.not_subset.mp hAnotC
    by_cases hPointB : point ∈ B
    · have hPointX : point ∈ sharedPart A B C :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointA, hPointB⟩, hPointC⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointX⟩
      dsimp [x12]
      omega
    · have hPointP : point ∈ privatePart A B C :=
        Finset.mem_sdiff.mpr ⟨hPointA, by simp [hPointB, hPointC]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointP⟩
      dsimp [p]
      omega
  have hRZ : 0 < r + x23 := by
    obtain ⟨point, hPointC, hPointA⟩ := Finset.not_subset.mp hCnotA
    by_cases hPointB : point ∈ B
    · have hPointZ : point ∈ sharedPart B C A :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointB, hPointC⟩, hPointA⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointZ⟩
      dsimp [x23]
      omega
    · have hPointR : point ∈ privatePart C A B :=
        Finset.mem_sdiff.mpr ⟨hPointC, by simp [hPointA, hPointB]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointR⟩
      dsimp [r]
      omega
  have hQX : 0 < q + x12 := by
    obtain ⟨point, hPointB, hPointC⟩ := Finset.not_subset.mp hBnotC
    by_cases hPointA : point ∈ A
    · have hPointX : point ∈ sharedPart A B C :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointA, hPointB⟩, hPointC⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointX⟩
      dsimp [x12]
      omega
    · have hPointQ : point ∈ privatePart B A C :=
        Finset.mem_sdiff.mpr ⟨hPointB, by simp [hPointA, hPointC]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointQ⟩
      dsimp [q]
      omega
  have hRY : 0 < r + x13 := by
    obtain ⟨point, hPointC, hPointB⟩ := Finset.not_subset.mp hCnotB
    by_cases hPointA : point ∈ A
    · have hPointY : point ∈ sharedPart A C B :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointA, hPointC⟩, hPointB⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointY⟩
      dsimp [x13]
      omega
    · have hPointR : point ∈ privatePart C A B :=
        Finset.mem_sdiff.mpr ⟨hPointC, by simp [hPointA, hPointB]⟩
      have hPositive := Finset.card_pos.mpr ⟨point, hPointR⟩
      dsimp [r]
      omega
  have hGenerated :
      x12 * x13 + x12 * x23 + x13 * x23 +
          x12 * r + x13 * q + x23 * p + p * q * r ≤ 4 := by
    have hLower := threeGeneratedRows_card_le_blocker hH hAB hAC hBC
    have hGeneratedLower :
        x12 * x13 + x12 * x23 + x13 * x23 +
            x12 * r + x13 * q + x23 * p + p * q * r ≤
          (blocker H).card := by
      simpa [p, q, r, x12, x13, x23] using hLower
    exact hGeneratedLower.trans hBlockerUpper
  have hValid :
      threeResidualMarginalValid p q r x12 x13 x23 = true := by
    unfold threeResidualMarginalValid
    apply decide_eq_true
    rw [hACard] at hALower hAUpper
    rw [hBCard] at hBLower hBUpper
    rw [hCCard] at hCLower hCUpper
    exact ⟨hALower, hAUpper, hBLower, hBUpper, hCLower, hCUpper,
      hPY, hQZ, hPX, hRZ, hQX, hRY, hGenerated⟩
  have hp : p < 6 := by omega
  have hq : q < 6 := by omega
  have hr : r < 6 := by omega
  have hx12 : x12 < 6 := by omega
  have hx13 : x13 < 6 := by omega
  have hx23 : x23 < 6 := by omega
  have hAccepted : threeResidualMarginalAccepted p q r x12 x13 x23 = true :=
    threeResidualMarginalCertificateCheck_sound hp hq hr hx12 hx13 hx23
      three_residual_marginal_certificate_check hValid
  refine ⟨A, B, C, hAB, hAC, hBC, hH, ?_⟩
  simpa [p, q, r, x12, x13, x23] using hAccepted

theorem threeRow_residual_marginal_profile
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 3)
    (hHRowsLower : RowsCardAtLeast H 2)
    (hHRowsUpper : ∀ R ∈ H, R.card ≤ 5)
    (hNoCommon : ∀ point, ∃ R ∈ H, point ∉ R)
    (hBlockerUpper : (blocker H).card ≤ 4) :
    ∃ A B C,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ H = {A, B, C} ∧
      ∃ representative ∈ threeResidualCanonicalMultiplicities,
        ∃ permutation ∈ threeRowPermutations,
          ∃ index, index < 6 ∧
            threePermuteMultiplicityValues permutation
                (threeResidualMultiplicityValues
                  (privatePart A B C).card
                  (privatePart B A C).card
                  (privatePart C A B).card
                  (sharedPart A B C).card
                  (sharedPart A C B).card
                  (sharedPart B C A).card) = representative ∧
            threeMultiplicitySupportList representative =
              sixResidualProfile index := by
  obtain ⟨A, B, C, hAB, hAC, hBC, hH, hAccepted⟩ :=
    threeRow_residual_marginal_accepted hHClutter hHCard
      hHRowsLower hHRowsUpper hNoCommon hBlockerUpper
  obtain ⟨representative, hRepresentative, permutation, hPermutation,
      index, hIndex, hValues, hProfile⟩ :=
    accepted_has_residual_profile hAccepted
  exact ⟨A, B, C, hAB, hAC, hBC, hH,
    representative, hRepresentative, permutation, hPermutation,
    index, hIndex, hValues, hProfile⟩

end AiMathLab.P0054.MiddleSevenNineThreeResidualSound
