import AiMathLab.P0054G420.FiveRowPairExactFiniteChecks
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyFour
import AiMathLab.P0054G420.FiveRowPairExactFinitePropertyThree

namespace AiMathLab.P0054.G420

open G413 G419

set_option maxHeartbeats 2000000 in
-- The generic bridge elaborates the complete-cover witness used by both instances.
theorem smallFourActualSupportMultiplicity_classified
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (pairBound : Nat) (leaf accept : FourMultiplicity → Bool)
    (hCheck : ∀ mask : Fin 16384,
      smallFourClassificationMaskCheck pairBound leaf accept mask.val = true)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hRowBounds : ∀ row < 4,
      0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5)
    (hBCard : (blocker T).card ≤ 5)
    (hPairCard : (pairRows (blocker T)).card ≤ pairBound)
    (hLeaf : leaf (fourActualSupportMultiplicity rowOrder) = true) :
    accept (fourActualSupportMultiplicity rowOrder) = true := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hClutter :=
    fourActualSupportMultiplicity_rows_clutter rowOrder hTClutter hBRows
  have hCovered :=
    fourActualSupportMultiplicity_active_supports_covered_of_complete
      rowOrder hTClutter hBRows four_minimal_support_index_covers_complete
  have hWeighted :=
    (fourWeightedCoverCount_le_blocker_card rowOrder hBRows).trans hBCard
  have hPair :=
    (fourPairCoverCount_le_pairRows_card rowOrder hBRows).trans hPairCard
  have hMask := smallFourMaskValid_multiplicityMask pairBound actual
    hRowBounds hClutter hCovered hWeighted hPair
  obtain ⟨finalDegrees, hGenerated⟩ :=
    smallFourGenerated_multiplicityMask pairBound actual
      (fourActualSupportMultiplicity_size rowOrder)
      (fun row hrow ↦ (hRowBounds row hrow).2) hWeighted hPair
  exact smallFourClassificationMaskCheck_sound hMask hGenerated hLeaf
    (hCheck ⟨fourMultiplicityMask actual, fourMultiplicityMask_lt actual⟩)

theorem fourExceptionalActualSupportMultiplicity_in_certificate
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hRowBounds : ∀ row < 4,
      0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5)
    (hBCard : (blocker T).card ≤ 5)
    (hPairCard : (pairRows (blocker T)).card ≤ 3)
    (hLeaf : fourExceptionalMultiplicityLeafValid
      (fourActualSupportMultiplicity rowOrder) = true) :
    fourExceptionalMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true := by
  exact smallFourActualSupportMultiplicity_classified rowOrder 3
    fourExceptionalMultiplicityLeafValid
    fourExceptionalMultiplicityInCertificate
    four_exceptional_pair_exact_classification_mask_check hTClutter hBRows
    hRowBounds hBCard hPairCard hLeaf

theorem threePaddedActualSupportMultiplicity_in_certificate
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hRowBounds : ∀ row < 4,
      0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5)
    (hBCard : (blocker T).card ≤ 5)
    (hPairCard : (pairRows (blocker T)).card = 0)
    (hLeaf : threePaddedMultiplicityLeafValid
      (fourActualSupportMultiplicity rowOrder) = true) :
    threePaddedMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true := by
  apply smallFourActualSupportMultiplicity_classified rowOrder 0
    threePaddedMultiplicityLeafValid
    threePaddedMultiplicityInCertificate
    three_padded_pair_exact_classification_mask_check hTClutter hBRows
    hRowBounds hBCard
  · omega
  · exact hLeaf

theorem fourExceptionalCertificate_activePoints_length
    (m : FourMultiplicity)
    (hCertificate : fourExceptionalMultiplicityInCertificate m = true) :
    (fourActivePoints m).length < 16 := by
  unfold fourExceptionalMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : m.toList = values := of_decide_eq_true hListCheck
  have hLength := four_exceptional_certificate_supports_length values hValues
  rw [← hList, middleFourModelSupports_length_eq_activePoints] at hLength
  exact hLength

theorem threePaddedCertificate_activePoints_length
    (m : FourMultiplicity)
    (hCertificate : threePaddedMultiplicityInCertificate m = true) :
    (fourActivePoints m).length < 16 := by
  unfold threePaddedMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : m.toList = values := of_decide_eq_true hListCheck
  have hLength := three_padded_certificate_supports_length values hValues
  rw [← hList, middleFourModelSupports_length_eq_activePoints] at hLength
  exact hLength

theorem fourExceptionalCertificate_model_property
    (m : FourMultiplicity)
    (hCertificate : fourExceptionalMultiplicityInCertificate m = true) :
    FourExceptionalModelProperty m.toList := by
  unfold fourExceptionalMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : m.toList = values := of_decide_eq_true hListCheck
  rw [hList]
  exact four_exceptional_certificate_property values hValues

theorem threePaddedCertificate_model_property
    (m : FourMultiplicity)
    (hCertificate : threePaddedMultiplicityInCertificate m = true) :
    ThreePaddedModelProperty m.toList := by
  unfold threePaddedMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : m.toList = values := of_decide_eq_true hListCheck
  rw [hList]
  exact three_padded_certificate_property values hValues

theorem middleFourBlockerRows_basePoint_inter_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    {P Q : G413.Row alpha} (hP : P ∈ blocker T) (hQ : Q ∈ blocker T) :
    ((P.image (middleFourBasePoint rowOrder centerPoint)) ∩
      (Q.image (middleFourBasePoint rowOrder centerPoint))).card =
        (P ∩ Q).card := by
  let pointMap := middleFourBasePoint rowOrder centerPoint
  have hPointInj := middleFourBasePoint_injOn_active
    rowOrder centerPoint hLength
  have hImageInter :
      (P ∩ Q).image pointMap =
        P.image pointMap ∩ Q.image pointMap := by
    apply Finset.Subset.antisymm
    · intro point hPoint
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hPoint
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨source, (Finset.mem_inter.mp hSource).1, rfl⟩,
          Finset.mem_image.mpr ⟨source, (Finset.mem_inter.mp hSource).2, rfl⟩⟩
    · intro point hPoint
      obtain ⟨hPointP, hPointQ⟩ := Finset.mem_inter.mp hPoint
      obtain ⟨left, hLeftP, hLeftEq⟩ := Finset.mem_image.mp hPointP
      obtain ⟨right, hRightQ, hRightEq⟩ := Finset.mem_image.mp hPointQ
      have hLeftActive := middleFourBlockerRow_subset_activeUniverse hP hLeftP
      have hRightActive := middleFourBlockerRow_subset_activeUniverse hQ hRightQ
      have hLeftRight : left = right :=
        hPointInj hLeftActive hRightActive (hLeftEq.trans hRightEq.symm)
      subst right
      exact Finset.mem_image.mpr
        ⟨left, Finset.mem_inter.mpr ⟨hLeftP, hRightQ⟩, hLeftEq⟩
  rw [← hImageInter]
  apply Finset.card_image_iff.mpr
  exact hPointInj.mono (by
    intro point hPoint
    exact middleFourBlockerRow_subset_activeUniverse hP
      (Finset.mem_inter.mp hPoint).1)

theorem fourExceptionalActualBlocker_property
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hCertificate : fourExceptionalMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true) :
    (blocker T).card = 5 ∧
      ∀ P ∈ blocker T, ∀ Q ∈ blocker T,
        3 ≤ P.card → 3 ≤ Q.card → P ≠ Q → (P ∩ Q).card = 2 := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hLength := fourExceptionalCertificate_activePoints_length actual hCertificate
  have hProperty := fourExceptionalCertificate_model_property actual hCertificate
  unfold FourExceptionalModelProperty at hProperty
  have hImage := middleFourActualBlocker_image_basePoint rowOrder centerPoint
    hBRows hLength
  constructor
  · have hCard := middleFourModelBlocker_card_eq_actual rowOrder hBRows hLength
    calc
      (blocker T).card = (middleFourModelBlocker actual.toList).card := hCard.symm
      _ = 5 := hProperty.1
  · intro P hP Q hQ hPCard hQCard hPQ
    let pointMap := middleFourBasePoint rowOrder centerPoint
    have hPModel : P.image pointMap ∈ middleFourModelBlocker actual.toList := by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
    have hQModel : Q.image pointMap ∈ middleFourModelBlocker actual.toList := by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    have hPImageCard := middleFourBlockerRow_basePoint_card
      rowOrder centerPoint hLength hP
    have hQImageCard := middleFourBlockerRow_basePoint_card
      rowOrder centerPoint hLength hQ
    have hPImageCard' : (P.image pointMap).card = P.card := by
      simpa [pointMap] using hPImageCard
    have hQImageCard' : (Q.image pointMap).card = Q.card := by
      simpa [pointMap] using hQImageCard
    have hImageNe : P.image pointMap ≠ Q.image pointMap := by
      intro hEq
      exact hPQ (middleFourBlockerRow_basePoint_injOn
        rowOrder centerPoint hLength hP hQ hEq)
    have hModelInter := hProperty.2 (P.image pointMap) hPModel
      (Q.image pointMap) hQModel (by omega) (by omega) hImageNe
    have hInterCard := middleFourBlockerRows_basePoint_inter_card
      rowOrder centerPoint hLength hP hQ
    have hInterCard' :
        (P.image pointMap ∩ Q.image pointMap).card = (P ∩ Q).card := by
      simpa [pointMap] using hInterCard
    omega

theorem threePaddedActualBlocker_property
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hCertificate : threePaddedMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true) :
    (blocker T).card = 5 ∧ ∀ P ∈ blocker T, P.card = 3 := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hLength := threePaddedCertificate_activePoints_length actual hCertificate
  have hProperty := threePaddedCertificate_model_property actual hCertificate
  unfold ThreePaddedModelProperty at hProperty
  have hImage := middleFourActualBlocker_image_basePoint rowOrder centerPoint
    hBRows hLength
  constructor
  · have hCard := middleFourModelBlocker_card_eq_actual rowOrder hBRows hLength
    calc
      (blocker T).card = (middleFourModelBlocker actual.toList).card := hCard.symm
      _ = 5 := hProperty.1
  · intro P hP
    let pointMap := middleFourBasePoint rowOrder centerPoint
    have hPModel : P.image pointMap ∈ middleFourModelBlocker actual.toList := by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
    have hPImageCard := middleFourBlockerRow_basePoint_card
      rowOrder centerPoint hLength hP
    have hModelCard := hProperty.2 (P.image pointMap) hPModel
    have hPImageCard' : (P.image pointMap).card = P.card := by
      simpa [pointMap] using hPImageCard
    omega

end AiMathLab.P0054.G420
