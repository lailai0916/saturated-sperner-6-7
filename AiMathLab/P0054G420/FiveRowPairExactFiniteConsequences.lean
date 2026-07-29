import AiMathLab.P0054G420.FiveRowPairExactPadding
import AiMathLab.P0054G420.MiddleFourActualEnumerated

namespace AiMathLab.P0054.G420

open G413 G419

noncomputable def fourRowOrderAt
    {alpha : Type*} [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (hTCard : T.card = 4)
    (E : G413.Row alpha) (hE : E ∈ T) : Fin 4 ≃ T :=
  let base := fourRowOrder hTCard
  (Equiv.swap (0 : Fin 4) (base.symm ⟨E, hE⟩)).trans base

@[simp]
theorem fourRowOrderAt_zero
    {alpha : Type*} [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (hTCard : T.card = 4)
    (E : G413.Row alpha) (hE : E ∈ T) :
    (fourRowOrderAt hTCard E hE 0 : G413.Row alpha) = E := by
  simp [fourRowOrderAt, Equiv.trans_apply, Equiv.swap_apply_left]

theorem fourActualRowDegree_eq_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2) (row : Fin 4) :
    fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val =
      (rowOrder row : G413.Row alpha).card := by
  exact fourRowDegree_actualSupportMultiplicity rowOrder
    (fourRows_actual_support_proper rowOrder hBRows) row

theorem pairRow_eq_of_pairRows_card_le_one
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hPairUpper : (pairRows H).card ≤ 1)
    {E F : G413.Row alpha} (hE : E ∈ pairRows H)
    (hF : F ∈ pairRows H) : E = F := by
  classical
  by_contra hNe
  have hSubset : ({E, F} : G413.Hypergraph alpha) ⊆ pairRows H := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact hE
    · exact hF
  have hLower := Finset.card_le_card hSubset
  rw [Finset.card_pair hNe] at hLower
  omega

set_option maxHeartbeats 2000000 in
-- The exceptional certificate is used only after the structural hypotheses
-- have identified a unique two-point row.
theorem fourRow_uniquePair_blocker_property
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 2)
    (hHUpper : ∀ E ∈ H, E.card ≤ 5)
    (hPairUpper : (pairRows H).card ≤ 1)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBCard : (blocker H).card ≤ 5)
    (hBPairUpper : (pairRows (blocker H)).card ≤ 3)
    {E : G413.Row alpha} (hEH : E ∈ H) (hECard : E.card = 2) :
    (blocker H).card = 5 ∧
      ∀ P ∈ blocker H, ∀ Q ∈ blocker H,
        3 ≤ P.card → 3 ≤ Q.card → P ≠ Q → (P ∩ Q).card = 2 := by
  classical
  let rowOrder := fourRowOrderAt hHCard E hEH
  have hRowZero : (rowOrder 0 : G413.Row alpha) = E := by
    simpa [rowOrder] using fourRowOrderAt_zero hHCard E hEH
  have hEPair : E ∈ pairRows H :=
    Finset.mem_filter.mpr ⟨hEH, hECard⟩
  have hRowsOther : ∀ row : Fin 4, row ≠ 0 →
      3 ≤ (rowOrder row : G413.Row alpha).card := by
    intro row hRowNe
    have hMember : (rowOrder row : G413.Row alpha) ∈ H :=
      (rowOrder row).property
    have hLower := hHRows _ hMember
    have hNotPair : (rowOrder row : G413.Row alpha).card ≠ 2 := by
      intro hCard
      have hPair : (rowOrder row : G413.Row alpha) ∈ pairRows H :=
        Finset.mem_filter.mpr ⟨hMember, hCard⟩
      have hEq := pairRow_eq_of_pairRows_card_le_one hPairUpper hPair hEPair
      have hIndexEq : row = 0 := rowOrder.injective (Subtype.ext (hEq.trans hRowZero.symm))
      exact hRowNe hIndexEq
    omega
  have hRowBounds : ∀ row < 4,
      0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5 := by
    intro row hRow
    let index : Fin 4 := ⟨row, hRow⟩
    have hDegree := fourActualRowDegree_eq_card rowOrder hBRows index
    have hLower := hHRows (rowOrder index : G413.Row alpha)
      (rowOrder index).property
    have hUpper := hHUpper (rowOrder index : G413.Row alpha)
      (rowOrder index).property
    change 0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ∧
      fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ≤ 5
    rw [hDegree]
    exact ⟨by omega, hUpper⟩
  have hLeaf : fourExceptionalMultiplicityLeafValid
      (fourActualSupportMultiplicity rowOrder) = true := by
    unfold fourExceptionalMultiplicityLeafValid
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true
      have hDegree := fourActualRowDegree_eq_card rowOrder hBRows (0 : Fin 4)
      simpa [hRowZero, hECard] using hDegree
    · rw [List.all_eq_true]
      intro row hRow
      have hRowLt : row < 4 := by
        simp at hRow
        omega
      let index : Fin 4 := ⟨row, hRowLt⟩
      have hIndexNe : index ≠ 0 := by
        intro hEq
        have : row = 0 := congrArg Fin.val hEq
        simp at hRow
        omega
      apply decide_eq_true
      change 3 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ≤ 5
      rw [fourActualRowDegree_eq_card rowOrder hBRows index]
      exact ⟨hRowsOther index hIndexNe,
        hHUpper (rowOrder index : G413.Row alpha) (rowOrder index).property⟩
  have hCertificate := fourExceptionalActualSupportMultiplicity_in_certificate
    rowOrder hHClutter hBRows hRowBounds hBCard hBPairUpper hLeaf
  obtain ⟨centerPoint, hCenterPoint⟩ : E.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < E.card)
  exact fourExceptionalActualBlocker_property rowOrder centerPoint hBRows
    hCertificate

set_option maxHeartbeats 2000000 in
-- Padding a three-row family by an isolated singleton turns its blockers into
-- the four-row objects covered by the padded certificate.
theorem threeRow_padded_blocker_property
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hHUpper : ∀ E ∈ H, E.card ≤ 5)
    (hPairUpper : (pairRows H).card ≤ 1)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBCard : (blocker H).card ≤ 5) :
    (blocker H).card = 5 ∧ ∀ P ∈ blocker H, P.card = 2 := by
  classical
  let T := padWithSingleton H
  have hHRowsOne : RowsCardAtLeast H 1 := by
    intro E hE
    exact (by have := hHRows E hE; omega)
  have hTCard : T.card = 4 := by
    have hCard : (padWithSingleton H).card = H.card + 1 :=
      padWithSingleton_card (H := H) hHRowsOne
    simpa [T, hHCard] using hCard
  have hSingletonT : ({none} : G413.Row (Option alpha)) ∈ T := by
    simp [T, padWithSingleton]
  let rowOrder := fourRowOrderAt hTCard
    ({none} : G413.Row (Option alpha)) hSingletonT
  have hRowZero :
      (rowOrder 0 : G413.Row (Option alpha)) = {none} := by
    simpa [rowOrder] using fourRowOrderAt_zero hTCard
      ({none} : G413.Row (Option alpha)) hSingletonT
  have hTClutter : IsClutter T := by
    simpa [T] using padWithSingleton_isClutter hHClutter hHRowsOne
  have hTBRowsThree : RowsCardAtLeast (blocker T) 3 := by
    simpa [T] using blocker_padWithSingleton_rows hBRows
  have hTBRows : RowsCardAtLeast (blocker T) 2 := by
    intro E hE
    exact (hTBRowsThree E hE).trans' (by omega)
  have hTMemberOther : ∀ row : Fin 4, row ≠ 0 →
      ∃ E ∈ H, (rowOrder row : G413.Row (Option alpha)) = optionImageRow E := by
    intro row hRowNe
    have hMember : (rowOrder row : G413.Row (Option alpha)) ∈ T :=
      (rowOrder row).property
    simp only [T, padWithSingleton, Finset.mem_insert] at hMember
    rcases hMember with hSingleton | hImage
    · have hIndexEq : row = 0 := rowOrder.injective
        (Subtype.ext (hSingleton.trans hRowZero.symm))
      exact (hRowNe hIndexEq).elim
    · obtain ⟨E, hEH, hEq⟩ := Finset.mem_image.mp hImage
      exact ⟨E, hEH, hEq.symm⟩
  have hRowBounds : ∀ row < 4,
      0 < fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5 := by
    intro row hRow
    let index : Fin 4 := ⟨row, hRow⟩
    have hDegree := fourActualRowDegree_eq_card rowOrder hTBRows index
    by_cases hIndexZero : index = 0
    · have hRowZeroNat : row = 0 := congrArg Fin.val hIndexZero
      subst row
      have hDegreeZero :=
        fourActualRowDegree_eq_card rowOrder hTBRows (0 : Fin 4)
      have hDegreeNat :
          fourRowDegree (fourActualSupportMultiplicity rowOrder) 0 =
            (rowOrder 0 : G413.Row (Option alpha)).card := by
        simpa using hDegreeZero
      rw [hDegreeNat, hRowZero]
      simp
    · obtain ⟨E, hEH, hEq⟩ := hTMemberOther index hIndexZero
      have hLower := hHRows E hEH
      have hUpper := hHUpper E hEH
      rw [hDegree, hEq, optionImageRow_card]
      exact ⟨by omega, hUpper⟩
  have hTBCard : (blocker T).card ≤ 5 := by
    rw [show (blocker T).card = (blocker H).card by
      simpa [T] using blocker_padWithSingleton_card H]
    exact hBCard
  have hTBPairCard : (pairRows (blocker T)).card = 0 := by
    have hEmpty := pairRows_blocker_padWithSingleton_eq_empty hBRows
    have hCard := congrArg Finset.card hEmpty
    simpa [T] using hCard
  have hTPairUpper : (pairRows T).card ≤ 1 := by
    rw [show (pairRows T).card = (pairRows H).card by
      simpa [T] using pairRows_padWithSingleton_card H]
    exact hPairUpper
  have hNoTwo {i j : Fin 4} (hij : i ≠ j)
      (hi : fourRowDegree (fourActualSupportMultiplicity rowOrder) i.val = 2)
      (hj : fourRowDegree (fourActualSupportMultiplicity rowOrder) j.val = 2) : False := by
    have hiCard := fourActualRowDegree_eq_card rowOrder hTBRows i
    have hjCard := fourActualRowDegree_eq_card rowOrder hTBRows j
    have hiPair : (rowOrder i : G413.Row (Option alpha)) ∈ pairRows T :=
      Finset.mem_filter.mpr ⟨(rowOrder i).property, by omega⟩
    have hjPair : (rowOrder j : G413.Row (Option alpha)) ∈ pairRows T :=
      Finset.mem_filter.mpr ⟨(rowOrder j).property, by omega⟩
    have hRowsEq := pairRow_eq_of_pairRows_card_le_one hTPairUpper hiPair hjPair
    exact hij (rowOrder.injective (Subtype.ext hRowsEq))
  have hZeroDegree :
      fourRowDegree (fourActualSupportMultiplicity rowOrder) 0 = 1 := by
    have hDegree := fourActualRowDegree_eq_card rowOrder hTBRows (0 : Fin 4)
    have hDegreeNat :
        fourRowDegree (fourActualSupportMultiplicity rowOrder) 0 =
          (rowOrder 0 : G413.Row (Option alpha)).card := by
      simpa using hDegree
    calc
      fourRowDegree (fourActualSupportMultiplicity rowOrder) 0 =
          (rowOrder 0 : G413.Row (Option alpha)).card := hDegreeNat
      _ = ({none} : G413.Row (Option alpha)).card :=
        congrArg Finset.card hRowZero
      _ = 1 := by simp
  have hOtherBounds : ∀ row ∈ [1, 2, 3],
      2 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5 := by
    intro row hRow
    have hRowLt : row < 4 := by simp at hRow; omega
    let index : Fin 4 := ⟨row, hRowLt⟩
    have hIndexNe : index ≠ 0 := by
      intro hEq
      have : row = 0 := congrArg Fin.val hEq
      simp at hRow
      omega
    obtain ⟨E, hEH, hEq⟩ := hTMemberOther index hIndexNe
    change 2 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ∧
      fourRowDegree (fourActualSupportMultiplicity rowOrder) index.val ≤ 5
    rw [fourActualRowDegree_eq_card rowOrder hTBRows index,
      hEq, optionImageRow_card]
    exact ⟨hHRows E hEH, hHUpper E hEH⟩
  have hOtherBoundsBool :
      ([1, 2, 3].all fun row ↦ decide
        (2 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) row ∧
          fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 5)) = true := by
    rw [List.all_eq_true]
    intro row hRow
    exact decide_eq_true (hOtherBounds row hRow)
  let d := fun row : Nat ↦
    fourRowDegree (fourActualSupportMultiplicity rowOrder) row
  have h12 : ¬(d 1 = 2 ∧ d 2 = 2) := by
    rintro ⟨h1, h2⟩
    exact hNoTwo (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide) h1 h2
  have h13 : ¬(d 1 = 2 ∧ d 3 = 2) := by
    rintro ⟨h1, h3⟩
    exact hNoTwo (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide) h1 h3
  have h23 : ¬(d 2 = 2 ∧ d 3 = 2) := by
    rintro ⟨h2, h3⟩
    exact hNoTwo (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide) h2 h3
  have hAtMostOnePairDegree :
      ([1, 2, 3].filter fun row ↦ d row = 2).length ≤ 1 := by
    by_cases h1 : d 1 = 2
    · by_cases h2 : d 2 = 2
      · exact (h12 ⟨h1, h2⟩).elim
      · by_cases h3 : d 3 = 2
        · exact (h13 ⟨h1, h3⟩).elim
        · simp [h1, h2, h3]
    · by_cases h2 : d 2 = 2
      · by_cases h3 : d 3 = 2
        · exact (h23 ⟨h2, h3⟩).elim
        · simp [h1, h2, h3]
      · by_cases h3 : d 3 = 2
        · simp [h1, h2, h3]
        · simp [h1, h2, h3]
  have hAtMostOnePairDegreeRaw :
      ([1, 2, 3].filter fun row ↦
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row = 2).length ≤ 1 := by
    exact hAtMostOnePairDegree
  have hLeaf : threePaddedMultiplicityLeafValid
      (fourActualSupportMultiplicity rowOrder) = true := by
    unfold threePaddedMultiplicityLeafValid
    rw [show decide
        (fourRowDegree (fourActualSupportMultiplicity rowOrder) 0 = 1) = true by
          exact decide_eq_true hZeroDegree,
      hOtherBoundsBool,
      show decide (([1, 2, 3].filter fun row ↦
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row = 2).length ≤ 1) = true by
          exact decide_eq_true hAtMostOnePairDegreeRaw]
    rfl
  have hCertificate := threePaddedActualSupportMultiplicity_in_certificate
    rowOrder hTClutter hTBRows hRowBounds hTBCard hTBPairCard hLeaf
  have hProperty := threePaddedActualBlocker_property rowOrder none hTBRows
    hCertificate
  constructor
  · rw [← blocker_padWithSingleton_card H]
    simpa [T] using hProperty.1
  · intro P hP
    have hLift : paddedBlockerRow P ∈ blocker T := by
      rw [show blocker T = (blocker H).image paddedBlockerRow by
        simpa [T] using blocker_padWithSingleton H]
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
    have hCard := hProperty.2 (paddedBlockerRow P) hLift
    rw [paddedBlockerRow_card] at hCard
    omega

theorem fourRow_large_blocker_card_not_le_five
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 3)
    (hHUpper : ∀ E ∈ H, E.card ≤ 5)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBCard : (blocker H).card ≤ 5)
    (hBPairUpper : (pairRows (blocker H)).card ≤ 3) : False := by
  classical
  let rowOrder := fourRowOrder hHCard
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hHClutter hBRows hHRows
    (by intro E hE; exact (hHUpper E hE).trans (by omega))
    (hBCard.trans (by omega)) (hBPairUpper.trans (by omega))
  have hWeighted := fourWeightedCoverCount_le_blocker_card rowOrder hBRows
  rcases hProfile with hEight | hSeven
  · omega
  · omega

end AiMathLab.P0054.G420
