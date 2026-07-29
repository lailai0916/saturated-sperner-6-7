import AiMathLab.P0054G420.DegreeBounds

namespace AiMathLab.P0054.G420

open G413 G419
open scoped BigOperators

set_option maxRecDepth 100000 in
theorem four_minimal_support_pair_covers_nodup :
    (fourMinimalSupportIndexCovers.take 25).Nodup := by
  exact four_minimal_support_index_covers_nodup.take

set_option maxRecDepth 100000 in
theorem four_minimal_support_pair_covers_length :
    ∀ C ∈ fourMinimalSupportIndexCovers.take 25, C.length = 2 := by
  decide

set_option maxRecDepth 100000 in
theorem four_minimal_support_pair_covers_values :
    ((fourMinimalSupportIndexCovers.take 25).map fun C ↦
      C.map fun s ↦ s.val) = fourMinimalSupportCovers.take 25 := by
  have h := congrArg (List.take 25) four_minimal_support_index_covers_values
  simpa only [List.map_take] using h

set_option maxRecDepth 100000 in
theorem four_minimal_support_pair_cover_codes_supports :
    (fourMinimalSupportCoverCodes.take 25).map fourCoverCodeSupports =
      fourMinimalSupportCovers.take 25 := by
  decide

theorem four_pair_cover_count_eq_index_covers (m : FourMultiplicity) :
    ((fourMinimalSupportIndexCovers.take 25).map fun C ↦
      (C.map fun s ↦ fourMultiplicityDigit m s.val).prod).sum =
        fourPairCoverCount m := by
  calc
    ((fourMinimalSupportIndexCovers.take 25).map fun C ↦
        (C.map fun s ↦ fourMultiplicityDigit m s.val).prod).sum =
        (((fourMinimalSupportIndexCovers.take 25).map fun C ↦
          C.map fun s ↦ s.val).map fun C ↦
            (C.map (fourMultiplicityDigit m)).prod).sum := by
      simp only [List.map_map, Function.comp_def]
    _ = ((fourMinimalSupportCovers.take 25).map fun C ↦
          (C.map (fourMultiplicityDigit m)).prod).sum := by
      rw [four_minimal_support_pair_covers_values]
    _ = (((fourMinimalSupportCoverCodes.take 25).map fourCoverCodeSupports).map
          fun C ↦ (C.map (fourMultiplicityDigit m)).prod).sum := by
      rw [four_minimal_support_pair_cover_codes_supports]
    _ = ((fourMinimalSupportCoverCodes.take 25).map
          (fourCoverCodeValue m)).sum := by
      simp only [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro code _hcode
      exact four_cover_code_value_eq_support_product m code
    _ = fourPairCoverCount m := rfl

noncomputable def fourActualPairChoices {alpha : Type*} [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    Finset (Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, alpha) := by
  classical
  exact (fourMinimalSupportIndexCovers.take 25).toFinset.sigma fun C ↦
    C.toFinset.pi fun s ↦ fourSupportFiber rowOrder s

theorem fourActualPairChoices_card {alpha : Type*} [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    (fourActualPairChoices rowOrder).card =
      fourPairCoverCount (fourActualSupportMultiplicity rowOrder) := by
  classical
  unfold fourActualPairChoices
  rw [Finset.card_sigma]
  rw [List.sum_toFinset _ four_minimal_support_pair_covers_nodup]
  rw [← four_pair_cover_count_eq_index_covers]
  apply congrArg List.sum
  apply List.map_congr_left
  intro C hC
  rw [Finset.card_pi]
  rw [List.prod_toFinset _
    ((four_minimal_support_index_covers_each_sorted C
      (List.mem_of_mem_take hC)).nodup)]
  apply congrArg List.prod
  apply List.map_congr_left
  intro s _hs
  exact (fourMultiplicityDigit_actualSupportMultiplicity rowOrder s).symm

theorem fourActualPairChoices_subset {alpha : Type*} [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    fourActualPairChoices rowOrder ⊆ fourActualChoices rowOrder := by
  classical
  intro q hq
  obtain ⟨hCover, hPi⟩ := Finset.mem_sigma.mp hq
  apply Finset.mem_sigma.mpr
  exact ⟨List.mem_toFinset.mpr (List.mem_of_mem_take
    (List.mem_toFinset.mp hCover)), hPi⟩

theorem fourPairChoiceRow_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha] {T : G413.Hypergraph alpha}
    (rowOrder : Fin 4 ≃ T)
    {q : Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, alpha}
    (hq : q ∈ fourActualPairChoices rowOrder) :
    (fourChoiceRow q).card = 2 := by
  classical
  have hqAll := fourActualPairChoices_subset rowOrder hq
  have hLength : q.1.length = 2 :=
    four_minimal_support_pair_covers_length q.1
      (List.mem_toFinset.mp (Finset.mem_sigma.mp hq).1)
  have hNodup := (four_minimal_support_index_covers_each_sorted q.1
    (List.mem_toFinset.mp (Finset.mem_sigma.mp hqAll).1)).nodup
  have hImageCard :
      ((fourChoiceRow q).image (fourActualSupportIndex rowOrder)).card = 2 := by
    rw [fourChoiceRow_supportIndices rowOrder hqAll]
    simpa [List.toFinset_card_of_nodup hNodup] using hLength
  have hLower := Finset.card_image_le (s := fourChoiceRow q)
    (f := fourActualSupportIndex rowOrder)
  have hUpper : (fourChoiceRow q).card ≤ q.1.toFinset.card := by
    calc
      (fourChoiceRow q).card =
          (q.1.toFinset.attach.image fun s : q.1.toFinset ↦ q.2 s.1 s.2).card := rfl
      _ ≤ q.1.toFinset.attach.card := Finset.card_image_le
      _ = q.1.toFinset.card := Finset.card_attach
  rw [List.toFinset_card_of_nodup hNodup, hLength] at hUpper
  omega

theorem fourPairCoverCount_le_pairRows_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha] {T : G413.Hypergraph alpha}
    (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    fourPairCoverCount (fourActualSupportMultiplicity rowOrder) ≤
      (pairRows (blocker T)).card := by
  classical
  have hImageSubset :
      (fourActualPairChoices rowOrder).image fourChoiceRow ⊆
        pairRows (blocker T) := by
    intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.mem_filter.mpr
      ⟨fourChoiceRow_mem_blocker rowOrder hBRows
        (fourActualPairChoices_subset rowOrder hq),
      fourPairChoiceRow_card rowOrder hq⟩
  calc
    fourPairCoverCount (fourActualSupportMultiplicity rowOrder) =
        (fourActualPairChoices rowOrder).card :=
      (fourActualPairChoices_card rowOrder).symm
    _ = ((fourActualPairChoices rowOrder).image fourChoiceRow).card := by
      rw [Finset.card_image_iff.mpr]
      exact (fourChoiceRow_injective rowOrder).mono
        (fourActualPairChoices_subset rowOrder)
    _ ≤ (pairRows (blocker T)).card := Finset.card_le_card hImageSubset

end AiMathLab.P0054.G420
