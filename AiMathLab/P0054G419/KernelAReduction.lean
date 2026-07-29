import AiMathLab.P0054G419.KernelAActualImpossible
import AiMathLab.P0054G419.KernelC

namespace AiMathLab.P0054.G419

open G413

theorem sixTen_degreeThree_kernelA_counts {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3)
    {A B C : Row α}
    (hK : avoidPoint H x = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hPrivateA : (privatePart A B C).card = 1)
    (hPrivateB : (privatePart B A C).card = 1)
    (hPrivateC : (privatePart C A B).card = 1)
    (hSharedAB : (sharedPart A B C).card = 1)
    (hSharedAC : (sharedPart A C B).card = 1)
    (hSharedBC : (sharedPart B C A).card = 1) :
    (pairRows (blocker (avoidPoint H x))).card = 6 ∧
      (rowsCardExactly (blocker (avoidPoint H x)) 3).card = 1 ∧
      (blocker (avoidPoint H x)).card = 7 ∧
      degree (blocker H) x = 6 ∧
      (avoidPoint (blocker H) x).card = 4 ∧
      rowsCardExactly (blocker (avoidPoint H x)) 3 ⊆
        avoidPoint (blocker H) x := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hPairUpper : (pairRows (blocker K)).card ≤ 6 := by
    simpa [K] using pairRows_blocker_avoidPoint_card_le_six
      hHClutter hHCard hHRows hBRows hBCard x
  have hPairLower : 6 ≤ (pairRows (blocker K)).card := by
    have hGenerated := threePairGenerated_card_le_pairRows
      (by simpa [K] using hK)
    simpa [hPrivateA, hPrivateB, hPrivateC,
      hSharedAB, hSharedAC, hSharedBC] using hGenerated
  have hPairCard : (pairRows (blocker K)).card = 6 := by omega
  have hTripleCard : (rowsCardExactly (blocker K) 3).card = 1 := by
    rw [threeRow_triple_blockers_card
      (by simpa [K] using hK) hAB hAC hBC]
    simp [hPrivateA, hPrivateB, hPrivateC]
  have hBKCard : (blocker K).card = 7 := by
    have hCardAdd := threeRow_blocker_card_add_pair_triple hKCard hBKRows
    omega
  have hDegreeLower : 6 ≤ degree (blocker H) x := by
    have hLower := pairRows_blocker_avoidPoint_card_le_degree hBRows x
    simpa [K, hPairCard] using hLower
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  have hDualCard : (blocker (blocker H)).card = 6 := by
    rw [blocker_involution hHClutter]
    exact hHCard
  have hDegreeUpper : degree (blocker H) x ≤ 6 :=
    blockerSide_maxDegreeAtMost_six
      (blocker_isClutter H) hBCard hBRows hDualRows hDualCard x
  have hBlockerDegree : degree (blocker H) x = 6 := by omega
  have hAvoidCard : (avoidPoint (blocker H) x).card = 4 := by
    have hPartition := card_avoidPoint_add_degree (blocker H) x
    omega
  let liftedPairs := (pairRows (blocker K)).image (avoidBlockerLift H x)
  have hLiftedCard : liftedPairs.card = 6 := by
    calc
      liftedPairs.card = (pairRows (blocker K)).card := by
        change ((pairRows (blocker K)).image (avoidBlockerLift H x)).card = _
        rw [Finset.card_image_iff.mpr]
        intro T hT U hU hEq
        exact avoidBlockerLift_injective H x
          (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hU).1 hEq
      _ = 6 := hPairCard
  have hLiftedSubset :
      liftedPairs ⊆ (blocker H).filter fun E ↦ x ∈ E := by
    intro T hT
    obtain ⟨U, hUPair, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
    refine Finset.mem_filter.mpr ⟨avoidBlockerLift_mem_blocker hUBlocker, ?_⟩
    unfold avoidBlockerLift
    split
    · rename_i hTransversal
      exact (false_of_small_transversal hBRows hTransversal (by omega)).elim
    · simp
  have hPointSupportCard : ((blocker H).filter fun E ↦ x ∈ E).card = 6 := by
    simpa [degree] using hBlockerDegree
  have hLiftedEq : liftedPairs = (blocker H).filter fun E ↦ x ∈ E :=
    Finset.eq_of_subset_of_card_le hLiftedSubset (by omega)
  have hTripleSubset :
      rowsCardExactly (blocker K) 3 ⊆ avoidPoint (blocker H) x := by
    intro T hTTriple
    obtain ⟨hTBlocker, hTCard⟩ := mem_rowsCardExactly.mp hTTriple
    have hxT : x ∉ T := blocker_rows_avoid_inactive
      (fun E hE ↦ (mem_avoidPoint.mp (by simpa [K] using hE)).2) T hTBlocker
    have hLiftMember := avoidBlockerLift_mem_blocker hTBlocker
    have hLiftAvoid : x ∉ avoidBlockerLift H x T := by
      intro hxLift
      have hLiftPoint :
          avoidBlockerLift H x T ∈ (blocker H).filter fun E ↦ x ∈ E :=
        Finset.mem_filter.mpr ⟨hLiftMember, hxLift⟩
      have hLiftImage : avoidBlockerLift H x T ∈ liftedPairs := by
        rw [hLiftedEq]
        exact hLiftPoint
      obtain ⟨U, hUPair, hULift⟩ := Finset.mem_image.mp hLiftImage
      obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
      have hUT : U = T :=
        avoidBlockerLift_injective H x hUBlocker hTBlocker hULift
      rw [hUT] at hUCard
      omega
    by_cases hTransversal : IsTransversal H T
    · have hTH : T ∈ blocker H := by
        simpa [avoidBlockerLift, hTransversal] using hLiftMember
      exact mem_avoidPoint.mpr ⟨hTH, hxT⟩
    · have hxLift : x ∈ avoidBlockerLift H x T := by
        simp [avoidBlockerLift, hTransversal]
      exact (hLiftAvoid hxLift).elim
  exact ⟨by simpa [K] using hPairCard,
    by simpa [K] using hTripleCard,
    by simpa [K] using hBKCard,
    hBlockerDegree, hAvoidCard, by simpa [K] using hTripleSubset⟩

theorem sixTen_degreeThree_kernelA_impossible_explicit {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3)
    {A B C : Row α}
    (hK : avoidPoint H x = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hPrivateA : (privatePart A B C).card = 1)
    (hPrivateB : (privatePart B A C).card = 1)
    (hPrivateC : (privatePart C A B).card = 1)
    (hSharedAB : (sharedPart A B C).card = 1)
    (hSharedAC : (sharedPart A C B).card = 1)
    (hSharedBC : (sharedPart B C A).card = 1) : False := by
  classical
  let K := avoidPoint H x
  let T := avoidPoint (blocker H) x
  obtain ⟨hPairCard, hTripleCard, hBKCard, hBlockerDegree,
      hTCard, hTripleSubset⟩ :=
    sixTen_degreeThree_kernelA_counts
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC hPrivateA hPrivateB hPrivateC
      hSharedAB hSharedAC hSharedBC
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hNoCommon : ∀ y, ¬(y ∈ A ∧ y ∈ B ∧ y ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two
      (by simpa [K] using hK) hBKRows
  obtain ⟨a, hPA⟩ := Finset.card_eq_one.mp hPrivateA
  obtain ⟨b, hPB⟩ := Finset.card_eq_one.mp hPrivateB
  obtain ⟨c, hPC⟩ := Finset.card_eq_one.mp hPrivateC
  obtain ⟨u, hX⟩ := Finset.card_eq_one.mp hSharedAB
  obtain ⟨v, hY⟩ := Finset.card_eq_one.mp hSharedAC
  obtain ⟨w, hZ⟩ := Finset.card_eq_one.mp hSharedBC
  have haP : a ∈ privatePart A B C := by rw [hPA]; simp
  have hbP : b ∈ privatePart B A C := by rw [hPB]; simp
  have hcP : c ∈ privatePart C A B := by rw [hPC]; simp
  have huX : u ∈ sharedPart A B C := by rw [hX]; simp
  have hvY : v ∈ sharedPart A C B := by rw [hY]; simp
  have hwZ : w ∈ sharedPart B C A := by rw [hZ]; simp
  have haMask := threeSupportMask_privatePart_first haP
  have hbMask := threeSupportMask_privatePart_second hbP
  have hcMask := threeSupportMask_privatePart_third hcP
  have huMask := threeSupportMask_sharedPart_twelve huX
  have hvMask := threeSupportMask_sharedPart_thirteen hvY
  have hwMask := threeSupportMask_sharedPart_twentyThree hwZ
  have support_ne_of_mask_ne {p q : α} {i j : Nat}
      (hp : threeSupportMask A B C p = i)
      (hq : threeSupportMask A B C q = j) (hij : i ≠ j) : p ≠ q := by
    intro hpq
    subst q
    omega
  have hab : a ≠ b := support_ne_of_mask_ne haMask hbMask (by omega)
  have hac : a ≠ c := support_ne_of_mask_ne haMask hcMask (by omega)
  have hbc : b ≠ c := support_ne_of_mask_ne hbMask hcMask (by omega)
  have hua : u ≠ a := support_ne_of_mask_ne huMask haMask (by omega)
  have hub : u ≠ b := support_ne_of_mask_ne huMask hbMask (by omega)
  have huc : u ≠ c := support_ne_of_mask_ne huMask hcMask (by omega)
  have hva : v ≠ a := support_ne_of_mask_ne hvMask haMask (by omega)
  have hvb : v ≠ b := support_ne_of_mask_ne hvMask hbMask (by omega)
  have hvc : v ≠ c := support_ne_of_mask_ne hvMask hcMask (by omega)
  have hwa : w ≠ a := support_ne_of_mask_ne hwMask haMask (by omega)
  have hwb : w ≠ b := support_ne_of_mask_ne hwMask hbMask (by omega)
  have hwc : w ≠ c := support_ne_of_mask_ne hwMask hcMask (by omega)
  have huv : u ≠ v := support_ne_of_mask_ne huMask hvMask (by omega)
  have huw : u ≠ w := support_ne_of_mask_ne huMask hwMask (by omega)
  have hvw : v ≠ w := support_ne_of_mask_ne hvMask hwMask (by omega)
  have hAForm : A = {a, u, v} := by
    rw [threeRows_first_partition hNoCommon, hPA, hX, hY]
    simp
  have hBForm : B = {b, u, w} := by
    rw [threeRows_second_partition hNoCommon, hPB, hX, hZ]
    simp
  have hCForm : C = {c, v, w} := by
    rw [threeRows_third_partition hNoCommon, hPC, hY, hZ]
    simp
  have hTripleExact :
      ({a, b, c} : Row α) ∈ rowsCardExactly (blocker K) 3 := by
    rw [threeRow_triple_blockers (by simpa [K] using hK) hAB hAC hBC]
    exact mem_tripleChoiceRows.mpr ⟨a, haP, b, hbP, c, hcP, rfl⟩
  have hTripleT : ({a, b, c} : Row α) ∈ T := by
    exact hTripleSubset hTripleExact
  have hTClutter : IsClutter T := by
    simpa [T] using avoidPoint_isClutter (blocker_isClutter H) x
  have hTRows : RowsCardAtLeast T 3 := by
    intro E hET
    exact hBRows E (mem_avoidPoint.mp (by simpa [T] using hET)).1
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  have hBlockerTRows : RowsCardAtLeast (blocker T) 2 := by
    simpa [T] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
  have hTUpper : ∀ E ∈ T, E.card ≤ 6 := by
    intro E hET
    have hEBlocker : E ∈ blocker H :=
      (mem_avoidPoint.mp (by simpa [T] using hET)).1
    exact (minimalTransversal_card_le_rows (mem_blocker.mp hEBlocker)).trans_eq hHCard
  have hThree : ∃ E ∈ T, E.card = 3 := by
    refine ⟨{a, b, c}, hTripleT, ?_⟩
    simp [hab, hac, hbc]
  have hBlockerT : blocker T = residual H x := by
    calc
      blocker T = blocker (avoidPoint (blocker H) x) := by rfl
      _ = residual (blocker (blocker H)) x :=
        blocker_avoidPoint (blocker_isClutter H) x
      _ = residual H x := by rw [blocker_involution hHClutter]
  have hBlockerTUpper : (blocker T).card ≤ 6 := by
    rw [hBlockerT]
    exact (residual_card_le H x).trans_eq hHCard
  let rowOrder := fourRowOrder (by simpa [T] using hTCard)
  have hWeightedLower :
      5 ≤ fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) :=
    fourActualSupportMultiplicity_weightedCoverCount_ge_five rowOrder
      hTClutter hBlockerTRows hTRows hTUpper hThree hBlockerTUpper
  have hBlockerTLower : 5 ≤ (blocker T).card :=
    hWeightedLower.trans
      (fourWeightedCoverCount_le_blocker_card rowOrder hBlockerTRows)
  have hAK : A ∈ K := by simpa [K, hK]
  have hBK : B ∈ K := by simpa [K, hK]
  have hCK : C ∈ K := by simpa [K, hK]
  have hAH : A ∈ H := (mem_avoidPoint.mp (by simpa [K] using hAK)).1
  have hBH : B ∈ H := (mem_avoidPoint.mp (by simpa [K] using hBK)).1
  have hCH : C ∈ H := (mem_avoidPoint.mp (by simpa [K] using hCK)).1
  have hxA : x ∉ A := (mem_avoidPoint.mp (by simpa [K] using hAK)).2
  have hxB : x ∉ B := (mem_avoidPoint.mp (by simpa [K] using hBK)).2
  have hxC : x ∉ C := (mem_avoidPoint.mp (by simpa [K] using hCK)).2
  let deleted := deletePoint H x
  let extra := ((deleted.erase A).erase B).erase C
  have hADeleted : A ∈ deleted :=
    Finset.mem_image.mpr ⟨A, hAH, by simp [hxA]⟩
  have hBDeleted : B ∈ deleted :=
    Finset.mem_image.mpr ⟨B, hBH, by simp [hxB]⟩
  have hCDeleted : C ∈ deleted :=
    Finset.mem_image.mpr ⟨C, hCH, by simp [hxC]⟩
  have hBEraseA : B ∈ deleted.erase A :=
    Finset.mem_erase.mpr ⟨hAB.symm, hBDeleted⟩
  have hCEraseAB : C ∈ (deleted.erase A).erase B :=
    Finset.mem_erase.mpr ⟨hBC.symm,
      Finset.mem_erase.mpr ⟨hAC.symm, hCDeleted⟩⟩
  have hDeletedCard : deleted.card ≤ 6 := by
    simpa [deleted, deletePoint, hHCard] using
      (Finset.card_image_le (f := fun E : Row α ↦ E.erase x) (s := H))
  have hExtraCard : extra.card ≤ 3 := by
    change (((deleted.erase A).erase B).erase C).card ≤ 3
    rw [Finset.card_erase_of_mem hCEraseAB,
      Finset.card_erase_of_mem hBEraseA,
      Finset.card_erase_of_mem hADeleted]
    omega
  have hResidualSubset : blocker T ⊆ deleted := by
    rw [hBlockerT]
    exact minimize_subset deleted
  have hBlockerSubset : blocker T ⊆ insert A (insert B (insert C extra)) := by
    intro E hET
    have hEDeleted := hResidualSubset hET
    by_cases hEA : E = A
    · simp [hEA]
    by_cases hEB : E = B
    · simp [hEB]
    by_cases hEC : E = C
    · simp [hEC]
    simp only [Finset.mem_insert]
    right; right; right
    exact Finset.mem_erase.mpr ⟨hEC,
      Finset.mem_erase.mpr ⟨hEB, Finset.mem_erase.mpr ⟨hEA, hEDeleted⟩⟩⟩
  let D₁ : Row α := {a, u, v}
  let D₂ : Row α := {b, u, w}
  let D₃ : Row α := {c, v, w}
  let D : G413.Hypergraph α := {D₁, D₂, D₃}
  let R := blocker T
  have hD₁D₂ : D₁ ≠ D₂ := by
    intro h
    apply hAB
    exact hAForm.trans (h.trans hBForm.symm)
  have hD₁D₃ : D₁ ≠ D₃ := by
    intro h
    apply hAC
    exact hAForm.trans (h.trans hCForm.symm)
  have hD₂D₃ : D₂ ≠ D₃ := by
    intro h
    apply hBC
    exact hBForm.trans (h.trans hCForm.symm)
  have hBlockerSubset' : R ⊆ insert D₁ (insert D₂ (insert D₃ extra)) := by
    simpa [R, D₁, D₂, D₃, hAForm, hBForm, hCForm] using hBlockerSubset
  have hRetainedSubset : R ⊆ (R ∩ D) ∪ extra := by
    intro E hER
    have hCases := hBlockerSubset' hER
    simp only [Finset.mem_insert] at hCases
    rcases hCases with hED₁ | hED₂ | hED₃ | hEExtra
    · subst E
      exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hER, by simp [D, D₁]⟩)
    · subst E
      exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hER, by simp [D, D₂]⟩)
    · subst E
      exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hER, by simp [D, D₃]⟩)
    · exact Finset.mem_union_right _ hEExtra
  have hRetainedLower : 2 ≤ (R ∩ D).card := by
    have hSubsetCard := Finset.card_le_card hRetainedSubset
    have hUnionCard := Finset.card_union_le (R ∩ D) extra
    have hRLower : 5 ≤ R.card := by simpa [R] using hBlockerTLower
    omega
  have hRetainedCard :
      (R ∩ D).card =
        (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
          (if D₃ ∈ R then 1 else 0) :=
    inter_three_card_eq_indicator_sum R D₁ D₂ D₃ hD₁D₂ hD₁D₃ hD₂D₃
  have hD₁orD₂ : D₁ ∈ R ∨ D₂ ∈ R := by
    by_contra h
    simp only [not_or] at h
    by_cases hD₃ : D₃ ∈ R
    · rw [hRetainedCard] at hRetainedLower
      simp [h.1, h.2, hD₃] at hRetainedLower
    · rw [hRetainedCard] at hRetainedLower
      simp [h.1, h.2, hD₃] at hRetainedLower
  have hD₁orD₃ : D₁ ∈ R ∨ D₃ ∈ R := by
    by_contra h
    simp only [not_or] at h
    by_cases hD₂ : D₂ ∈ R
    · rw [hRetainedCard] at hRetainedLower
      simp [h.1, hD₂, h.2] at hRetainedLower
    · rw [hRetainedCard] at hRetainedLower
      simp [h.1, hD₂, h.2] at hRetainedLower
  have hD₂orD₃ : D₂ ∈ R ∨ D₃ ∈ R := by
    by_contra h
    simp only [not_or] at h
    by_cases hD₁ : D₁ ∈ R
    · rw [hRetainedCard] at hRetainedLower
      simp [hD₁, h.1, h.2] at hRetainedLower
    · rw [hRetainedCard] at hRetainedLower
      simp [hD₁, h.1, h.2] at hRetainedLower
  have active_of_blocker_row {E : Row α} (hER : E ∈ R)
      {y : α} (hyE : y ∈ E) : y ∈ fourActiveUniverse T := by
    have hEMinimal : E ∈ blocker T := by simpa [R] using hER
    obtain ⟨F, hPrivate⟩ := (mem_blocker.mp hEMinimal).exists_privateRow hyE
    exact mem_fourActiveUniverse.mpr
      ⟨F, hPrivate.1, hPrivate.2.2.1⟩
  have huActive : u ∈ fourActiveUniverse T := by
    rcases hD₁orD₂ with hD₁ | hD₂
    · exact active_of_blocker_row hD₁ (by simp [D₁])
    · exact active_of_blocker_row hD₂ (by simp [D₂])
  have hvActive : v ∈ fourActiveUniverse T := by
    rcases hD₁orD₃ with hD₁ | hD₃
    · exact active_of_blocker_row hD₁ (by simp [D₁])
    · exact active_of_blocker_row hD₃ (by simp [D₃])
  have hwActive : w ∈ fourActiveUniverse T := by
    rcases hD₂orD₃ with hD₂ | hD₃
    · exact active_of_blocker_row hD₂ (by simp [D₂])
    · exact active_of_blocker_row hD₃ (by simp [D₃])
  have huTriple : u ∉ ({a, b, c} : Row α) := by simp [hua, hub, huc]
  have hvTriple : v ∉ ({a, b, c} : Row α) := by simp [hva, hvb, hvc]
  have hwTriple : w ∉ ({a, b, c} : Row α) := by simp [hwa, hwb, hwc]
  have hCompatible :
      fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = true :=
    fourKernelCompatibleExact_actual_of_budget rowOrder hBlockerTRows
      hTripleT rfl hab hac hbc huTriple hvTriple hwTriple huv huw hvw
      huActive hvActive hwActive hD₁D₂ hD₁D₃ hD₂D₃ extra
      (by simpa [R, D₁, D₂, D₃] using hBlockerSubset') hExtraCard
  exact fourKernelA_actual_impossible rowOrder
    hTClutter hBlockerTRows hTRows hTUpper hThree hBlockerTUpper hCompatible

def IsKernelAProfile
    (p q r x12 x13 x23 : Nat) : Prop :=
  p = 1 ∧ q = 1 ∧ r = 1 ∧ x12 = 1 ∧ x13 = 1 ∧ x23 = 1

theorem sixTen_degreeThree_kernelA_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3)
    {A B C : Row α}
    (hK : avoidPoint H x = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hProfile : IsKernelAProfile
      (privatePart A B C).card
      (privatePart B A C).card
      (privatePart C A B).card
      (sharedPart A B C).card
      (sharedPart A C B).card
      (sharedPart B C A).card) : False := by
  exact sixTen_degreeThree_kernelA_impossible_explicit
    hHClutter hHCard hHRows hBRows hBCard hDegree hK hAB hAC hBC
    hProfile.1 hProfile.2.1 hProfile.2.2.1 hProfile.2.2.2.1
    hProfile.2.2.2.2.1 hProfile.2.2.2.2.2

end AiMathLab.P0054.G419
