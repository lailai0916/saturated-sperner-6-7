import AiMathLab.P0054G419.KernelProfile

namespace AiMathLab.P0054.G419

open G413

theorem threeRow_blocker_card_add_pair_triple {α : Type*}
    [Fintype α]
    {K : G413.Hypergraph α}
    (hKCard : K.card = 3)
    (hBRows : RowsCardAtLeast (blocker K) 2) :
    (pairRows (blocker K)).card +
        (rowsCardExactly (blocker K) 3).card =
      (blocker K).card := by
  classical
  have hPartition :
      pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3 = blocker K := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_union.mp hE with hPair | hTriple
      · exact (Finset.mem_filter.mp hPair).1
      · exact (mem_rowsCardExactly.mp hTriple).1
    · intro hE
      have hLower := hBRows E hE
      have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hE)
      have hCases : E.card = 2 ∨ E.card = 3 := by omega
      rcases hCases with hCard | hCard
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE, hCard⟩)
      · exact Finset.mem_union_right _ (mem_rowsCardExactly.mpr ⟨hE, hCard⟩)
  have hDisjoint :
      Disjoint (pairRows (blocker K)) (rowsCardExactly (blocker K) 3) := by
    apply Finset.disjoint_left.mpr
    intro E hPair hTriple
    have hTwo := (Finset.mem_filter.mp hPair).2
    have hThree := (mem_rowsCardExactly.mp hTriple).2
    omega
  calc
    (pairRows (blocker K)).card +
          (rowsCardExactly (blocker K) 3).card =
        (pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3).card :=
      (Finset.card_union_of_disjoint hDisjoint).symm
    _ = (blocker K).card := congrArg Finset.card hPartition

theorem sixTen_degreeThree_kernelC_counts {α : Type*}
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
    (hPairExpression :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card = 6)
    (hPrivateProduct :
      (privatePart A B C).card *
          (privatePart B A C).card *
          (privatePart C A B).card = 3) :
    (pairRows (blocker (avoidPoint H x))).card = 6 ∧
      (rowsCardExactly (blocker (avoidPoint H x)) 3).card = 3 ∧
      (blocker (avoidPoint H x)).card = 9 ∧
      degree (blocker H) x = 6 ∧
      (avoidPoint (blocker H) x).card = 4 ∧
      rowsCardExactly (blocker (avoidPoint H x)) 3 ⊆
        avoidPoint (blocker H) x := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hPairUpper : (pairRows (blocker K)).card ≤ 6 := by
    simpa [K] using pairRows_blocker_avoidPoint_card_le_six
      hHClutter hHCard hHRows hBRows hBCard x
  have hPairLower : 6 ≤ (pairRows (blocker K)).card := by
    calc
      6 =
          (sharedPart A B C).card * (sharedPart A C B).card +
            (sharedPart A B C).card * (sharedPart B C A).card +
            (sharedPart A C B).card * (sharedPart B C A).card +
            (sharedPart A B C).card * (privatePart C A B).card +
            (sharedPart A C B).card * (privatePart B A C).card +
            (sharedPart B C A).card * (privatePart A B C).card :=
        hPairExpression.symm
      _ ≤ (pairRows (blocker K)).card := by
        exact threePairGenerated_card_le_pairRows (by simpa [K] using hK)
  have hPairCard : (pairRows (blocker K)).card = 6 := by omega
  have hTripleCard : (rowsCardExactly (blocker K) 3).card = 3 := by
    calc
      (rowsCardExactly (blocker K) 3).card =
          (privatePart A B C).card *
            (privatePart B A C).card *
            (privatePart C A B).card :=
        threeRow_triple_blockers_card (by simpa [K] using hK) hAB hAC hBC
      _ = 3 := hPrivateProduct
  have hBKCard : (blocker K).card = 9 := by
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

end AiMathLab.P0054.G419
