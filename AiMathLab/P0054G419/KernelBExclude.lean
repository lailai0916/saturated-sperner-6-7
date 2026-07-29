import AiMathLab.P0054G419.KernelBGrid

namespace AiMathLab.P0054.G419

open G413

theorem sixTen_degreeThree_kernelB_impossible_explicit {α : Type*}
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
    (hPrivateB : (privatePart B A C).card = 2)
    (hPrivateC : (privatePart C A B).card = 2)
    (hSharedAB : (sharedPart A B C).card = 1)
    (hSharedAC : (sharedPart A C B).card = 1)
    (hSharedBC : (sharedPart B C A).card = 0) : False := by
  classical
  let K := avoidPoint H x
  let PA := privatePart A B C
  let PB := privatePart B A C
  let PC := privatePart C A B
  let pairFamily := pairRows (blocker K)
  let tripleFamily := rowsCardExactly (blocker K) 3
  let T := avoidPoint (blocker H) x
  let F := tripleFamily ∩ T
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hPairLower : 5 ≤ pairFamily.card := by
    have hGenerated := threePairGenerated_card_le_pairRows (by simpa [K] using hK)
    simpa [pairFamily, hPrivateA, hPrivateB, hPrivateC,
      hSharedAB, hSharedAC, hSharedBC] using hGenerated
  have hTripleCard : tripleFamily.card = 4 := by
    change (rowsCardExactly (blocker K) 3).card = 4
    rw [threeRow_triple_blockers_card (by simpa [K] using hK) hAB hAC hBC]
    simp [hPrivateA, hPrivateB, hPrivateC]
  have hTripleForm : tripleFamily = tripleChoiceRows PA PB PC := by
    change rowsCardExactly (blocker K) 3 = tripleChoiceRows PA PB PC
    simpa [PA, PB, PC] using
      threeRow_triple_blockers (by simpa [K] using hK) hAB hAC hBC
  have hBKCardUpper : (blocker K).card ≤ 10 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  have hPairTripleCard := threeRow_blocker_card_add_pair_triple hKCard hBKRows
  have hPairUpper : pairFamily.card ≤ 6 := by
    change pairFamily.card + tripleFamily.card = (blocker K).card at hPairTripleCard
    omega
  let liftedPairs := pairFamily.image (avoidBlockerLift H x)
  have hLiftedPairsCard : liftedPairs.card = pairFamily.card := by
    change (pairFamily.image (avoidBlockerLift H x)).card = pairFamily.card
    rw [Finset.card_image_iff.mpr]
    intro U hU V hV hEq
    exact avoidBlockerLift_injective H x
      (Finset.mem_filter.mp hU).1 (Finset.mem_filter.mp hV).1 hEq
  have hLiftedPairsSubset :
      liftedPairs ⊆ (blocker H).filter fun E ↦ x ∈ E := by
    intro E hE
    obtain ⟨U, hUPair, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
    refine Finset.mem_filter.mpr ⟨avoidBlockerLift_mem_blocker hUBlocker, ?_⟩
    unfold avoidBlockerLift
    split
    · rename_i hTransversal
      exact (false_of_small_transversal hBRows hTransversal (by omega)).elim
    · simp
  let badTriples := tripleFamily.filter fun U ↦ x ∈ avoidBlockerLift H x U
  let liftedBadTriples := badTriples.image (avoidBlockerLift H x)
  have hLiftedBadCard : liftedBadTriples.card = badTriples.card := by
    change (badTriples.image (avoidBlockerLift H x)).card = badTriples.card
    rw [Finset.card_image_iff.mpr]
    intro U hU V hV hEq
    exact avoidBlockerLift_injective H x
      (mem_rowsCardExactly.mp (Finset.mem_filter.mp hU).1).1
      (mem_rowsCardExactly.mp (Finset.mem_filter.mp hV).1).1 hEq
  have hLiftedBadSubset :
      liftedBadTriples ⊆ (blocker H).filter fun E ↦ x ∈ E := by
    intro E hE
    obtain ⟨U, hUBad, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hUTriple, hxLift⟩ := Finset.mem_filter.mp hUBad
    exact Finset.mem_filter.mpr
      ⟨avoidBlockerLift_mem_blocker (mem_rowsCardExactly.mp hUTriple).1, hxLift⟩
  have hLiftedDisjoint : Disjoint liftedPairs liftedBadTriples := by
    apply Finset.disjoint_left.mpr
    intro E hEPair hEBad
    obtain ⟨U, hUPair, hULift⟩ := Finset.mem_image.mp hEPair
    obtain ⟨V, hVBad, hVLift⟩ := Finset.mem_image.mp hEBad
    have hUV : U = V := avoidBlockerLift_injective H x
      (Finset.mem_filter.mp hUPair).1
      (mem_rowsCardExactly.mp (Finset.mem_filter.mp hVBad).1).1
      (hULift.trans hVLift.symm)
    have hUCard := (Finset.mem_filter.mp hUPair).2
    have hVCard := (mem_rowsCardExactly.mp (Finset.mem_filter.mp hVBad).1).2
    rw [hUV] at hUCard
    omega
  have hPointRowsCard :
      ((blocker H).filter fun E ↦ x ∈ E).card ≤ 6 := by
    change degree (blocker H) x ≤ 6
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      rw [blocker_involution hHClutter]
      exact hHRows
    have hDualCard : (blocker (blocker H)).card = 6 := by
      rw [blocker_involution hHClutter]
      exact hHCard
    exact blockerSide_maxDegreeAtMost_six
      (blocker_isClutter H) hBCard hBRows hDualRows hDualCard x
  have hBadBudget : pairFamily.card + badTriples.card ≤ 6 := by
    calc
      pairFamily.card + badTriples.card =
          liftedPairs.card + liftedBadTriples.card := by
        rw [hLiftedPairsCard, hLiftedBadCard]
      _ = (liftedPairs ∪ liftedBadTriples).card :=
        (Finset.card_union_of_disjoint hLiftedDisjoint).symm
      _ ≤ ((blocker H).filter fun E ↦ x ∈ E).card := by
        apply Finset.card_le_card
        intro E hE
        rcases Finset.mem_union.mp hE with hEPair | hEBad
        · exact hLiftedPairsSubset hEPair
        · exact hLiftedBadSubset hEBad
      _ ≤ 6 := hPointRowsCard
  let goodTriples := tripleFamily.filter fun U ↦ x ∉ avoidBlockerLift H x U
  have hGoodBadCard : goodTriples.card + badTriples.card = tripleFamily.card := by
    simpa [goodTriples, badTriples] using
      (Finset.card_filter_add_card_filter_not
        (s := tripleFamily) fun U ↦ x ∉ avoidBlockerLift H x U)
  have hGoodSubsetF : goodTriples ⊆ F := by
    intro U hUGood
    obtain ⟨hUTriple, hxLift⟩ := Finset.mem_filter.mp hUGood
    have hUBlocker := (mem_rowsCardExactly.mp hUTriple).1
    have hxU := blocker_avoidPoint_avoids H x hUBlocker
    have hUTransversal : IsTransversal H U := by
      by_contra hUTransversal
      apply hxLift
      simp [avoidBlockerLift, hUTransversal]
    have hLiftEq : avoidBlockerLift H x U = U := by
      simp [avoidBlockerLift, hUTransversal]
    have hUH : U ∈ blocker H := by
      simpa [hLiftEq] using avoidBlockerLift_mem_blocker hUBlocker
    exact Finset.mem_inter.mpr
      ⟨hUTriple, by simpa [T] using mem_avoidPoint.mpr ⟨hUH, hxU⟩⟩
  have hFCardLower : 3 ≤ F.card := by
    have hGoodLower : 3 ≤ goodTriples.card := by
      rw [hTripleCard] at hGoodBadCard
      omega
    exact hGoodLower.trans (Finset.card_le_card hGoodSubsetF)
  have hPointRowsLower :
      pairFamily.card + badTriples.card ≤ degree (blocker H) x := by
    change pairFamily.card + badTriples.card ≤
      ((blocker H).filter fun E ↦ x ∈ E).card
    calc
      pairFamily.card + badTriples.card =
          (liftedPairs ∪ liftedBadTriples).card := by
        rw [Finset.card_union_of_disjoint hLiftedDisjoint,
          hLiftedPairsCard, hLiftedBadCard]
      _ ≤ ((blocker H).filter fun E ↦ x ∈ E).card := by
        apply Finset.card_le_card
        intro E hE
        rcases Finset.mem_union.mp hE with hEPair | hEBad
        · exact hLiftedPairsSubset hEPair
        · exact hLiftedBadSubset hEBad
  have hTCardUpper : T.card ≤ F.card + 1 := by
    have hTPartition := card_avoidPoint_add_degree (blocker H) x
    have hGoodUpper : goodTriples.card ≤ F.card := Finset.card_le_card hGoodSubsetF
    rw [hBCard] at hTPartition
    rw [hTripleCard] at hGoodBadCard
    change (avoidPoint (blocker H) x).card ≤ F.card + 1
    omega
  have hFSubsetT : F ⊆ T := Finset.inter_subset_right
  have hFStrict : F ⊂ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hFSubsetT, ?_⟩
    intro hFT
    obtain ⟨a, hPARaw⟩ := Finset.card_eq_one.mp (by simpa [PA] using hPrivateA)
    have hPA : PA = {a} := by simpa [PA] using hPARaw
    have hAllA : ∀ E ∈ F, a ∈ E := by
      refine tripleChoiceRows_all_first
        (A := PA) (B := PB) (C := PC) hPA ?_
      intro E hEF
      have hETriple := Finset.mem_inter.mp hEF |>.1
      rw [hTripleForm] at hETriple
      exact hETriple
    have hSingleton : IsTransversal T {a} := by
      intro E hET
      have hEF : E ∈ F := by rw [hFT]; exact hET
      exact ⟨a, by simp, hAllA E hEF⟩
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      rw [blocker_involution hHClutter]
      exact hHRows
    have hBlockerTRows : RowsCardAtLeast (blocker T) 2 := by
      simpa [T] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
    exact false_of_small_transversal hBlockerTRows hSingleton (by simp)
  obtain ⟨Q, hQT, hQNotF⟩ := Finset.exists_of_ssubset hFStrict
  have hTForm : T = insert Q F := by
    have hInsertSubset : insert Q F ⊆ T := by
      intro E hE
      simp only [Finset.mem_insert] at hE
      rcases hE with rfl | hEF
      · exact hQT
      · exact hFSubsetT hEF
    have hInsertCard : (insert Q F).card = F.card + 1 := by
      rw [Finset.card_insert_of_notMem hQNotF]
    exact (Finset.eq_of_subset_of_card_le hInsertSubset (by omega)).symm
  have hTRows : RowsCardAtLeast T 3 := by
    intro E hET
    exact hBRows E (mem_avoidPoint.mp (by simpa [T] using hET)).1
  have hQCard : 3 ≤ Q.card := hTRows Q hQT
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  have hBlockerTRows : RowsCardAtLeast (blocker T) 2 := by
    simpa [T] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
  have hBlockerT : blocker T = residual H x := by
    calc
      blocker T = blocker (avoidPoint (blocker H) x) := by rfl
      _ = residual (blocker (blocker H)) x :=
        blocker_avoidPoint (blocker_isClutter H) x
      _ = residual H x := by rw [blocker_involution hHClutter]
  have hBlockerTUpper : (blocker T).card ≤ 6 := by
    rw [hBlockerT]
    exact (residual_card_le H x).trans_eq hHCard
  obtain ⟨a, hPARaw⟩ := Finset.card_eq_one.mp (by simpa [PA] using hPrivateA)
  have hPA : PA = {a} := by simpa [PA] using hPARaw
  obtain ⟨hPAPB, hPAPC, hPBPC⟩ := privatePart_pairwise_disjoint A B C
  have hFTripleSubset : F ⊆ tripleChoiceRows PA PB PC := by
    intro E hEF
    rw [← hTripleForm]
    exact Finset.mem_inter.mp hEF |>.1
  obtain ⟨hPBBlockerF, hPCBlockerF⟩ :=
    tripleChoiceRows_two_covers_of_card_ge_three
      hPAPB hPAPC hPBPC
      (by simpa [PA] using hPrivateA)
      (by simpa [PB] using hPrivateB)
      (by simpa [PC] using hPrivateC)
      hFTripleSubset hFCardLower
  have hAllA : ∀ E ∈ F, a ∈ E :=
    tripleChoiceRows_all_first hPA hFTripleSubset
  have haPB : a ∉ PB := by
    intro haPB
    have haPA : a ∈ PA := by rw [hPA]; simp
    exact Finset.disjoint_left.mp hPAPB haPA haPB
  have haPC : a ∉ PC := by
    intro haPC
    have haPA : a ∈ PA := by rw [hPA]; simp
    exact Finset.disjoint_left.mp hPAPC haPA haPC
  have hPBMeet : (PB ∩ Q).Nonempty :=
    kernelB_cover_must_meet hTForm hAllA hQCard
      hPBBlockerF hPCBlockerF
      (by omega)
      hPBPC haPB haPC hBlockerTRows hBlockerTUpper
  have hPCMeet : (PC ∩ Q).Nonempty :=
    kernelB_cover_must_meet hTForm hAllA hQCard
      hPCBlockerF hPBBlockerF
      (by omega)
      hPBPC.symm haPC haPB hBlockerTRows hBlockerTUpper
  have hBlockerTLower : 5 ≤ (blocker T).card :=
    kernelB_blocker_card_ge_five_of_covers_meet
      hTForm hAllA hQCard hPBBlockerF hPCBlockerF
      (by omega)
      (by omega)
      hPBPC haPB haPC hPBMeet hPCMeet hBlockerTRows
  have hAK : A ∈ K := by change A ∈ avoidPoint H x; rw [hK]; simp
  have hBK : B ∈ K := by change B ∈ avoidPoint H x; rw [hK]; simp
  have hCK : C ∈ K := by change C ∈ avoidPoint H x; rw [hK]; simp
  have hAH : A ∈ H := (mem_avoidPoint.mp (by simpa [K] using hAK)).1
  have hBH : B ∈ H := (mem_avoidPoint.mp (by simpa [K] using hBK)).1
  have hCH : C ∈ H := (mem_avoidPoint.mp (by simpa [K] using hCK)).1
  have hxA : x ∉ A := (mem_avoidPoint.mp (by simpa [K] using hAK)).2
  have hxB : x ∉ B := (mem_avoidPoint.mp (by simpa [K] using hBK)).2
  have hxC : x ∉ C := (mem_avoidPoint.mp (by simpa [K] using hCK)).2
  have hANotBlockerT : A ∉ blocker T := by
    intro hAT
    obtain ⟨q, hqA, hqQ⟩ := (mem_blocker.mp hAT).prop Q hQT
    have hPairBlocker := kernelB_star_pair_mem_blocker
      hTForm hAllA hqQ (by
        intro haQ
        have hSingleton : IsTransversal T {a} := by
          intro E hET
          rw [hTForm] at hET
          simp only [Finset.mem_insert] at hET
          rcases hET with rfl | hEF
          · exact ⟨a, by simp, haQ⟩
          · exact ⟨a, by simp, hAllA E hEF⟩
        exact false_of_small_transversal hBlockerTRows hSingleton (by simp))
      hBlockerTRows
    have haA : a ∈ A := by
      have haPA : a ∈ PA := by rw [hPA]; simp
      exact (Finset.mem_sdiff.mp haPA).1
    have hPairSubset : ({a, q} : Row α) ⊆ A := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact haA
      · exact hqA
    have hEq := blocker_isClutter T hPairBlocker hAT hPairSubset
    have hPairCard : ({a, q} : Row α).card ≤ 2 := by
      calc
        ({a, q} : Row α).card ≤ ({q} : Row α).card + 1 := Finset.card_insert_le a {q}
        _ = 2 := by simp
    have hACard := hHRows A hAH
    rw [hEq] at hPairCard
    omega
  have hPBBlockerT : PB ∈ blocker T :=
    blocker_of_cover_meets_extra_row hTForm hPBBlockerF hPBMeet
  have hPCBlockerT : PC ∈ blocker T :=
    blocker_of_cover_meets_extra_row hTForm hPCBlockerF hPCMeet
  have hBNotBlockerT : B ∉ blocker T := by
    intro hBT
    have hPBSubset : PB ⊆ B := by
      intro y hyPB
      exact (Finset.mem_sdiff.mp hyPB).1
    have hEq := blocker_isClutter T hPBBlockerT hBT hPBSubset
    have hBCardLower := hHRows B hBH
    have hPBCard : PB.card = 2 := by simpa [PB] using hPrivateB
    rw [← hEq, hPBCard] at hBCardLower
    omega
  have hCNotBlockerT : C ∉ blocker T := by
    intro hCT
    have hPCSubset : PC ⊆ C := by
      intro y hyPC
      exact (Finset.mem_sdiff.mp hyPC).1
    have hEq := blocker_isClutter T hPCBlockerT hCT hPCSubset
    have hCCardLower := hHRows C hCH
    have hPCCard : PC.card = 2 := by simpa [PC] using hPrivateC
    rw [← hEq, hPCCard] at hCCardLower
    omega
  let deleted := deletePoint H x
  have hADeleted : A ∈ deleted := by
    exact Finset.mem_image.mpr ⟨A, hAH, by simp [hxA]⟩
  have hBDeleted : B ∈ deleted := by
    exact Finset.mem_image.mpr ⟨B, hBH, by simp [hxB]⟩
  have hCDeleted : C ∈ deleted := by
    exact Finset.mem_image.mpr ⟨C, hCH, by simp [hxC]⟩
  have hResidualSubset : blocker T ⊆ deleted := by
    rw [hBlockerT]
    exact minimize_subset deleted
  have hSmallSource : blocker T ⊆ ((deleted.erase A).erase B).erase C := by
    intro E hET
    have hEDeleted := hResidualSubset hET
    have hEA : E ≠ A := fun hEA ↦ hANotBlockerT (hEA ▸ hET)
    have hEB : E ≠ B := fun hEB ↦ hBNotBlockerT (hEB ▸ hET)
    have hEC : E ≠ C := fun hEC ↦ hCNotBlockerT (hEC ▸ hET)
    exact Finset.mem_erase.mpr ⟨hEC,
      Finset.mem_erase.mpr ⟨hEB, Finset.mem_erase.mpr ⟨hEA, hEDeleted⟩⟩⟩
  have hDeletedCard : deleted.card ≤ 6 := by
    simpa [deleted, deletePoint, hHCard] using
      (Finset.card_image_le (f := fun E : Row α ↦ E.erase x) (s := H))
  have hBEraseA : B ∈ deleted.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hBDeleted⟩
  have hCEraseAB : C ∈ (deleted.erase A).erase B :=
    Finset.mem_erase.mpr ⟨hBC.symm,
      Finset.mem_erase.mpr ⟨hAC.symm, hCDeleted⟩⟩
  have hSmallSourceCard : (((deleted.erase A).erase B).erase C).card ≤ 3 := by
    rw [Finset.card_erase_of_mem hCEraseAB,
      Finset.card_erase_of_mem hBEraseA,
      Finset.card_erase_of_mem hADeleted]
    omega
  have hBlockerTSmall := (Finset.card_le_card hSmallSource).trans hSmallSourceCard
  omega

def IsKernelBProfile
    (p q r x12 x13 x23 : Nat) : Prop :=
  (p = 1 ∧ q = 2 ∧ r = 2 ∧ x12 = 1 ∧ x13 = 1 ∧ x23 = 0) ∨
  (p = 2 ∧ q = 1 ∧ r = 2 ∧ x12 = 1 ∧ x13 = 0 ∧ x23 = 1) ∨
  (p = 2 ∧ q = 2 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 1 ∧ x23 = 1)

theorem sixTen_degreeThree_kernelB_impossible {α : Type*}
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
    (hProfile : IsKernelBProfile
      (privatePart A B C).card
      (privatePart B A C).card
      (privatePart C A B).card
      (sharedPart A B C).card
      (sharedPart A C B).card
      (sharedPart B C A).card) : False := by
  unfold IsKernelBProfile at hProfile
  rcases hProfile with hProfile | hProfile | hProfile
  · exact sixTen_degreeThree_kernelB_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC
      hProfile.1 hProfile.2.1 hProfile.2.2.1
      hProfile.2.2.2.1 hProfile.2.2.2.2.1 hProfile.2.2.2.2.2
  · have hK' : avoidPoint H x = {B, A, C} := by
      rw [hK]
      ext E
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact sixTen_degreeThree_kernelB_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK' hAB.symm hBC hAC
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.2)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.1)
  · have hK' : avoidPoint H x = {C, A, B} := by
      rw [hK]
      ext E
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact sixTen_degreeThree_kernelB_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK' hAC.symm hBC.symm hAB
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.2)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.1)

end AiMathLab.P0054.G419
