import AiMathLab.P0054MiddleNineDegree
import AiMathLab.P0054G419.KernelBGrid

/-!
# The tight B-profile in the middle split six plus nine

The three-row kernel has five pair blockers and four triple blockers.  Their
nine canonical lifts exhaust the nine blockers of the original clutter.  This
forces a two-point transversal on the dual side, contradicting the row-size
assumption.
-/

namespace AiMathLab.P0054.MiddleSixNineKernel

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem kernelB_impossible_explicit {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9)
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
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two
      (by simpa [K] using hK) hBKRows
  have hPairLower : 5 ≤ pairFamily.card := by
    have hGenerated := threePairGenerated_card_le_pairRows
      (by simpa [K] using hK)
    simpa [pairFamily, hPrivateA, hPrivateB, hPrivateC,
      hSharedAB, hSharedAC, hSharedBC] using hGenerated
  have hTripleCard : tripleFamily.card = 4 := by
    change (rowsCardExactly (blocker K) 3).card = 4
    rw [threeRow_triple_blockers_card
      (by simpa [K] using hK) hAB hAC hBC]
    simp [hPrivateA, hPrivateB, hPrivateC]
  have hTripleForm : tripleFamily = tripleChoiceRows PA PB PC := by
    change rowsCardExactly (blocker K) 3 = tripleChoiceRows PA PB PC
    simpa [PA, PB, PC] using
      threeRow_triple_blockers (by simpa [K] using hK) hAB hAC hBC
  have hBKCardUpper : (blocker K).card ≤ 9 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  have hPairTripleCard :=
    threeRow_blocker_card_add_pair_triple hKCard hBKRows
  have hPairCard : pairFamily.card = 5 := by
    change pairFamily.card + tripleFamily.card = (blocker K).card at hPairTripleCard
    omega
  have hBKCard : (blocker K).card = 9 := by
    change pairFamily.card + tripleFamily.card = (blocker K).card at hPairTripleCard
    omega
  obtain ⟨a, hPARaw⟩ :=
    Finset.card_eq_one.mp (by simpa [PA] using hPrivateA)
  have hPA : PA = {a} := by simpa [PA] using hPARaw
  have haPA : a ∈ PA := by simp [hPA]
  have haPrivate : a ∈ privatePart A B C := by simpa [PA] using haPA
  have haA : a ∈ A := (Finset.mem_sdiff.mp haPrivate).1
  have haNotUnion : a ∉ B ∪ C := (Finset.mem_sdiff.mp haPrivate).2
  have haB : a ∉ B := fun haB ↦ haNotUnion (Finset.mem_union_left C haB)
  have haC : a ∉ C := fun haC ↦ haNotUnion (Finset.mem_union_right B haC)
  have hAK : A ∈ K := by simp [K, hK]
  have hxA : x ∉ A := (mem_avoidPoint.mp (by simpa [K] using hAK)).2
  have hax : a ≠ x := fun hax ↦ hxA (hax ▸ haA)
  have hPairAvoidsA : ∀ U ∈ pairFamily, a ∉ U := by
    intro U hUPair haU
    obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
    have hBMem : B ∈ K := by simp [K, hK]
    have hCMem : C ∈ K := by simp [K, hK]
    obtain ⟨b, hbU, hbB⟩ := (mem_blocker.mp hUBlocker).prop B hBMem
    obtain ⟨c, hcU, hcC⟩ := (mem_blocker.mp hUBlocker).prop C hCMem
    have hba : b ≠ a := fun hba ↦ haB (hba ▸ hbB)
    have hca : c ≠ a := fun hca ↦ haC (hca ▸ hcC)
    have hbErase : b ∈ U.erase a := Finset.mem_erase.mpr ⟨hba, hbU⟩
    have hcErase : c ∈ U.erase a := Finset.mem_erase.mpr ⟨hca, hcU⟩
    have hEraseCard : (U.erase a).card = 1 := by
      rw [Finset.card_erase_of_mem haU, hUCard]
    obtain ⟨d, hErase⟩ := Finset.card_eq_one.mp hEraseCard
    have hbd : b = d := by rw [hErase] at hbErase; simpa using hbErase
    have hcd : c = d := by rw [hErase] at hcErase; simpa using hcErase
    have hbc : b = c := hbd.trans hcd.symm
    have hbC : b ∈ C := hbc ▸ hcC
    by_cases hbA : b ∈ A
    · exact hNoCommon b ⟨hbA, hbB, hbC⟩
    · have hbShared : b ∈ sharedPart B C A :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hbB, hbC⟩, hbA⟩
      have hSharedEmpty : sharedPart B C A = ∅ :=
        Finset.card_eq_zero.mp hSharedBC
      rw [hSharedEmpty] at hbShared
      simp at hbShared
  let lifts := (blocker K).image (avoidBlockerLift H x)
  have hLiftsCard : lifts.card = 9 := by
    calc
      lifts.card = (blocker K).card :=
        Finset.card_image_iff.mpr (avoidBlockerLift_injective H x)
      _ = 9 := hBKCard
  have hLiftsSubset : lifts ⊆ blocker H := by
    intro E hE
    obtain ⟨U, hUK, rfl⟩ := Finset.mem_image.mp hE
    exact avoidBlockerLift_mem_blocker hUK
  have hLiftsEq : lifts = blocker H :=
    Finset.eq_of_subset_of_card_le hLiftsSubset (by rw [hLiftsCard, hBCard])
  have hAvoidContainsA :
      ∀ E ∈ blocker H, x ∉ E → a ∈ E := by
    intro E hEB hxE
    have hELift : E ∈ lifts := by rw [hLiftsEq]; exact hEB
    obtain ⟨U, hUK, hLiftEq⟩ := Finset.mem_image.mp hELift
    have hUNotPair : U ∉ pairFamily := by
      intro hUPair
      obtain ⟨-, hUCard⟩ := Finset.mem_filter.mp hUPair
      have hNotTransversal : ¬ IsTransversal H U := by
        intro hTransversal
        exact false_of_small_transversal hBRows hTransversal (by omega)
      have hxLift : x ∈ avoidBlockerLift H x U := by
        simp [avoidBlockerLift, hNotTransversal]
      rw [hLiftEq] at hxLift
      exact hxE hxLift
    have hUCardLower : 2 ≤ U.card := hBKRows U hUK
    have hUCardUpper : U.card ≤ K.card :=
      minimalTransversal_card_le_rows (mem_blocker.mp hUK)
    have hUCard : U.card = 3 := by
      have hCases : U.card = 2 ∨ U.card = 3 := by omega
      rcases hCases with hTwo | hThree
      · exact (hUNotPair (Finset.mem_filter.mpr ⟨hUK, hTwo⟩)).elim
      · exact hThree
    have hUTriple : U ∈ tripleFamily := by
      exact mem_rowsCardExactly.mpr ⟨hUK, hUCard⟩
    have hUChoice : U ∈ tripleChoiceRows PA PB PC := by
      rw [← hTripleForm]
      exact hUTriple
    obtain ⟨p, hpPA, q, hqPB, r, hrPC, hpqr⟩ :=
      mem_tripleChoiceRows.mp hUChoice
    have hpa : p = a := by rw [hPA] at hpPA; simpa using hpPA
    have haU : a ∈ U := by rw [← hpqr, hpa]; simp
    have haLift : a ∈ avoidBlockerLift H x U := by
      unfold avoidBlockerLift
      split <;> simp [haU]
    rw [hLiftEq] at haLift
    exact haLift
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hAvoidLower : 2 ≤ (avoidPoint (blocker H) x).card :=
    AiMathLab.P0054.MiddleLower.avoid_blocker_card_ge_two
      hHNonempty hHRows x
  have hAvoidNonempty : (avoidPoint (blocker H) x).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨E, hEAvoid⟩ := hAvoidNonempty
  have hEB : E ∈ blocker H := (mem_avoidPoint.mp hEAvoid).1
  have hxE : x ∉ E := (mem_avoidPoint.mp hEAvoid).2
  have haE : a ∈ E := hAvoidContainsA E hEB hxE
  have hPairNonempty : pairFamily.Nonempty :=
    Finset.card_pos.mp (by rw [hPairCard]; omega)
  obtain ⟨U, hUPair⟩ := hPairNonempty
  obtain ⟨hUK, hUCard⟩ := Finset.mem_filter.mp hUPair
  have hUNotTransversal : ¬ IsTransversal H U := by
    intro hTransversal
    exact false_of_small_transversal hBRows hTransversal (by omega)
  have hPairLiftB : avoidBlockerLift H x U ∈ blocker H :=
    avoidBlockerLift_mem_blocker hUK
  have hxPairLift : x ∈ avoidBlockerLift H x U := by
    simp [avoidBlockerLift, hUNotTransversal]
  have haPairLift : a ∉ avoidBlockerLift H x U := by
    simp [avoidBlockerLift, hUNotTransversal,
      hPairAvoidsA U hUPair, hax]
  have hTwoTransversal : IsTransversal (blocker H) {a, x} := by
    intro Q hQB
    by_cases hxQ : x ∈ Q
    · exact ⟨x, by simp, hxQ⟩
    · exact ⟨a, by simp, hAvoidContainsA Q hQB hxQ⟩
  have hTwoDual : {a, x} ∈ blocker (blocker H) := by
    apply mem_blocker.mpr
    apply hTwoTransversal.minimal_of_privateRows
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hya | hyx
    · subst y
      refine ⟨E, hEB, by simp, haE, ?_⟩
      intro z hzPair hzE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with rfl | rfl
      · rfl
      · exact (hxE hzE).elim
    · subst y
      refine ⟨avoidBlockerLift H x U, hPairLiftB, by simp, hxPairLift, ?_⟩
      intro z hzPair hzLift
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with rfl | rfl
      · exact (haPairLift hzLift).elim
      · rfl
  have hTwoH : {a, x} ∈ H := by
    rw [blocker_involution hHClutter] at hTwoDual
    exact hTwoDual
  have hTwoLower := hHRows {a, x} hTwoH
  have hTwoUpper : ({a, x} : Row α).card ≤ 2 := Finset.card_le_two
  omega

theorem kernelB_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9)
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
  · exact kernelB_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC
      hProfile.1 hProfile.2.1 hProfile.2.2.1
      hProfile.2.2.2.1 hProfile.2.2.2.2.1 hProfile.2.2.2.2.2
  · have hK' : avoidPoint H x = {B, A, C} := by
      rw [hK]
      ext E
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact kernelB_impossible_explicit
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
    exact kernelB_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK' hAC.symm hBC.symm hAB
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.2)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.1)

end AiMathLab.P0054.MiddleSixNineKernel
