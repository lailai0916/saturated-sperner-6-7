import AiMathLab.P0054G419.KernelCExclude

namespace AiMathLab.P0054.G419

open G413

noncomputable def minimalBlockerSubset {α : Type*} [Fintype α]
    (H : G413.Hypergraph α) (T : Row α) : Row α := by
  classical
  exact if hT : IsTransversal H T then
    Classical.choose (exists_minimalTransversal_subset hT)
  else ∅

theorem minimalBlockerSubset_spec {α : Type*} [Fintype α]
    {H : G413.Hypergraph α} {T : Row α}
    (hT : IsTransversal H T) :
    minimalBlockerSubset H T ⊆ T ∧ minimalBlockerSubset H T ∈ blocker H := by
  classical
  unfold minimalBlockerSubset
  rw [dif_pos hT]
  exact ⟨(Classical.choose_spec (exists_minimalTransversal_subset hT)).1,
    mem_blocker.mpr (Classical.choose_spec (exists_minimalTransversal_subset hT)).2⟩

theorem kernelB_star_pair_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {a q : α} {F T : G413.Hypergraph α} {Q : Row α}
    (hT : T = insert Q F)
    (hAllA : ∀ E ∈ F, a ∈ E)
    (hqQ : q ∈ Q) (haQ : a ∉ Q)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    ({a, q} : Row α) ∈ blocker T := by
  have haq : a ≠ q := fun haq ↦ haQ (haq ▸ hqQ)
  have hTransversal : IsTransversal T {a, q} := by
    intro E hET
    rw [hT] at hET
    simp only [Finset.mem_insert] at hET
    rcases hET with rfl | hEF
    · exact ⟨q, by simp, hqQ⟩
    · exact ⟨a, by simp, hAllA E hEF⟩
  have hSingletonNotTransversal : ¬IsTransversal T {q} := by
    intro hq
    exact false_of_small_transversal hBRows hq (by simp)
  simp only [IsTransversal] at hSingletonNotTransversal
  push Not at hSingletonNotTransversal
  obtain ⟨E, hET, hMiss⟩ := hSingletonNotTransversal
  have hqE : q ∉ E := fun hqE ↦ hMiss q (by simp) hqE
  have hEF : E ∈ F := by
    rw [hT] at hET
    simp only [Finset.mem_insert] at hET
    rcases hET with hEQ | hEF
    · subst E
      exact (hqE hqQ).elim
    · exact hEF
  apply pair_mem_blocker_threeRows hTransversal
  · exact ⟨E, by rw [hT]; simp [hEF], hAllA E hEF, hqE⟩
  · exact ⟨Q, by rw [hT]; simp, hqQ, haQ⟩

noncomputable def kernelBCoverLift {α : Type*} [Fintype α] [DecidableEq α]
    (T : G413.Hypergraph α) (S : Row α) (q : α) : Row α :=
  minimalBlockerSubset T (insert q S)

theorem kernelBCoverLift_spec {α : Type*}
    [Fintype α] [DecidableEq α]
    {q : α} {F T : G413.Hypergraph α} {Q S : Row α}
    (hT : T = insert Q F)
    (hSBlocker : S ∈ blocker F) (hqQ : q ∈ Q) :
    kernelBCoverLift T S q ⊆ insert q S ∧
      kernelBCoverLift T S q ∈ blocker T := by
  unfold kernelBCoverLift
  apply minimalBlockerSubset_spec
  intro E hET
  rw [hT] at hET
  simp only [Finset.mem_insert] at hET
  rcases hET with rfl | hEF
  · exact ⟨q, by simp, hqQ⟩
  · obtain ⟨s, hsS, hsE⟩ := (mem_blocker.mp hSBlocker).prop E hEF
    exact ⟨s, by simp [hsS], hsE⟩

theorem kernelBCoverLift_mem {α : Type*}
    [Fintype α] [DecidableEq α]
    {q : α} {F T : G413.Hypergraph α} {Q S : Row α}
    (hT : T = insert Q F)
    (hSBlocker : S ∈ blocker F) (hSQ : Disjoint S Q) (hqQ : q ∈ Q) :
    q ∈ kernelBCoverLift T S q := by
  obtain ⟨hLiftSubset, hLiftBlocker⟩ :=
    kernelBCoverLift_spec hT hSBlocker hqQ
  have hQT : Q ∈ T := by rw [hT]; simp
  obtain ⟨y, hyLift, hyQ⟩ := (mem_blocker.mp hLiftBlocker).prop Q hQT
  have hySource := hLiftSubset hyLift
  simp only [Finset.mem_insert] at hySource
  rcases hySource with hyq | hyS
  · simpa [hyq] using hyLift
  · exact (Finset.disjoint_left.mp hSQ hyS hyQ).elim

theorem kernelBCoverLift_trace_unique {α : Type*}
    [Fintype α] [DecidableEq α]
    {q y : α} {F T : G413.Hypergraph α} {Q S : Row α}
    (hT : T = insert Q F)
    (hSBlocker : S ∈ blocker F) (hSQ : Disjoint S Q) (hqQ : q ∈ Q)
    (hyQ : y ∈ Q) (hyLift : y ∈ kernelBCoverLift T S q) : y = q := by
  have hLiftSubset := (kernelBCoverLift_spec hT hSBlocker hqQ).1
  have hySource := hLiftSubset hyLift
  simp only [Finset.mem_insert] at hySource
  rcases hySource with hyq | hyS
  · exact hyq
  · exact (Finset.disjoint_left.mp hSQ hyS hyQ).elim

theorem kernelBCoverLift_avoids {α : Type*}
    [Fintype α] [DecidableEq α]
    {a q : α} {F T : G413.Hypergraph α} {Q S : Row α}
    (hT : T = insert Q F)
    (hSBlocker : S ∈ blocker F) (hqQ : q ∈ Q)
    (haS : a ∉ S) (haQ : a ∉ Q) :
    a ∉ kernelBCoverLift T S q := by
  intro haLift
  have haSource := (kernelBCoverLift_spec hT hSBlocker hqQ).1 haLift
  simp only [Finset.mem_insert] at haSource
  rcases haSource with haq | haS'
  · exact haQ (haq ▸ hqQ)
  · exact haS haS'

theorem blocker_of_cover_meets_extra_row {α : Type*}
    [Fintype α] [DecidableEq α]
    {F T : G413.Hypergraph α} {Q D : Row α}
    (hT : T = insert Q F)
    (hDBlocker : D ∈ blocker F) (hMeet : (D ∩ Q).Nonempty) :
    D ∈ blocker T := by
  obtain ⟨q, hqMeet⟩ := hMeet
  obtain ⟨hqD, hqQ⟩ := Finset.mem_inter.mp hqMeet
  have hDTransversal : IsTransversal T D := by
    intro E hET
    rw [hT] at hET
    simp only [Finset.mem_insert] at hET
    rcases hET with rfl | hEF
    · exact ⟨q, hqD, hqQ⟩
    · exact (mem_blocker.mp hDBlocker).prop E hEF
  apply mem_blocker.mpr
  apply isMinimalTransversal_iff.mpr
  refine ⟨hDTransversal, ?_⟩
  intro U hUD hUTransversal
  have hUF : IsTransversal F U := by
    intro E hEF
    exact hUTransversal E (by rw [hT]; simp [hEF])
  exact (isMinimalTransversal_iff.mp (mem_blocker.mp hDBlocker)).2 hUD hUF

theorem exists_mem_ne_of_two_le_card {α : Type*}
    {S : Row α} (hS : 2 ≤ S.card) (x : α) (_hxS : x ∈ S) :
    ∃ y ∈ S, y ≠ x := by
  obtain ⟨u, huS, v, hvS, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  by_cases hux : u = x
  · exact ⟨v, hvS, fun hvx ↦ huv (hux.trans hvx.symm)⟩
  · exact ⟨u, huS, hux⟩

theorem kernelB_cover_must_meet {α : Type*}
    [Fintype α] [DecidableEq α]
    {a : α} {F T : G413.Hypergraph α} {Q S D : Row α}
    (hT : T = insert Q F)
    (hAllA : ∀ E ∈ F, a ∈ E)
    (hQCard : 3 ≤ Q.card)
    (hSBlocker : S ∈ blocker F) (hDBlocker : D ∈ blocker F)
    (hDCard : 2 ≤ D.card)
    (hSD : Disjoint S D) (haS : a ∉ S) (haD : a ∉ D)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hBCard : (blocker T).card ≤ 6) :
    (S ∩ Q).Nonempty := by
  classical
  have haQ : a ∉ Q := by
    intro haQ
    have hATransversal : IsTransversal T {a} := by
      intro E hET
      rw [hT] at hET
      simp only [Finset.mem_insert] at hET
      rcases hET with rfl | hEF
      · exact ⟨a, by simp, haQ⟩
      · exact ⟨a, by simp, hAllA E hEF⟩
    exact false_of_small_transversal hBRows hATransversal (by simp)
  by_contra hMeet
  have hSQ : Disjoint S Q := Finset.disjoint_left.mpr (by
    intro s hsS hsQ
    exact hMeet ⟨s, Finset.mem_inter.mpr ⟨hsS, hsQ⟩⟩)
  let pairs := crossPairRows ({a} : Row α) Q
  have hPairSubset : pairs ⊆ blocker T := by
    intro E hE
    obtain ⟨z, hz, q, hqQ, rfl⟩ := mem_crossPairRows.mp hE
    have hza : z = a := by simpa using hz
    subst z
    exact kernelB_star_pair_mem_blocker hT hAllA hqQ haQ hBRows
  have hPairLower : 3 ≤ pairs.card := by
    have hDisjoint : Disjoint ({a} : Row α) Q := by simp [haQ]
    calc
      3 ≤ ({a} : Row α).card * Q.card := by
        simpa only [Finset.card_singleton, one_mul] using hQCard
      _ ≤ pairs.card := card_mul_le_crossPairRows_card_of_disjoint hDisjoint
  let lifts := Q.image fun q ↦ kernelBCoverLift T S q
  have hLiftCard : lifts.card = Q.card := by
    change (Q.image fun q ↦ kernelBCoverLift T S q).card = Q.card
    rw [Finset.card_image_iff.mpr]
    intro q hqQ r hrQ hEq
    have hqLift : q ∈ kernelBCoverLift T S q :=
      kernelBCoverLift_mem hT hSBlocker hSQ hqQ
    have hqOther : q ∈ kernelBCoverLift T S r := by simpa [hEq] using hqLift
    exact kernelBCoverLift_trace_unique hT hSBlocker hSQ hrQ hqQ hqOther
  have hLiftSubset : lifts ⊆ blocker T := by
    intro E hE
    obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hE
    exact (kernelBCoverLift_spec hT hSBlocker hqQ).2
  have hPairLiftDisjoint : Disjoint pairs lifts := by
    apply Finset.disjoint_left.mpr
    intro E hEPair hELift
    obtain ⟨z, hz, q, hqQ, hzaq⟩ := mem_crossPairRows.mp hEPair
    have hza : z = a := by simpa using hz
    obtain ⟨r, hrQ, hrEq⟩ := Finset.mem_image.mp hELift
    have haE : a ∈ E := by rw [← hzaq, hza]; simp
    rw [← hrEq] at haE
    exact kernelBCoverLift_avoids hT hSBlocker hrQ haS haQ haE
  have hBaseSubset : pairs ∪ lifts ⊆ blocker T := by
    intro E hE
    rcases Finset.mem_union.mp hE with hEPair | hELift
    · exact hPairSubset hEPair
    · exact hLiftSubset hELift
  have hBaseLower : 6 ≤ (pairs ∪ lifts).card := by
    rw [Finset.card_union_of_disjoint hPairLiftDisjoint, hLiftCard]
    omega
  obtain ⟨q0, hq0Q⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
  let extra : Row α := if hDQ : (D ∩ Q).Nonempty then D
    else kernelBCoverLift T D q0
  have hExtraBlocker : extra ∈ blocker T := by
    unfold extra
    split
    · rename_i hDQ
      exact blocker_of_cover_meets_extra_row hT hDBlocker hDQ
    · exact (kernelBCoverLift_spec hT hDBlocker hq0Q).2
  have haExtra : a ∉ extra := by
    unfold extra
    split
    · exact haD
    · exact kernelBCoverLift_avoids hT hDBlocker hq0Q haD haQ
  have hExtraNotPairs : extra ∉ pairs := by
    intro hExtra
    obtain ⟨z, hz, q, hqQ, hzq⟩ := mem_crossPairRows.mp hExtra
    have hza : z = a := by simpa using hz
    apply haExtra
    rw [← hzq, hza]
    simp
  have hExtraNotLifts : extra ∉ lifts := by
    intro hExtra
    obtain ⟨q, hqQ, hLiftEq⟩ := Finset.mem_image.mp hExtra
    unfold extra at hLiftEq
    split at hLiftEq
    · rename_i hDQ
      obtain ⟨d, hdMeet⟩ := hDQ
      obtain ⟨hdD, hdQ⟩ := Finset.mem_inter.mp hdMeet
      have hdLift : d ∈ kernelBCoverLift T S q := by rw [hLiftEq]; exact hdD
      have hdq := kernelBCoverLift_trace_unique hT hSBlocker hSQ hqQ hdQ hdLift
      obtain ⟨e, heD, hed⟩ := exists_mem_ne_of_two_le_card hDCard d hdD
      have heLift : e ∈ kernelBCoverLift T S q := by rw [hLiftEq]; exact heD
      have heSource := (kernelBCoverLift_spec hT hSBlocker hqQ).1 heLift
      simp only [Finset.mem_insert] at heSource
      rcases heSource with heq | heS
      · exact (hed (heq.trans hdq.symm)).elim
      · exact (Finset.disjoint_left.mp hSD heS heD).elim
    · rename_i hDQ
      have hDQDisjoint : Disjoint D Q := Finset.disjoint_left.mpr (by
        intro d hdD hdQ
        exact hDQ ⟨d, Finset.mem_inter.mpr ⟨hdD, hdQ⟩⟩)
      have hq0Extra : q0 ∈ kernelBCoverLift T D q0 :=
        kernelBCoverLift_mem hT hDBlocker hDQDisjoint hq0Q
      have hq0Lift : q0 ∈ kernelBCoverLift T S q := by
        simpa [hLiftEq] using hq0Extra
      have hq0q := kernelBCoverLift_trace_unique hT hSBlocker hSQ hqQ hq0Q hq0Lift
      have hExtraCard : 2 ≤ (kernelBCoverLift T D q0).card :=
        hBRows _ (kernelBCoverLift_spec hT hDBlocker hq0Q).2
      obtain ⟨e, heExtra, heq0⟩ :=
        exists_mem_ne_of_two_le_card hExtraCard q0 hq0Extra
      have heSLift : e ∈ kernelBCoverLift T S q := by
        simpa [hLiftEq] using heExtra
      have heSsource := (kernelBCoverLift_spec hT hSBlocker hqQ).1 heSLift
      have heDsource := (kernelBCoverLift_spec hT hDBlocker hq0Q).1 heExtra
      simp only [Finset.mem_insert] at heSsource heDsource
      rcases heSsource with heq | heS
      · exact (heq0 (heq.trans hq0q.symm)).elim
      · rcases heDsource with heq0' | heD
        · exact (heq0 heq0').elim
        · exact (Finset.disjoint_left.mp hSD heS heD).elim
  have hExtraNotBase : extra ∉ pairs ∪ lifts := by simp [hExtraNotPairs, hExtraNotLifts]
  have hInsertSubset : insert extra (pairs ∪ lifts) ⊆ blocker T := by
    intro E hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | hEBase
    · exact hExtraBlocker
    · exact hBaseSubset hEBase
  have hSeven : 7 ≤ (blocker T).card := by
    calc
      7 ≤ (pairs ∪ lifts).card + 1 := by omega
      _ = (insert extra (pairs ∪ lifts)).card :=
        (Finset.card_insert_of_notMem hExtraNotBase).symm
      _ ≤ (blocker T).card := Finset.card_le_card hInsertSubset
  omega

theorem kernelB_blocker_card_ge_five_of_covers_meet {α : Type*}
    [Fintype α] [DecidableEq α]
    {a : α} {F T : G413.Hypergraph α} {Q S D : Row α}
    (hT : T = insert Q F)
    (hAllA : ∀ E ∈ F, a ∈ E)
    (hQCard : 3 ≤ Q.card)
    (hSBlocker : S ∈ blocker F) (hDBlocker : D ∈ blocker F)
    (hSCard : 2 ≤ S.card) (hDCard : 2 ≤ D.card)
    (hSD : Disjoint S D) (haS : a ∉ S) (haD : a ∉ D)
    (hSMeet : (S ∩ Q).Nonempty) (hDMeet : (D ∩ Q).Nonempty)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    5 ≤ (blocker T).card := by
  classical
  have haQ : a ∉ Q := by
    intro haQ
    have hATransversal : IsTransversal T {a} := by
      intro E hET
      rw [hT] at hET
      simp only [Finset.mem_insert] at hET
      rcases hET with rfl | hEF
      · exact ⟨a, by simp, haQ⟩
      · exact ⟨a, by simp, hAllA E hEF⟩
    exact false_of_small_transversal hBRows hATransversal (by simp)
  let pairs := crossPairRows ({a} : Row α) Q
  have hPairSubset : pairs ⊆ blocker T := by
    intro E hE
    obtain ⟨z, hz, q, hqQ, rfl⟩ := mem_crossPairRows.mp hE
    have hza : z = a := by simpa using hz
    subst z
    exact kernelB_star_pair_mem_blocker hT hAllA hqQ haQ hBRows
  have hPairLower : 3 ≤ pairs.card := by
    have hDisjoint : Disjoint ({a} : Row α) Q := by simp [haQ]
    calc
      3 ≤ ({a} : Row α).card * Q.card := by
        simpa only [Finset.card_singleton, one_mul] using hQCard
      _ ≤ pairs.card := card_mul_le_crossPairRows_card_of_disjoint hDisjoint
  have hST : S ∈ blocker T :=
    blocker_of_cover_meets_extra_row hT hSBlocker hSMeet
  have hDT : D ∈ blocker T :=
    blocker_of_cover_meets_extra_row hT hDBlocker hDMeet
  have hSNotPairs : S ∉ pairs := by
    intro hS
    obtain ⟨z, hz, q, hqQ, hzq⟩ := mem_crossPairRows.mp hS
    have hza : z = a := by simpa using hz
    have haS' : a ∈ S := by rw [← hzq, hza]; simp
    exact haS haS'
  have hDNotPairs : D ∉ pairs := by
    intro hD
    obtain ⟨z, hz, q, hqQ, hzq⟩ := mem_crossPairRows.mp hD
    have hza : z = a := by simpa using hz
    have haD' : a ∈ D := by rw [← hzq, hza]; simp
    exact haD haD'
  have hSDNe : S ≠ D := by
    intro hEq
    obtain ⟨s, hsS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact Finset.disjoint_left.mp hSD hsS (hEq ▸ hsS)
  have hKnownSubset : insert S (insert D pairs) ⊆ blocker T := by
    intro E hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEPair
    · exact hST
    · exact hDT
    · exact hPairSubset hEPair
  have hKnownCard : (insert S (insert D pairs)).card = pairs.card + 2 := by
    have hSNotInsert : S ∉ insert D pairs := by simp [hSDNe, hSNotPairs]
    rw [Finset.card_insert_of_notMem hSNotInsert]
    rw [Finset.card_insert_of_notMem hDNotPairs]
  calc
    5 ≤ (insert S (insert D pairs)).card := by rw [hKnownCard]; omega
    _ ≤ (blocker T).card := Finset.card_le_card hKnownSubset

end AiMathLab.P0054.G419
