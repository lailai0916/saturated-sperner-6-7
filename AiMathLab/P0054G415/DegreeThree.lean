import AiMathLab.P0054G413.FiveRowLarge

namespace AiMathLab.P0054.G415

open G413

theorem twoAvoidingRows_blockers_containing_card_ge_nine {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    {x : α} (hAvoidCard : (avoidPoint H x).card = 2) :
    9 ≤ degree (blocker H) x := by
  classical
  obtain ⟨P, Q, hPQ, hAvoid⟩ := Finset.card_eq_two.mp hAvoidCard
  have hPAvoid : P ∈ avoidPoint H x := by simp [hAvoid]
  have hQAvoid : Q ∈ avoidPoint H x := by simp [hAvoid]
  have hPH : P ∈ H := (mem_avoidPoint.mp hPAvoid).1
  have hQH : Q ∈ H := (mem_avoidPoint.mp hQAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hxQ : x ∉ Q := (mem_avoidPoint.mp hQAvoid).2
  have hDisjoint : Disjoint P Q := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hyPQ
    have hTransversal : IsTransversal H {x, y} := by
      intro E hEH
      by_cases hxE : x ∈ E
      · exact ⟨x, by simp, hxE⟩
      · have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hEPQ : E = P ∨ E = Q := by simpa [hAvoid] using hEAvoid
        rcases hEPQ with rfl | rfl
        · exact ⟨y, by simp, (Finset.mem_inter.mp hyPQ).1⟩
        · exact ⟨y, by simp, (Finset.mem_inter.mp hyPQ).2⟩
    exact (false_of_small_transversal hBRows hTransversal
      (Finset.card_le_two.trans_lt (by omega))).elim
  let starRow : α × α → Row α := fun p ↦ {x, p.1, p.2}
  let choices : Finset (α × α) := P.product Q
  have hInjective : Set.InjOn starRow (↑choices : Set (α × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpP, hpQ⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqP, hqQ⟩ := Finset.mem_product.mp hq'
    have hFirst : p.1 = q.1 := by
      have hpMem : p.1 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq
      · exact (hxP (hpq ▸ hpP)).elim
      · exact hpq
      · exact (Finset.disjoint_left.mp hDisjoint hpP (hpq ▸ hqQ)).elim
    have hSecond : p.2 = q.2 := by
      have hpMem : p.2 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq
      · exact (hxQ (hpq ▸ hpQ)).elim
      · exact (Finset.disjoint_left.mp hDisjoint (hpq ▸ hqP) hpQ).elim
      · exact hpq
    exact Prod.ext hFirst hSecond
  have hImageSubset : choices.image starRow ⊆ blocker H := by
    intro T hT
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hpP, hpQ⟩ := Finset.mem_product.mp hp
    apply mem_blocker.mpr
    have hTransversal : IsTransversal H (starRow p) := by
      intro E hEH
      by_cases hxE : x ∈ E
      · exact ⟨x, by simp [starRow], hxE⟩
      · have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hEPQ : E = P ∨ E = Q := by simpa [hAvoid] using hEAvoid
        rcases hEPQ with rfl | rfl
        · exact ⟨p.1, by simp [starRow], hpP⟩
        · exact ⟨p.2, by simp [starRow], hpQ⟩
    apply hTransversal.minimal_of_privateRows
    intro y hyRow
    simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
    rcases hyRow with hyx | hyp | hyq
    · subst y
      have hPairNotTransversal : ¬ IsTransversal H {p.1, p.2} := by
        intro hPairTransversal
        exact false_of_small_transversal hBRows hPairTransversal
          (Finset.card_le_two.trans_lt (by omega))
      simp only [IsTransversal] at hPairNotTransversal
      push Not at hPairNotTransversal
      obtain ⟨E, hEH, hNoPair⟩ := hPairNotTransversal
      have hxE : x ∈ E := by
        obtain ⟨z, hzRow, hzE⟩ := hTransversal E hEH
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hzRow
        rcases hzRow with rfl | rfl | rfl
        · exact hzE
        · exact (hNoPair p.1 (by simp) hzE).elim
        · exact (hNoPair p.2 (by simp) hzE).elim
      exact ⟨E, hEH, by simp [starRow], hxE, by
        intro z hzRow hzE
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hzRow
        rcases hzRow with rfl | rfl | rfl
        · rfl
        · exact (hNoPair p.1 (by simp) hzE).elim
        · exact (hNoPair p.2 (by simp) hzE).elim⟩
    · subst y
      exact ⟨P, hPH, by simp [starRow], hpP, by
        intro z hzRow hzP
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hzRow
        rcases hzRow with rfl | rfl | rfl
        · exact (hxP hzP).elim
        · rfl
        · exact (Finset.disjoint_left.mp hDisjoint hzP hpQ).elim⟩
    · subst y
      exact ⟨Q, hQH, by simp [starRow], hpQ, by
        intro z hzRow hzQ
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hzRow
        rcases hzRow with rfl | rfl | rfl
        · exact (hxQ hzQ).elim
        · exact (Finset.disjoint_left.mp hDisjoint hpP hzQ).elim
        · rfl⟩
  have hImageSubsetDegree :
      choices.image starRow ⊆ (blocker H).filter fun E ↦ x ∈ E := by
    intro E hE
    exact Finset.mem_filter.mpr ⟨hImageSubset hE, by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hE
      simp [starRow]⟩
  calc
    9 = 3 * 3 := rfl
    _ ≤ P.card * Q.card := Nat.mul_le_mul (hHRows P hPH) (hHRows Q hQH)
    _ = choices.card := by simp [choices, Finset.card_product]
    _ = (choices.image starRow).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ degree (blocker H) x := by
      rw [degree]
      exact Finset.card_le_card hImageSubsetDegree

theorem degreeThree_blockers_containing_card_ge_nine {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    {x : α} (hDegree : degree H x = 3) :
    9 ≤ degree (blocker H) x := by
  apply twoAvoidingRows_blockers_containing_card_ge_nine hHRows hBRows
  have hPartition := card_avoidPoint_add_degree H x
  omega

theorem fiveEleven_degreeThree_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (_hH : IsClutter H)
    (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBcard : (blocker H).card = 11)
    {x : α} (hDegree : degree H x = 3) : False := by
  classical
  have hBlockerDegree : 9 ≤ degree (blocker H) x :=
    degreeThree_blockers_containing_card_ge_nine hHcard hHRows hBRows hDegree
  have hAvoidHCard : (avoidPoint H x).card = 2 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  have hAvoidHNonempty : (avoidPoint H x).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨P, hPAvoid⟩ := hAvoidHNonempty
  have hPH : P ∈ H := (mem_avoidPoint.mp hPAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hPDelete : P ∈ deletePoint H x := by
    exact Finset.mem_image.mpr ⟨P, hPH, by simp [hxP]⟩
  let R : Hypergraph α := residual H x
  obtain ⟨M, hMMinimize, -⟩ := exists_minimize_subset hPDelete
  have hRNonempty : R.Nonempty := by
    exact ⟨M, by simpa [R, residual] using hMMinimize⟩
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter H x
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hHRows x
  have hResidualBlockerLower : 2 ≤ (blocker R).card :=
    blocker_card_ge_two_of_rows_cardAtLeast_two hRClutter hRNonempty hRRows
  have hAvoidBlockerLower : 2 ≤ (avoidPoint (blocker H) x).card := by
    rw [← blocker_residual H x]
    simpa [R] using hResidualBlockerLower
  have hBlockerPartition := card_avoidPoint_add_degree (blocker H) x
  have hAvoidBlockerCard : (avoidPoint (blocker H) x).card = 2 := by
    omega
  obtain ⟨E₀, E₁, hE₀E₁, hAvoidBlocker⟩ :=
    Finset.card_eq_two.mp hAvoidBlockerCard
  have hE₀Avoid : E₀ ∈ avoidPoint (blocker H) x := by simp [hAvoidBlocker]
  have hE₁Avoid : E₁ ∈ avoidPoint (blocker H) x := by simp [hAvoidBlocker]
  have hE₀Blocker : E₀ ∈ blocker H := (mem_avoidPoint.mp hE₀Avoid).1
  have hE₁Blocker : E₁ ∈ blocker H := (mem_avoidPoint.mp hE₁Avoid).1
  have hE₀Card : 3 ≤ E₀.card := hBRows E₀ hE₀Blocker
  have hE₁Card : 3 ≤ E₁.card := hBRows E₁ hE₁Blocker
  have hResidualBlocker : blocker R = {E₀, E₁} := by
    calc
      blocker R = avoidPoint (blocker H) x := by simpa [R] using blocker_residual H x
      _ = {E₀, E₁} := hAvoidBlocker
  have hPairBlocker : blocker ({E₀, E₁} : Hypergraph α) = R := by
    calc
      blocker ({E₀, E₁} : Hypergraph α) = blocker (blocker R) :=
        (congrArg blocker hResidualBlocker).symm
      _ = R := blocker_involution hRClutter
  have hPairBlockerRows :
      RowsCardAtLeast (blocker ({E₀, E₁} : Hypergraph α)) 2 := by
    rw [hPairBlocker]
    exact hRRows
  have hProduct := twoRow_blocker_card_ge_product hPairBlockerRows
  have hRLower : 9 ≤ R.card := by
    calc
      9 = 3 * 3 := rfl
      _ ≤ E₀.card * E₁.card := Nat.mul_le_mul hE₀Card hE₁Card
      _ ≤ (blocker ({E₀, E₁} : Hypergraph α)).card := hProduct
      _ = R.card := congrArg Finset.card hPairBlocker
  have hRUpper : R.card ≤ 5 := by
    have hUpper := residual_card_le H x
    simpa [R, hHcard] using hUpper
  omega

end AiMathLab.P0054.G415
