import AiMathLab.P0054G413.FiveRowPair

namespace AiMathLab.P0054.G413

theorem false_of_small_transversal {α : Type*}
    [Fintype α]
    {H : Hypergraph α} {T : Row α} {n : Nat}
    (hBRows : RowsCardAtLeast (blocker H) n)
    (hT : IsTransversal H T) (hTcard : T.card < n) : False := by
  obtain ⟨S, hST, hSmin⟩ := exists_minimalTransversal_subset hT
  have hSlower := hBRows S (mem_blocker.mpr hSmin)
  have hSupper := Finset.card_le_card hST
  omega

theorem fiveRow_maxDegreeAtMost_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    MaxDegreeAtMost H 3 := by
  classical
  intro x
  by_contra hnot
  have hDegree : 4 ≤ degree H x := by omega
  have hAvoidUpper : (avoidPoint H x).card ≤ 1 := by
    have hCount := card_avoidPoint_add_degree H x
    omega
  by_cases hAvoidEmpty : (avoidPoint H x).card = 0
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hPositive : 0 < (avoidPoint H x).card := Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · have hAvoidCard : (avoidPoint H x).card = 1 := by omega
    obtain ⟨E, hAvoidEq⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoidEq]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    have hEcard : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEcard
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : Row α).card ≤ 2).trans_lt (by omega))

theorem erase_mem_residual_of_row_card_eq_three {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) {E : Row α} (hEH : E ∈ H)
    {x : α} (hxE : x ∈ E) : E.erase x ∈ residual H x := by
  classical
  apply mem_minimize.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨E, hEH, rfl⟩
  · intro F hFdelete hFsub
    obtain ⟨A, hAH, hAerase⟩ := Finset.mem_image.mp hFdelete
    have hAsubE : A ⊆ E := by
      intro y hyA
      by_cases hyx : y = x
      · simpa [hyx] using hxE
      · have hyErase : y ∈ A.erase x := Finset.mem_erase.mpr ⟨hyx, hyA⟩
        have hyF : y ∈ F := hAerase ▸ hyErase
        exact Finset.mem_of_mem_erase (hFsub hyF)
    have hAE : A = E := hH hAH hEH hAsubE
    subst A
    simp [hAerase]

theorem fiveRow_three_row_avoiding_blocker_bound {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    {E : Row α} (hEH : E ∈ H) (hEcard : E.card = 3)
    {x : α} (hxE : x ∈ E) :
    6 ≤ (avoidPoint (blocker H) x).card := by
  classical
  let R := residual H x
  have hRclutter : IsClutter R := residual_isClutter H x
  have hRupper : R.card ≤ 5 := (residual_card_le H x).trans_eq hHcard
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hHRows x
  have hRPair : E.erase x ∈ pairRows R := by
    apply Finset.mem_filter.mpr
    constructor
    · exact erase_mem_residual_of_row_card_eq_three hH hEH hxE
    · rw [Finset.card_erase_of_mem hxE, hEcard]
  have hRPairs : (pairRows R).card ≤ 3 := by
    have hDegree := fiveRow_maxDegreeAtMost_three hHcard hHRows hBRows x
    exact (pairRows_residual_card_le_degree hHRows x).trans hDegree
  have hRBlockerRows : RowsCardAtLeast (blocker R) 3 := by
    intro T hTR
    have hTAvoid : T ∈ avoidPoint (blocker H) x := by
      simpa [R, blocker_residual] using hTR
    exact hBRows T (mem_avoidPoint.mp hTAvoid).1
  have hRRowsNonempty : RowsNonempty R := by
    intro A hAR
    have hAcard := hRRows A hAR
    exact Finset.card_pos.mp (by omega)
  obtain ⟨T, hTBlocker⟩ := blocker_nonempty hRRowsNonempty
  have hRlower : 3 ≤ R.card := by
    have hTlower := hRBlockerRows T hTBlocker
    have hTupper := minimalTransversal_card_le_rows (mem_blocker.mp hTBlocker)
    omega
  have hCases : R.card = 3 ∨ R.card = 4 ∨ R.card = 5 := by omega
  have hSix : 6 ≤ (blocker R).card := by
    rcases hCases with hRcard | hRcard | hRcard
    · have hEight := threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three
        hRcard hRRows hRBlockerRows
      omega
    · exact fourRow_pair_residual_bound R hRclutter hRcard hRRows hRPairs
        hRBlockerRows ⟨E.erase x, (Finset.mem_filter.mp hRPair).1,
          (Finset.mem_filter.mp hRPair).2⟩
    · exact fiveRow_pair_residual_bound R hRclutter hRcard hRRows hRPairs
        hRBlockerRows ⟨E.erase x, (Finset.mem_filter.mp hRPair).1,
          (Finset.mem_filter.mp hRPair).2⟩
  simpa [R, blocker_residual] using hSix

theorem fiveRows_opposite_rows_disjoint {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D E : Row α}
    (hH : H = {A, B, C, D, E})
    (hBRows : RowsCardAtLeast (blocker H) 4)
    (hAB : (A ∩ B).Nonempty) (hE : E.Nonempty) :
    Disjoint C D := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hyCD
  obtain ⟨x, hxAB⟩ := hAB
  obtain ⟨z, hzE⟩ := hE
  have hTransversal : IsTransversal H {x, y, z} := by
    intro R hRH
    simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with rfl | rfl | rfl | rfl | rfl
    · exact ⟨x, by simp, (Finset.mem_inter.mp hxAB).1⟩
    · exact ⟨x, by simp, (Finset.mem_inter.mp hxAB).2⟩
    · exact ⟨y, by simp, (Finset.mem_inter.mp hyCD).1⟩
    · exact ⟨y, by simp, (Finset.mem_inter.mp hyCD).2⟩
    · exact ⟨z, by simp, hzE⟩
  exact (false_of_small_transversal hBRows hTransversal
    (Finset.card_le_three.trans_lt (by omega))).elim

theorem fiveRows_intersecting_pair_blocker_card_ge_sixteen {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D E : Row α}
    (hH : H = {A, B, C, D, E})
    (hRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 4)
    (hAB : (A ∩ B).Nonempty) :
    16 ≤ (blocker H).card := by
  classical
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hEH : E ∈ H := by simp [hH]
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by
    have := hRows C hCH
    omega)
  have hDnonempty : D.Nonempty := Finset.card_pos.mp (by
    have := hRows D hDH
    omega)
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by
    have := hRows E hEH
    omega)
  have hCD : Disjoint C D :=
    fiveRows_opposite_rows_disjoint hH hBRows hAB hEnonempty
  have hCE : Disjoint C E :=
    fiveRows_opposite_rows_disjoint
      (A := A) (B := B) (C := C) (D := E) (E := D)
      (by
        rw [hH]
        ext R
        simp [or_comm]) hBRows hAB hDnonempty
  have hDE : Disjoint D E :=
    fiveRows_opposite_rows_disjoint
      (A := A) (B := B) (C := D) (D := E) (E := C)
      (by
        rw [hH]
        ext R
        simp [or_comm, or_left_comm]) hBRows hAB hCnonempty
  obtain ⟨z, hzAB⟩ := hAB
  obtain ⟨e, heE⟩ := hEnonempty
  have hzC : z ∉ C := by
    intro hzC
    obtain ⟨d, hdD⟩ := hDnonempty
    have hTransversal : IsTransversal H {z, d, e} := by
      intro R hRH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hRH
      rcases hRH with rfl | rfl | rfl | rfl | rfl
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).1⟩
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).2⟩
      · exact ⟨z, by simp, hzC⟩
      · exact ⟨d, by simp, hdD⟩
      · exact ⟨e, by simp, heE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_three.trans_lt (by omega))
  have hzD : z ∉ D := by
    intro hzD
    obtain ⟨c, hcC⟩ := hCnonempty
    have hTransversal : IsTransversal H {z, c, e} := by
      intro R hRH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hRH
      rcases hRH with rfl | rfl | rfl | rfl | rfl
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).1⟩
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).2⟩
      · exact ⟨c, by simp, hcC⟩
      · exact ⟨z, by simp, hzD⟩
      · exact ⟨e, by simp, heE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_three.trans_lt (by omega))
  have hzE : z ∉ E := by
    intro hzE
    obtain ⟨c, hcC⟩ := hCnonempty
    obtain ⟨d, hdD⟩ := hDnonempty
    have hTransversal : IsTransversal H {z, c, d} := by
      intro R hRH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hRH
      rcases hRH with rfl | rfl | rfl | rfl | rfl
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).1⟩
      · exact ⟨z, by simp, (Finset.mem_inter.mp hzAB).2⟩
      · exact ⟨c, by simp, hcC⟩
      · exact ⟨d, by simp, hdD⟩
      · exact ⟨z, by simp, hzE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_three.trans_lt (by omega))
  let starRow : α × α → Row α := fun p ↦ {z, p.1, p.2, e}
  let choices : Finset (α × α) := C.product D
  have hInjective : Set.InjOn starRow (↑choices : Set (α × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpC, hpD⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqC, hqD⟩ := Finset.mem_product.mp hq'
    have hFirst : p.1 = q.1 := by
      have hpMem : p.1 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq | hpq
      · exact (hzC (hpq ▸ hpC)).elim
      · exact hpq
      · exact (Finset.disjoint_left.mp hCD hpC (hpq ▸ hqD)).elim
      · exact (Finset.disjoint_left.mp hCE hpC (hpq ▸ heE)).elim
    have hSecond : p.2 = q.2 := by
      have hpMem : p.2 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq | hpq
      · exact (hzD (hpq ▸ hpD)).elim
      · exact (Finset.disjoint_left.mp hCD (hpq ▸ hqC) hpD).elim
      · exact hpq
      · exact (Finset.disjoint_left.mp hDE hpD (hpq ▸ heE)).elim
    exact Prod.ext hFirst hSecond
  have hImageSubset : choices.image starRow ⊆ blocker H := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hpC, hpD⟩ := Finset.mem_product.mp hp
    apply mem_blocker.mpr
    have hTransversal : IsTransversal H (starRow p) := by
      intro F hFH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hFH
      rcases hFH with rfl | rfl | rfl | rfl | rfl
      · exact ⟨z, by simp [starRow], (Finset.mem_inter.mp hzAB).1⟩
      · exact ⟨z, by simp [starRow], (Finset.mem_inter.mp hzAB).2⟩
      · exact ⟨p.1, by simp [starRow], hpC⟩
      · exact ⟨p.2, by simp [starRow], hpD⟩
      · exact ⟨e, by simp [starRow], heE⟩
    apply hTransversal.minimal_of_privateRows
    intro x hxRow
    simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hxRow
    rcases hxRow with hxz | hxc | hxd | hxe
    · subst x
      by_cases hAPrivate : ∀ y ∈ starRow p, y ∈ A → y = z
      · exact ⟨A, hAH, by simp [starRow], (Finset.mem_inter.mp hzAB).1, hAPrivate⟩
      · push Not at hAPrivate
        obtain ⟨a, haRow, haA, haz⟩ := hAPrivate
        have haSmall : a ∈ ({p.1, p.2, e} : Row α) := by
          simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at haRow
          rcases haRow with rfl | haRow | haRow | haRow
          · exact (haz rfl).elim
          · simp [haRow]
          · simp [haRow]
          · simp [haRow]
        have hBPrivate : ∀ y ∈ starRow p, y ∈ B → y = z := by
          intro y hyRow hyB
          by_contra hyz
          have hySmall : y ∈ ({p.1, p.2, e} : Row α) := by
            simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
            rcases hyRow with rfl | hyRow | hyRow | hyRow
            · exact (hyz rfl).elim
            · simp [hyRow]
            · simp [hyRow]
            · simp [hyRow]
          have hSmallTransversal : IsTransversal H {p.1, p.2, e} := by
            intro F hFH
            simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hFH
            rcases hFH with rfl | rfl | rfl | rfl | rfl
            · exact ⟨a, haSmall, haA⟩
            · exact ⟨y, hySmall, hyB⟩
            · exact ⟨p.1, by simp, hpC⟩
            · exact ⟨p.2, by simp, hpD⟩
            · exact ⟨e, by simp, heE⟩
          exact false_of_small_transversal hBRows hSmallTransversal
            (Finset.card_le_three.trans_lt (by omega))
        exact ⟨B, hBH, by simp [starRow], (Finset.mem_inter.mp hzAB).2, hBPrivate⟩
    · subst x
      exact ⟨C, hCH, by simp [starRow], hpC, by
        intro y hyRow hyC
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl
        · exact (hzC hyC).elim
        · rfl
        · exact (Finset.disjoint_left.mp hCD hyC hpD).elim
        · exact (Finset.disjoint_left.mp hCE hyC heE).elim⟩
    · subst x
      exact ⟨D, hDH, by simp [starRow], hpD, by
        intro y hyRow hyD
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl
        · exact (hzD hyD).elim
        · exact (Finset.disjoint_left.mp hCD hpC hyD).elim
        · rfl
        · exact (Finset.disjoint_left.mp hDE hyD heE).elim⟩
    · subst x
      exact ⟨E, hEH, by simp [starRow], heE, by
        intro y hyRow hyE
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl
        · exact (hzE hyE).elim
        · exact (Finset.disjoint_left.mp hCE hpC hyE).elim
        · exact (Finset.disjoint_left.mp hDE hpD hyE).elim
        · rfl⟩
  calc
    16 = 4 * 4 := rfl
    _ ≤ C.card * D.card := Nat.mul_le_mul (hRows C hCH) (hRows D hDH)
    _ = choices.card := by simp [choices, Finset.card_product]
    _ = (choices.image starRow).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem fiveRows_pairwise_disjoint_blocker_card_ge_sixteen {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D E : Row α}
    (hH : H = {A, B, C, D, E})
    (hRows : RowsCardAtLeast H 4)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hAE : Disjoint A E) (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hBE : Disjoint B E) (hCD : Disjoint C D) (hCE : Disjoint C E)
    (hDE : Disjoint D E) :
    16 ≤ (blocker H).card := by
  classical
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hEH : E ∈ H := by simp [hH]
  have hApositive : 0 < A.card := by
    have := hRows A hAH
    omega
  have hBpositive : 0 < B.card := by
    have := hRows B hBH
    omega
  have hCpositive : 0 < C.card := by
    have := hRows C hCH
    omega
  obtain ⟨a, haA⟩ := Finset.card_pos.mp hApositive
  obtain ⟨b, hbB⟩ := Finset.card_pos.mp hBpositive
  obtain ⟨c, hcC⟩ := Finset.card_pos.mp hCpositive
  let fullRow : α × α → Row α := fun p ↦ {a, b, c, p.1, p.2}
  let choices : Finset (α × α) := D.product E
  have hInjective : Set.InjOn fullRow (↑choices : Set (α × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqD, hqE⟩ := Finset.mem_product.mp hq'
    have hFirst : p.1 = q.1 := by
      have hpMem : p.1 ∈ fullRow q := by
        rw [← hEq]
        simp [fullRow]
      simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq | hpq | hpq
      · exact (Finset.disjoint_left.mp hAD (hpq ▸ haA) hpD).elim
      · exact (Finset.disjoint_left.mp hBD (hpq ▸ hbB) hpD).elim
      · exact (Finset.disjoint_left.mp hCD (hpq ▸ hcC) hpD).elim
      · exact hpq
      · exact (Finset.disjoint_left.mp hDE hpD (hpq ▸ hqE)).elim
    have hSecond : p.2 = q.2 := by
      have hpMem : p.2 ∈ fullRow q := by
        rw [← hEq]
        simp [fullRow]
      simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq | hpq | hpq
      · exact (Finset.disjoint_left.mp hAE (hpq ▸ haA) hpE).elim
      · exact (Finset.disjoint_left.mp hBE (hpq ▸ hbB) hpE).elim
      · exact (Finset.disjoint_left.mp hCE (hpq ▸ hcC) hpE).elim
      · exact (Finset.disjoint_left.mp hDE (hpq ▸ hqD) hpE).elim
      · exact hpq
    exact Prod.ext hFirst hSecond
  have hImageSubset : choices.image fullRow ⊆ blocker H := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hpD, hpE⟩ := Finset.mem_product.mp hp
    apply mem_blocker.mpr
    have hTransversal : IsTransversal H (fullRow p) := by
      intro F hFH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hFH
      rcases hFH with rfl | rfl | rfl | rfl | rfl
      · exact ⟨a, by simp [fullRow], haA⟩
      · exact ⟨b, by simp [fullRow], hbB⟩
      · exact ⟨c, by simp [fullRow], hcC⟩
      · exact ⟨p.1, by simp [fullRow], hpD⟩
      · exact ⟨p.2, by simp [fullRow], hpE⟩
    apply hTransversal.minimal_of_privateRows
    intro x hxRow
    simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hxRow
    rcases hxRow with hxa | hxb | hxc | hxd | hxe
    · subst x
      exact ⟨A, hAH, by simp [fullRow], haA, by
        intro y hyRow hyA
        simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl | rfl
        · rfl
        · exact (Finset.disjoint_left.mp hAB hyA hbB).elim
        · exact (Finset.disjoint_left.mp hAC hyA hcC).elim
        · exact (Finset.disjoint_left.mp hAD hyA hpD).elim
        · exact (Finset.disjoint_left.mp hAE hyA hpE).elim⟩
    · subst x
      exact ⟨B, hBH, by simp [fullRow], hbB, by
        intro y hyRow hyB
        simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hAB haA hyB).elim
        · rfl
        · exact (Finset.disjoint_left.mp hBC hyB hcC).elim
        · exact (Finset.disjoint_left.mp hBD hyB hpD).elim
        · exact (Finset.disjoint_left.mp hBE hyB hpE).elim⟩
    · subst x
      exact ⟨C, hCH, by simp [fullRow], hcC, by
        intro y hyRow hyC
        simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hAC haA hyC).elim
        · exact (Finset.disjoint_left.mp hBC hbB hyC).elim
        · rfl
        · exact (Finset.disjoint_left.mp hCD hyC hpD).elim
        · exact (Finset.disjoint_left.mp hCE hyC hpE).elim⟩
    · subst x
      exact ⟨D, hDH, by simp [fullRow], hpD, by
        intro y hyRow hyD
        simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hAD haA hyD).elim
        · exact (Finset.disjoint_left.mp hBD hbB hyD).elim
        · exact (Finset.disjoint_left.mp hCD hcC hyD).elim
        · rfl
        · exact (Finset.disjoint_left.mp hDE hyD hpE).elim⟩
    · subst x
      exact ⟨E, hEH, by simp [fullRow], hpE, by
        intro y hyRow hyE
        simp only [fullRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hAE haA hyE).elim
        · exact (Finset.disjoint_left.mp hBE hbB hyE).elim
        · exact (Finset.disjoint_left.mp hCE hcC hyE).elim
        · exact (Finset.disjoint_left.mp hDE hpD hyE).elim
        · rfl⟩
  calc
    16 = 4 * 4 := rfl
    _ ≤ D.card * E.card := Nat.mul_le_mul (hRows D hDH) (hRows E hEH)
    _ = choices.card := by simp [choices, Finset.card_product]
    _ = (choices.image fullRow).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem exists_five_distinct_rows_of_card_eq_five {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} (hHcard : H.card = 5) :
    ∃ A B C D E : Row α,
      H = {A, B, C, D, E} ∧
      A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ A ≠ E ∧
      B ≠ C ∧ B ≠ D ∧ B ≠ E ∧ C ≠ D ∧ C ≠ E ∧ D ≠ E := by
  classical
  have hCardFive : H.card = 4 + 1 := by omega
  obtain ⟨A, H₄, hAH₄, hAForm, hH₄card⟩ := Finset.card_eq_succ.mp hCardFive
  have hCardFour : H₄.card = 3 + 1 := by omega
  obtain ⟨B, H₃, hBH₃, hBForm, hH₃card⟩ := Finset.card_eq_succ.mp hCardFour
  have hCardThree : H₃.card = 2 + 1 := by omega
  obtain ⟨C, H₂, hCH₂, hCForm, hH₂card⟩ := Finset.card_eq_succ.mp hCardThree
  have hCardTwo : H₂.card = 1 + 1 := by omega
  obtain ⟨D, H₁, hDH₁, hDForm, hH₁card⟩ := Finset.card_eq_succ.mp hCardTwo
  have hCardOne : H₁.card = 0 + 1 := by omega
  obtain ⟨E, H₀, hEH₀, hEForm, hH₀card⟩ := Finset.card_eq_succ.mp hCardOne
  have hH₀empty : H₀ = ∅ := Finset.card_eq_zero.mp hH₀card
  have hForm : H = {A, B, C, D, E} := by
    calc
      H = insert A H₄ := hAForm.symm
      _ = insert A (insert B H₃) := by rw [hBForm]
      _ = insert A (insert B (insert C H₂)) := by rw [hCForm]
      _ = insert A (insert B (insert C (insert D H₁))) := by rw [hDForm]
      _ = insert A (insert B (insert C (insert D (insert E H₀)))) := by rw [hEForm]
      _ = {A, B, C, D, E} := by simp [hH₀empty]
  have hBH₄ : B ∈ H₄ := by rw [← hBForm]; simp
  have hCH₄ : C ∈ H₄ := by rw [← hBForm, ← hCForm]; simp
  have hDH₄ : D ∈ H₄ := by rw [← hBForm, ← hCForm, ← hDForm]; simp
  have hEH₄ : E ∈ H₄ := by rw [← hBForm, ← hCForm, ← hDForm, ← hEForm]; simp
  have hCH₃ : C ∈ H₃ := by rw [← hCForm]; simp
  have hDH₃ : D ∈ H₃ := by rw [← hCForm, ← hDForm]; simp
  have hEH₃ : E ∈ H₃ := by rw [← hCForm, ← hDForm, ← hEForm]; simp
  have hDH₂ : D ∈ H₂ := by rw [← hDForm]; simp
  have hEH₂ : E ∈ H₂ := by rw [← hDForm, ← hEForm]; simp
  have hEH₁ : E ∈ H₁ := by rw [← hEForm]; simp
  refine ⟨A, B, C, D, E, hForm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h ↦ hAH₄ (h ▸ hBH₄)
  · exact fun h ↦ hAH₄ (h ▸ hCH₄)
  · exact fun h ↦ hAH₄ (h ▸ hDH₄)
  · exact fun h ↦ hAH₄ (h ▸ hEH₄)
  · exact fun h ↦ hBH₃ (h ▸ hCH₃)
  · exact fun h ↦ hBH₃ (h ▸ hDH₃)
  · exact fun h ↦ hBH₃ (h ▸ hEH₃)
  · exact fun h ↦ hCH₂ (h ▸ hDH₂)
  · exact fun h ↦ hCH₂ (h ▸ hEH₂)
  · exact fun h ↦ hDH₁ (h ▸ hEH₁)

theorem fiveRow_intersecting_rows_blocker_card_ge_sixteen {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hHcard : H.card = 5)
    (hRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 4)
    {A B : Row α} (hAH : A ∈ H) (hBH : B ∈ H)
    (hABne : A ≠ B) (hAB : (A ∩ B).Nonempty) :
    16 ≤ (blocker H).card := by
  classical
  let K := (H.erase A).erase B
  have hBErase : B ∈ H.erase A := Finset.mem_erase.mpr ⟨hABne.symm, hBH⟩
  have hEraseAcard : (H.erase A).card = 4 := by
    rw [Finset.card_erase_of_mem hAH, hHcard]
  have hKcard : K.card = 3 := by
    dsimp [K]
    rw [Finset.card_erase_of_mem hBErase, hEraseAcard]
  obtain ⟨C, D, E, -, -, -, hKForm⟩ := Finset.card_eq_three.mp hKcard
  have hCH : C ∈ H := by
    have hCK : C ∈ K := by simp [hKForm]
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hCK)
  have hDH : D ∈ H := by
    have hDK : D ∈ K := by simp [hKForm]
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hDK)
  have hEH : E ∈ H := by
    have hEK : E ∈ K := by simp [hKForm]
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hEK)
  have hForm : H = {A, B, C, D, E} := by
    ext R
    constructor
    · intro hRH
      by_cases hRA : R = A
      · simp [hRA]
      by_cases hRB : R = B
      · simp [hRB]
      have hRK : R ∈ K := by simp [K, hRH, hRA, hRB]
      have hCases : R = C ∨ R = D ∨ R = E := by simpa [hKForm] using hRK
      rcases hCases with rfl | rfl | rfl <;> simp
    · intro hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl
      · exact hAH
      · exact hBH
      · exact hCH
      · exact hDH
      · exact hEH
  exact fiveRows_intersecting_pair_blocker_card_ge_sixteen hForm hRows hBRows hAB

theorem fiveRow_blocker_card_ge_sixteen_of_both_rows_cardAtLeast_four {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hHcard : H.card = 5)
    (hRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    16 ≤ (blocker H).card := by
  classical
  by_cases hIntersect :
      ∃ A ∈ H, ∃ B ∈ H, A ≠ B ∧ (A ∩ B).Nonempty
  · obtain ⟨A, hAH, B, hBH, hABne, hAB⟩ := hIntersect
    exact fiveRow_intersecting_rows_blocker_card_ge_sixteen
      hHcard hRows hBRows hAH hBH hABne hAB
  · obtain ⟨A, B, C, D, E, hH,
      hABne, hACne, hADne, hAEne, hBCne, hBDne, hBEne, hCDne, hCEne, hDEne⟩ :=
      exists_five_distinct_rows_of_card_eq_five hHcard
    have hAH : A ∈ H := by simp [hH]
    have hBH : B ∈ H := by simp [hH]
    have hCH : C ∈ H := by simp [hH]
    have hDH : D ∈ H := by simp [hH]
    have hEH : E ∈ H := by simp [hH]
    have pairDisjoint {X Y : Row α}
        (hXH : X ∈ H) (hYH : Y ∈ H) (hXY : X ≠ Y) : Disjoint X Y :=
      disjoint_of_inter_not_nonempty
        (fun hXYInter ↦ hIntersect ⟨X, hXH, Y, hYH, hXY, hXYInter⟩)
    exact fiveRows_pairwise_disjoint_blocker_card_ge_sixteen hH hRows
      (pairDisjoint hAH hBH hABne)
      (pairDisjoint hAH hCH hACne)
      (pairDisjoint hAH hDH hADne)
      (pairDisjoint hAH hEH hAEne)
      (pairDisjoint hBH hCH hBCne)
      (pairDisjoint hBH hDH hBDne)
      (pairDisjoint hBH hEH hBEne)
      (pairDisjoint hCH hDH hCDne)
      (pairDisjoint hCH hEH hCEne)
      (pairDisjoint hDH hEH hDEne)

theorem fiveRow_large_residual_bound {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    6 ≤ (blocker H).card := by
  classical
  by_contra hnot
  have hBupper : (blocker H).card ≤ 5 := by omega
  have hHpositive : 0 < H.card := by omega
  obtain ⟨A, hAH⟩ := Finset.card_pos.mp hHpositive
  have hAdual : A ∈ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hAH
  have hBlower : 3 ≤ (blocker H).card := by
    have hAcard := hHRows A hAH
    have hAle := minimalTransversal_card_le_rows (mem_blocker.mp hAdual)
    omega
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hH]
    exact hHRows
  have hBRowsTwo : RowsCardAtLeast (blocker H) 2 := by
    intro T hTH
    have := hBRows T hTH
    omega
  have hBcard : (blocker H).card = 5 := by
    have hCases :
        (blocker H).card = 3 ∨ (blocker H).card = 4 ∨ (blocker H).card = 5 := by
      omega
    rcases hCases with hCardThree | hCardFour | hCardFive
    · have hEight := threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three
        hCardThree hBRowsTwo hDualRows
      rw [blocker_involution hH, hHcard] at hEight
      omega
    · have hNine := fourLargeRows_blocker_card_ge_nine
        (blocker_isClutter H) hCardFour hBRows hDualRows
      rw [blocker_involution hH, hHcard] at hNine
      omega
    · exact hCardFive
  have hHRowsFour : RowsCardAtLeast H 4 := by
    intro E hEH
    have hEcardLower := hHRows E hEH
    by_contra hEcardNotFour
    have hEcard : E.card = 3 := by omega
    have hEpositive : 0 < E.card := by omega
    obtain ⟨x, hxE⟩ := Finset.card_pos.mp hEpositive
    have hSixAvoid := fiveRow_three_row_avoiding_blocker_bound
      hH hHcard hHRows hBRows hEH hEcard hxE
    have hAvoidUpper : (avoidPoint (blocker H) x).card ≤ (blocker H).card :=
      Finset.card_le_card (by
        intro T hT
        exact (mem_avoidPoint.mp hT).1)
    omega
  have hBRowsFour : RowsCardAtLeast (blocker H) 4 := by
    intro T hTH
    have hTcardLower := hBRows T hTH
    by_contra hTcardNotFour
    have hTcard : T.card = 3 := by omega
    have hTpositive : 0 < T.card := by omega
    obtain ⟨x, hxT⟩ := Finset.card_pos.mp hTpositive
    have hSixAvoid := fiveRow_three_row_avoiding_blocker_bound
      (blocker_isClutter H) hBcard hBRows hDualRows hTH hTcard hxT
    have hAvoidUpper :
        (avoidPoint (blocker (blocker H)) x).card ≤ (blocker (blocker H)).card :=
      Finset.card_le_card (by
        intro Q hQ
        exact (mem_avoidPoint.mp hQ).1)
    rw [blocker_involution hH] at hSixAvoid
    rw [blocker_involution hH, hHcard] at hAvoidUpper
    omega
  have hSixteen := fiveRow_blocker_card_ge_sixteen_of_both_rows_cardAtLeast_four
    hHcard hHRowsFour hBRowsFour
  omega

end AiMathLab.P0054.G413
