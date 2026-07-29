import AiMathLab.P0054G413.ThreeRows

namespace AiMathLab.P0054.G413

theorem IsClutter.mono {α : Type*} {H K : Hypergraph α}
    (hH : IsClutter H) (hKH : K ⊆ H) : IsClutter K := by
  intro A hAK B hBK hAB
  exact hH (hKH hAK) (hKH hBK) hAB

theorem disjoint_of_inter_not_nonempty {α : Type*} [DecidableEq α]
    {A B : Row α} (hAB : ¬(A ∩ B).Nonempty) : Disjoint A B := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact Finset.not_nonempty_iff_eq_empty.mp hAB

theorem isolatedRow_product_le_blocker_card {α : Type*}
    [Fintype α] [DecidableEq α]
    {H K : Hypergraph α} {A : Row α}
    (hH : H = insert A K)
    (hAK : ∀ E ∈ K, Disjoint A E) :
    A.card * (blocker K).card ≤ (blocker H).card := by
  let lifted : α × Row α → Row α := fun p ↦ insert p.1 p.2
  let choices : Finset (α × Row α) := A.product (blocker K)
  have avoids_A {T : Row α} (hTb : T ∈ blocker K) : ∀ x ∈ T, x ∉ A := by
    intro x hxT hxA
    obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hTb).exists_privateRow hxT
    exact Finset.disjoint_left.mp (hAK E hPrivate.1) hxA hPrivate.2.2.1
  have hInjective : Set.InjOn lifted (↑choices : Set (α × Row α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp hq'
    have hpAvoid := avoids_A hpB
    have hqAvoid := avoids_A hqB
    have hFirst : p.1 = q.1 := by
      have hpMem : p.1 ∈ lifted q := by
        rw [← hEq]
        simp [lifted]
      simp only [lifted, Finset.mem_insert] at hpMem
      rcases hpMem with hpq | hpq
      · exact hpq
      · exact (hqAvoid p.1 hpq hpA).elim
    have hSecond : p.2 = q.2 := by
      ext x
      constructor
      · intro hxp
        have hxLifted : x ∈ lifted q := by
          rw [← hEq]
          simp [lifted, hxp]
        simp only [lifted, Finset.mem_insert] at hxLifted
        rcases hxLifted with hxq | hxq
        · exact (hpAvoid x hxp (hxq ▸ hqA)).elim
        · exact hxq
      · intro hxq
        have hxLifted : x ∈ lifted p := by
          rw [hEq]
          simp [lifted, hxq]
        simp only [lifted, Finset.mem_insert] at hxLifted
        rcases hxLifted with hxp | hxp
        · exact (hqAvoid x hxq (hxp ▸ hpA)).elim
        · exact hxp
    exact Prod.ext hFirst hSecond
  have hImageSubset : choices.image lifted ⊆ blocker H := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
    have hpAvoid := avoids_A hpB
    apply mem_blocker.mpr
    have hTransversal : IsTransversal H (lifted p) := by
      intro E hEH
      simp only [hH, Finset.mem_insert] at hEH
      rcases hEH with rfl | hEK
      · exact ⟨p.1, by simp [lifted], hpA⟩
      · obtain ⟨x, hxT, hxE⟩ := (mem_blocker.mp hpB).prop E hEK
        exact ⟨x, by simp [lifted, hxT], hxE⟩
    apply hTransversal.minimal_of_privateRows
    intro x hxR
    simp only [lifted, Finset.mem_insert] at hxR
    rcases hxR with rfl | hxT
    · exact ⟨A, by simp [hH], by simp [lifted], hpA, by
        intro y hyR hyA
        simp only [lifted, Finset.mem_insert] at hyR
        rcases hyR with rfl | hyT
        · rfl
        · exact (hpAvoid y hyT hyA).elim⟩
    · obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hpB).exists_privateRow hxT
      exact ⟨E, by simp [hH, hPrivate.1], by simp [lifted, hxT], hPrivate.2.2.1, by
        intro y hyR hyE
        simp only [lifted, Finset.mem_insert] at hyR
        rcases hyR with rfl | hyT
        · exact (Finset.disjoint_left.mp (hAK E hPrivate.1) hpA hyE).elim
        · exact hPrivate.2.2.2 hyT hyE⟩
  calc
    A.card * (blocker K).card = choices.card := by
      simp [choices, Finset.card_product]
    _ = (choices.image lifted).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem fourRows_blocker_card_ge_nine_of_first_isolated {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D : Row α}
    (hHclutter : IsClutter H) (hH : H = {A, B, C, D})
    (hRows : RowsCardAtLeast H 3)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) :
    9 ≤ (blocker H).card := by
  let K : Hypergraph α := {B, C, D}
  have hHK : H = insert A K := by simp [hH, K]
  have hKsubset : K ⊆ H := by
    intro E hE
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl <;> simp [hH]
  have hKclutter : IsClutter K := hHclutter.mono hKsubset
  have hAK : ∀ E ∈ K, Disjoint A E := by
    intro E hE
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hAD
  have hProduct := isolatedRow_product_le_blocker_card hHK hAK
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hBK : B ∈ K := by simp [K]
  have hBdual : B ∈ blocker (blocker K) := by
    rw [blocker_involution hKclutter]
    exact hBK
  have hBlockerKLower : 3 ≤ (blocker K).card := by
    have hBcardLe := minimalTransversal_card_le_rows (mem_blocker.mp hBdual)
    exact (hRows B hBH).trans hBcardLe
  calc
    9 = 3 * 3 := rfl
    _ ≤ A.card * (blocker K).card :=
      Nat.mul_le_mul (hRows A hAH) hBlockerKLower
    _ ≤ (blocker H).card := hProduct

theorem fourRows_blocker_card_ge_nine_of_first_star {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D : Row α}
    (hH : H = {A, B, C, D}) (hRows : RowsCardAtLeast H 3)
    (hAB : (A ∩ B).Nonempty)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    9 ≤ (blocker H).card := by
  obtain ⟨z, hzAB⟩ := hAB
  let starRow : α × α → Row α := fun p ↦ {p.1, z, p.2}
  let choices : Finset (α × α) := C.product D
  have hzB : z ∈ B := (Finset.mem_inter.mp hzAB).2
  have hInjective : Set.InjOn starRow (↑choices : Set (α × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpC, hpD⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqC, hqD⟩ := Finset.mem_product.mp hq'
    have hzNotC : z ∉ C := fun hzC ↦ Finset.disjoint_left.mp hBC hzB hzC
    have hzNotD : z ∉ D := fun hzD ↦ Finset.disjoint_left.mp hBD hzB hzD
    have hFirst : p.1 = q.1 := by
      have hpMem : p.1 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq
      · exact hpq
      · exact (hzNotC (hpq ▸ hpC)).elim
      · exact (Finset.disjoint_left.mp hCD hpC (hpq ▸ hqD)).elim
    have hSecond : p.2 = q.2 := by
      have hpMem : p.2 ∈ starRow q := by
        rw [← hEq]
        simp [starRow]
      simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq
      · exact (Finset.disjoint_left.mp hCD (hpq ▸ hqC) hpD).elim
      · exact (hzNotD (hpq ▸ hpD)).elim
      · exact hpq
    exact Prod.ext hFirst hSecond
  have hImageSubset : choices.image starRow ⊆ blocker H := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hpC, hpD⟩ := Finset.mem_product.mp hp
    have hzA : z ∈ A := (Finset.mem_inter.mp hzAB).1
    have hzNotC : z ∉ C := fun hzC ↦ Finset.disjoint_left.mp hBC hzB hzC
    have hzNotD : z ∉ D := fun hzD ↦ Finset.disjoint_left.mp hBD hzB hzD
    apply mem_blocker.mpr
    have hTransversal : IsTransversal H (starRow p) := by
      intro E hEH
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hEH
      rcases hEH with rfl | rfl | rfl | rfl
      · exact ⟨z, by simp [starRow], hzA⟩
      · exact ⟨z, by simp [starRow], hzB⟩
      · exact ⟨p.1, by simp [starRow], hpC⟩
      · exact ⟨p.2, by simp [starRow], hpD⟩
    apply hTransversal.minimal_of_privateRows
    intro x hx
    simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨C, by simp [hH], by simp [starRow], hpC, by
        intro y hyRow hyC
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl
        · rfl
        · exact (hzNotC hyC).elim
        · exact (Finset.disjoint_left.mp hCD hyC hpD).elim⟩
    · exact ⟨B, by simp [hH], by simp [starRow], hzB, by
        intro y hyRow hyB
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hBC hyB hpC).elim
        · rfl
        · exact (Finset.disjoint_left.mp hBD hyB hpD).elim⟩
    · exact ⟨D, by simp [hH], by simp [starRow], hpD, by
        intro y hyRow hyD
        simp only [starRow, Finset.mem_insert, Finset.mem_singleton] at hyRow
        rcases hyRow with rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp hCD hpC hyD).elim
        · exact (hzNotD hyD).elim
        · rfl⟩
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hProduct : C.card * D.card ≤ (blocker H).card := by
    calc
      C.card * D.card = choices.card := by simp [choices, Finset.card_product]
      _ = (choices.image starRow).card :=
        (Finset.card_image_iff.mpr hInjective).symm
      _ ≤ (blocker H).card := Finset.card_le_card hImageSubset
  calc
    9 = 3 * 3 := rfl
    _ ≤ C.card * D.card := Nat.mul_le_mul (hRows C hCH) (hRows D hDH)
    _ ≤ (blocker H).card := hProduct

theorem opposite_intersections_not_both_nonempty {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D : Row α}
    (hH : H = {A, B, C, D})
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    ¬((A ∩ B).Nonempty ∧ (C ∩ D).Nonempty) := by
  rintro ⟨hAB, hCD⟩
  obtain ⟨x, hxAB⟩ := hAB
  obtain ⟨y, hyCD⟩ := hCD
  have hPairTransversal : IsTransversal H {x, y} := by
    intro E hEH
    simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hEH
    rcases hEH with rfl | rfl | rfl | rfl
    · exact ⟨x, by simp, (Finset.mem_inter.mp hxAB).1⟩
    · exact ⟨x, by simp, (Finset.mem_inter.mp hxAB).2⟩
    · exact ⟨y, by simp, (Finset.mem_inter.mp hyCD).1⟩
    · exact ⟨y, by simp, (Finset.mem_inter.mp hyCD).2⟩
  obtain ⟨T, hTPair, hTMinimal⟩ := exists_minimalTransversal_subset hPairTransversal
  have hTupper : T.card ≤ 2 :=
    (Finset.card_le_card hTPair).trans Finset.card_le_two
  have hTlower := hBRows T (mem_blocker.mpr hTMinimal)
  omega

theorem fourLargeRows_blocker_card_ge_nine {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hHclutter : IsClutter H) (hHcard : H.card = 4)
    (hRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    9 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, D, hABne, hACne, hADne, hBCne, hBDne, hCDne, hH⟩ :=
    Finset.card_eq_four.mp hHcard
  let ab : Prop := (A ∩ B).Nonempty
  let ac : Prop := (A ∩ C).Nonempty
  let ad : Prop := (A ∩ D).Nonempty
  let bc : Prop := (B ∩ C).Nonempty
  let bd : Prop := (B ∩ D).Nonempty
  let cd : Prop := (C ∩ D).Nonempty
  have hABCD : ¬(ab ∧ cd) := opposite_intersections_not_both_nonempty hH hBRows
  have hACBD : ¬(ac ∧ bd) := opposite_intersections_not_both_nonempty
    (by
      rw [hH]
      ext T
      simp [or_left_comm]) hBRows
  have hADBC : ¬(ad ∧ bc) := opposite_intersections_not_both_nonempty
    (by
      rw [hH]
      ext T
      simp [or_comm, or_left_comm]) hBRows
  have hHB : H = {B, A, C, D} := by
    calc
      H = {A, B, C, D} := hH
      _ = {B, A, C, D} := by
        ext T
        simp [or_left_comm]
  have hHC : H = {C, A, B, D} := by
    calc
      H = {A, B, C, D} := hH
      _ = {C, A, B, D} := by
        ext T
        simp [or_left_comm]
  have hHD : H = {D, A, B, C} := by
    calc
      H = {A, B, C, D} := hH
      _ = {D, A, B, C} := by
        ext T
        simp [or_comm, or_left_comm]
  have isolatedA (h : ¬ab ∧ ¬ac ∧ ¬ad) : 9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_isolated hHclutter hH hRows
      (disjoint_of_inter_not_nonempty h.1)
      (disjoint_of_inter_not_nonempty h.2.1)
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedB (h : ¬ab ∧ ¬bc ∧ ¬bd) : 9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_isolated
      (A := B) (B := A) (C := C) (D := D) hHclutter hHB hRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1)
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedC (h : ¬ac ∧ ¬bc ∧ ¬cd) : 9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_isolated
      (A := C) (B := A) (C := B) (D := D) hHclutter hHC hRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1).symm
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedD (h : ¬ad ∧ ¬bd ∧ ¬cd) : 9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_isolated
      (A := D) (B := A) (C := B) (D := C) hHclutter hHD hRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1).symm
      (disjoint_of_inter_not_nonempty h.2.2).symm
  have starA (hab : ab) (hbc : ¬bc) (hbd : ¬bd) (hcd : ¬cd) :
      9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_star hH hRows hab
      (disjoint_of_inter_not_nonempty hbc)
      (disjoint_of_inter_not_nonempty hbd)
      (disjoint_of_inter_not_nonempty hcd)
  have starB (hab : ab) (hac : ¬ac) (had : ¬ad) (hcd : ¬cd) :
      9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_star
      (A := B) (B := A) (C := C) (D := D) hHB hRows
      (by simpa [ab, Finset.inter_comm] using hab)
      (disjoint_of_inter_not_nonempty hac)
      (disjoint_of_inter_not_nonempty had)
      (disjoint_of_inter_not_nonempty hcd)
  have starC (hac : ac) (hab : ¬ab) (had : ¬ad) (hbd : ¬bd) :
      9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_star
      (A := C) (B := A) (C := B) (D := D) hHC hRows
      (by simpa [ac, Finset.inter_comm] using hac)
      (disjoint_of_inter_not_nonempty hab)
      (disjoint_of_inter_not_nonempty had)
      (disjoint_of_inter_not_nonempty hbd)
  have starD (had : ad) (hab : ¬ab) (hac : ¬ac) (hbc : ¬bc) :
      9 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_nine_of_first_star
      (A := D) (B := A) (C := B) (D := C) hHD hRows
      (by simpa [ad, Finset.inter_comm] using had)
      (disjoint_of_inter_not_nonempty hab)
      (disjoint_of_inter_not_nonempty hac)
      (disjoint_of_inter_not_nonempty hbc)
  by_cases hAiso : ¬ab ∧ ¬ac ∧ ¬ad
  · exact isolatedA hAiso
  by_cases hBiso : ¬ab ∧ ¬bc ∧ ¬bd
  · exact isolatedB hBiso
  by_cases hCiso : ¬ac ∧ ¬bc ∧ ¬cd
  · exact isolatedC hCiso
  by_cases hDiso : ¬ad ∧ ¬bd ∧ ¬cd
  · exact isolatedD hDiso
  have hAneighbor : ab ∨ ac ∨ ad := by
    by_contra hnot
    push Not at hnot
    exact hAiso hnot
  have hBneighbor : ab ∨ bc ∨ bd := by
    by_contra hnot
    push Not at hnot
    exact hBiso hnot
  have hCneighbor : ac ∨ bc ∨ cd := by
    by_contra hnot
    push Not at hnot
    exact hCiso hnot
  have hDneighbor : ad ∨ bd ∨ cd := by
    by_contra hnot
    push Not at hnot
    exact hDiso hnot
  by_cases hab : ab
  · have hcd : ¬cd := fun hcd ↦ hABCD ⟨hab, hcd⟩
    rcases hCneighbor with hac | hbc | hcd'
    · have hbd : ¬bd := fun hbd ↦ hACBD ⟨hac, hbd⟩
      have had : ad := by
        rcases hDneighbor with had | hbd' | hcd'
        · exact had
        · exact (hbd hbd').elim
        · exact (hcd hcd').elim
      have hbc : ¬bc := fun hbc ↦ hADBC ⟨had, hbc⟩
      exact starA hab hbc hbd hcd
    · have had : ¬ad := fun had ↦ hADBC ⟨had, hbc⟩
      have hbd : bd := by
        rcases hDneighbor with had' | hbd | hcd'
        · exact (had had').elim
        · exact hbd
        · exact (hcd hcd').elim
      have hac : ¬ac := fun hac ↦ hACBD ⟨hac, hbd⟩
      exact starB hab hac had hcd
    · exact (hcd hcd').elim
  · by_cases hac : ac
    · have hbd : ¬bd := fun hbd ↦ hACBD ⟨hac, hbd⟩
      have hbc : bc := by
        rcases hBneighbor with hab' | hbc | hbd'
        · exact (hab hab').elim
        · exact hbc
        · exact (hbd hbd').elim
      have had : ¬ad := fun had ↦ hADBC ⟨had, hbc⟩
      have hcd : cd := by
        rcases hDneighbor with had' | hbd' | hcd
        · exact (had had').elim
        · exact (hbd hbd').elim
        · exact hcd
      exact starC hac hab had hbd
    · have had : ad := by
        rcases hAneighbor with hab' | hac' | had
        · exact (hab hab').elim
        · exact (hac hac').elim
        · exact had
      have hbc : ¬bc := fun hbc ↦ hADBC ⟨had, hbc⟩
      have hbd : bd := by
        rcases hBneighbor with hab' | hbc' | hbd
        · exact (hab hab').elim
        · exact (hbc hbc').elim
        · exact hbd
      have hcd : cd := by
        rcases hCneighbor with hac' | hbc' | hcd
        · exact (hac hac').elim
        · exact (hbc hbc').elim
        · exact hcd
      exact starD had hab hac hbc

end AiMathLab.P0054.G413
