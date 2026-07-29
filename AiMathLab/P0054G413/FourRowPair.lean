import AiMathLab.P0054G413.FourRows

namespace AiMathLab.P0054.G413

theorem minimize_eq_self_of_isClutter {α : Type*} {H : Hypergraph α}
    (hH : IsClutter H) : minimize H = H := by
  ext E
  constructor
  · intro hE
    exact minimize_subset H hE
  · intro hEH
    exact mem_minimize.mpr ⟨hEH, fun F hFH hFE ↦ hH hFH hEH hFE ▸ Finset.Subset.rfl⟩

theorem false_of_two_point_transversal {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hPairTransversal : IsTransversal H {p, q}) : False := by
  obtain ⟨T, hTPair, hTMinimal⟩ := exists_minimalTransversal_subset hPairTransversal
  have hTupper : T.card ≤ 2 :=
    (Finset.card_le_card hTPair).trans Finset.card_le_two
  have hTlower := hBRows T (mem_blocker.mpr hTMinimal)
  omega

noncomputable def pairSide {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (p q : α) : Hypergraph α :=
  residual (avoidPoint H p) q

theorem pairSide_rows_avoid_first {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (p q : α) :
    ∀ E ∈ pairSide H p q, p ∉ E := by
  classical
  intro E hE hpE
  have hEdelete : E ∈ deletePoint (avoidPoint H p) q :=
    minimize_subset _ hE
  obtain ⟨A, hAavoid, hAerase⟩ := Finset.mem_image.mp hEdelete
  have hpA : p ∉ A := (mem_avoidPoint.mp hAavoid).2
  have hpErase : p ∈ A.erase q := hAerase ▸ hpE
  exact hpA (Finset.mem_of_mem_erase hpErase)

theorem pairSide_rows_avoid_second {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (p q : α) :
    ∀ E ∈ pairSide H p q, q ∉ E := by
  intro E hE
  exact deletePoint_rows_avoid (minimize_subset _ hE)

theorem pairSide_rows_nonempty {α : Type*} [DecidableEq α]
    {H : Hypergraph α} (hHRows : RowsCardAtLeast H 2) (p q : α) :
    RowsNonempty (pairSide H p q) := by
  have hAvoidRows : RowsCardAtLeast (avoidPoint H p) 2 := by
    intro E hE
    exact hHRows E (mem_avoidPoint.mp hE).1
  have hResidualRows := residual_rows_cardAtLeast hAvoidRows q
  intro E hE
  exact Finset.card_pos.mp (by simpa [pairSide] using hResidualRows E hE)

theorem pairSide_blocker_lift {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {D : Row α}
    (hPair : ({p, q} : Row α) ∈ H)
    (hD : D ∈ blocker (pairSide H p q)) :
    insert p D ∈ blocker H := by
  have hResidual := blocker_residual (avoidPoint H p) q
  have hDavoid : D ∈ avoidPoint (blocker (avoidPoint H p)) q := by
    rw [← hResidual]
    exact hD
  obtain ⟨hDbase, hqD⟩ := mem_avoidPoint.mp hDavoid
  have hpD : p ∉ D :=
    blocker_rows_avoid_inactive
      (H := avoidPoint H p) (by intro E hE; exact (mem_avoidPoint.mp hE).2) D hDbase
  apply mem_blocker.mpr
  have hTransversal : IsTransversal H (insert p D) := by
    intro E hEH
    by_cases hpE : p ∈ E
    · exact ⟨p, by simp, hpE⟩
    · obtain ⟨x, hxD, hxE⟩ :=
        (mem_blocker.mp hDbase).prop E (mem_avoidPoint.mpr ⟨hEH, hpE⟩)
      exact ⟨x, by simp [hxD], hxE⟩
  apply hTransversal.minimal_of_privateRows
  intro x hx
  simp only [Finset.mem_insert] at hx
  rcases hx with hxp | hxD
  · subst x
    refine ⟨{p, q}, hPair, by simp, by simp, ?_⟩
    intro y hyRow hyPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyRow hyPair
    rcases hyRow with rfl | hyD
    · rfl
    · rcases hyPair with rfl | rfl
      · exact (hpD hyD).elim
      · exact (hqD hyD).elim
  · obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hDbase).exists_privateRow hxD
    obtain ⟨hEavoid, hxD', hxE, hUnique⟩ := hPrivate
    obtain ⟨hEH, hpE⟩ := mem_avoidPoint.mp hEavoid
    refine ⟨E, hEH, by simp [hxD'], hxE, ?_⟩
    intro y hyRow hyE
    simp only [Finset.mem_insert] at hyRow
    rcases hyRow with rfl | hyD
    · exact (hpE hyE).elim
    · exact hUnique hyD hyE

theorem pairSide_blocker_rows_cardAtLeast_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hPair : ({p, q} : Row α) ∈ H)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    RowsCardAtLeast (blocker (pairSide H p q)) 2 := by
  intro D hD
  have hLift := pairSide_blocker_lift hPair hD
  have hpD : p ∉ D :=
    (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H p q)
  have hLarge := hBRows (insert p D) hLift
  rw [Finset.card_insert_of_notMem hpD] at hLarge
  omega

theorem pairSide_blocker_card_add_le {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} (hpq : p ≠ q)
    (hPair : ({p, q} : Row α) ∈ H) :
    (blocker (pairSide H p q)).card +
        (blocker (pairSide H q p)).card ≤ (blocker H).card := by
  let liftP : Row α → Row α := insert p
  let liftQ : Row α → Row α := insert q
  let left : Hypergraph α := (blocker (pairSide H p q)).image liftP
  let right : Hypergraph α := (blocker (pairSide H q p)).image liftQ
  have hLeftSubset : left ⊆ blocker H := by
    intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    exact pairSide_blocker_lift hPair hD
  have hRightSubset : right ⊆ blocker H := by
    intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    simpa [Finset.pair_comm] using
      (pairSide_blocker_lift (H := H) (p := q) (q := p) (D := D)
        (by simpa [Finset.pair_comm] using hPair) hD)
  have hLiftPInjective : Set.InjOn liftP (↑(blocker (pairSide H p q)) : Set (Row α)) := by
    intro D hD F hF hEq
    have hpD : p ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H p q)
    have hpF : p ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_first H p q)
    simpa [liftP, hpD, hpF] using congrArg (Finset.erase · p) hEq
  have hLiftQInjective : Set.InjOn liftQ (↑(blocker (pairSide H q p)) : Set (Row α)) := by
    intro D hD F hF hEq
    have hqD : q ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H q p)
    have hqF : q ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_first H q p)
    simpa [liftQ, hqD, hqF] using congrArg (Finset.erase · q) hEq
  have hDisjoint : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro T hTleft hTright
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hTleft
    obtain ⟨F, hF, hEq⟩ := Finset.mem_image.mp hTright
    have hqD : q ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H p q)
    have hpF : p ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_second H q p)
    have hpRight : p ∈ liftQ F := by
      rw [hEq]
      simp only [liftP]
      exact Finset.mem_insert_self p D
    simp only [liftQ, Finset.mem_insert] at hpRight
    rcases hpRight with hpq' | hpF'
    · exact hpq hpq'
    · exact hpF hpF'
  calc
    (blocker (pairSide H p q)).card + (blocker (pairSide H q p)).card =
        left.card + right.card := by
      rw [Finset.card_image_iff.mpr hLiftPInjective,
        Finset.card_image_iff.mpr hLiftQInjective]
    _ = (left ∪ right).card := (Finset.card_union_of_disjoint hDisjoint).symm
    _ ≤ (blocker H).card := Finset.card_le_card (Finset.union_subset hLeftSubset hRightSubset)

theorem twoRow_blocker_card_ge_product {α : Type*}
    [Fintype α] [DecidableEq α]
    {A B : Row α}
    (hBRows : RowsCardAtLeast (blocker ({A, B} : Hypergraph α)) 2) :
    A.card * B.card ≤ (blocker ({A, B} : Hypergraph α)).card := by
  have hDisjoint : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hSingleton : ({x} : Row α) ∈ blocker ({A, B} : Hypergraph α) := by
      rw [blocker_pairFamily]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨x, hx, rfl⟩)
    have hLarge := hBRows {x} hSingleton
    simp at hLarge
  have hCrossSubset : crossPairRows A B ⊆ blocker ({A, B} : Hypergraph α) := by
    intro T hT
    obtain ⟨a, haA, b, hbB, rfl⟩ := mem_crossPairRows.mp hT
    rw [blocker_pairFamily]
    exact mem_twoRowBlockers.mpr (Or.inr
      ⟨a, Finset.mem_sdiff.mpr
          ⟨haA, fun haB ↦ Finset.disjoint_left.mp hDisjoint haA haB⟩,
        b, Finset.mem_sdiff.mpr
          ⟨hbB, fun hbA ↦ Finset.disjoint_left.mp hDisjoint hbA hbB⟩,
        rfl⟩)
  exact (card_mul_le_crossPairRows_card_of_disjoint hDisjoint).trans
    (Finset.card_le_card hCrossSubset)

theorem blocker_card_ge_two_of_atMostOne_singletonRow {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHnonempty : RowsNonempty H)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hSingleton : (rowsCardAtMost H 1).card ≤ 1) :
    2 ≤ (blocker H).card := by
  classical
  have hBpositive : 0 < (blocker H).card :=
    Finset.card_pos.mpr (blocker_nonempty hHnonempty)
  by_contra hnot
  have hBcard : (blocker H).card = 1 := by omega
  obtain ⟨Q, hBQ⟩ := Finset.card_eq_one.mp hBcard
  have hQb : Q ∈ blocker H := by simp [hBQ]
  have hQcard : 2 ≤ Q.card := hBRows Q hQb
  obtain ⟨q₁, hq₁Q, q₂, hq₂Q, hqNe⟩ := Finset.one_lt_card.mp hQcard
  have hHsingle : H = singletonRows Q :=
    family_eq_singletonRows_of_blocker_eq_singleton hH hBQ
  have hq₁H : ({q₁} : Row α) ∈ H := by
    rw [hHsingle]
    exact mem_singletonRows.mpr ⟨q₁, hq₁Q, rfl⟩
  have hq₂H : ({q₂} : Row α) ∈ H := by
    rw [hHsingle]
    exact mem_singletonRows.mpr ⟨q₂, hq₂Q, rfl⟩
  have hRowsSubset : ({{q₁}, {q₂}} : Hypergraph α) ⊆ rowsCardAtMost H 1 := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact mem_rowsCardAtMost.mpr ⟨hq₁H, by simp⟩
    · exact mem_rowsCardAtMost.mpr ⟨hq₂H, by simp⟩
  have hTwo := Finset.card_le_card hRowsSubset
  simpa [Finset.singleton_inj, hqNe] using hTwo.trans hSingleton

theorem fourRow_pair_bound_of_two_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X Z₁ Z₂ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X, Z₁, Z₂})
    (hHclutter : IsClutter H) (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX : p ∈ X) (hqX : q ∉ X)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂) :
    6 ≤ (blocker H).card := by
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hAvoidP : avoidPoint H p = {Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX).elim
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
  have hDeleteQ : deletePoint ({Z₁, Z₂} : Hypergraph α) q = {Z₁, Z₂} := by
    ext T
    simp [deletePoint, hqZ₁, hqZ₂]
  have hZclutter : IsClutter ({Z₁, Z₂} : Hypergraph α) := by
    apply hHclutter.mono
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hZ₁H
    · exact hZ₂H
  have hSideP : pairSide H p q = {Z₁, Z₂} := by
    rw [pairSide, residual, hAvoidP, hDeleteQ, minimize_eq_self_of_isClutter hZclutter]
  have hSidePBlockerRows := pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hSidePProduct : Z₁.card * Z₂.card ≤ (blocker (pairSide H p q)).card := by
    rw [hSideP]
    exact twoRow_blocker_card_ge_product (by simpa [hSideP] using hSidePBlockerRows)
  have hSidePFour : 4 ≤ (blocker (pairSide H p q)).card := by
    calc
      4 = 2 * 2 := rfl
      _ ≤ Z₁.card * Z₂.card := Nat.mul_le_mul (hHRows Z₁ hZ₁H) (hHRows Z₂ hZ₂H)
      _ ≤ (blocker (pairSide H p q)).card := hSidePProduct
  have hAvoidQ : avoidPoint H q = {X, Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨by simp [hH], hqX⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
  have hSideQSingleton : (rowsCardAtMost (pairSide H q p) 1).card ≤ 1 := by
    calc
      (rowsCardAtMost (pairSide H q p) 1).card ≤ ({X.erase p} : Hypergraph α).card := by
        apply Finset.card_le_card
        intro T hT
        obtain ⟨hTSide, hTcard⟩ := mem_rowsCardAtMost.mp hT
        have hTsource : T ∈ deletePoint (avoidPoint H q) p :=
          minimize_subset _ hTSide
        rw [hAvoidQ] at hTsource
        simp only [deletePoint, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at hTsource
        obtain ⟨A, hA, hAerase⟩ := hTsource
        rcases hA with hAX | hAZ₁ | hAZ₂
        · subst A
          simp [hAerase]
        · subst A
          have hZ₁card := hHRows Z₁ hZ₁H
          have hEq : T = Z₁ := by simpa [hpZ₁] using hAerase.symm
          rw [hEq] at hTcard
          omega
        · subst A
          have hZ₂card := hHRows Z₂ hZ₂H
          have hEq : T = Z₂ := by simpa [hpZ₂] using hAerase.symm
          rw [hEq] at hTcard
          omega
      _ = 1 := Finset.card_singleton _
  have hSideQTwo : 2 ≤ (blocker (pairSide H q p)).card :=
    blocker_card_ge_two_of_atMostOne_singletonRow
      (residual_isClutter _ _)
      (pairSide_rows_nonempty hHRows q p)
      (pairSide_blocker_rows_cardAtLeast_two
        (by simpa [Finset.pair_comm] using hPair) hBRows)
      hSideQSingleton
  have hSum := pairSide_blocker_card_add_le hpq hPair
  omega

theorem fourRow_pair_bound_of_three_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {Z₁ Z₂ Z₃ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, Z₁, Z₂, Z₃}) (hHcard : H.card = 4)
    (hHclutter : IsClutter H) (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂)
    (hpZ₃ : p ∉ Z₃) (hqZ₃ : q ∉ Z₃) :
    6 ≤ (blocker H).card := by
  let K : Hypergraph α := {Z₁, Z₂, Z₃}
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hZ₃H : Z₃ ∈ H := by simp [hH]
  have hKsubset : K ⊆ H := by
    intro T hT
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact hZ₁H
    · exact hZ₂H
    · exact hZ₃H
  have hKclutter : IsClutter K := hHclutter.mono hKsubset
  have hPairNotK : ({p, q} : Row α) ∉ K := by
    intro hPairK
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hPairK
    rcases hPairK with hEq | hEq | hEq
    · exact hpZ₁ (hEq ▸ (by simp))
    · exact hpZ₂ (hEq ▸ (by simp))
    · exact hpZ₃ (hEq ▸ (by simp))
  have hKcard : K.card = 3 := by
    rw [hH] at hHcard
    rw [Finset.card_insert_of_notMem hPairNotK] at hHcard
    omega
  have hKRows : RowsCardAtLeast K 2 := by
    intro T hT
    exact hHRows T (hKsubset hT)
  have hKPairRows : (pairRows K).card ≤ 2 := by
    by_contra hnot
    have hPairCard : (pairRows K).card = 3 := by
      have hSubset : pairRows K ⊆ K := by
        intro E hE
        exact (Finset.mem_filter.mp hE).1
      have hUpper := Finset.card_le_card hSubset
      omega
    have hPairSubset : pairRows K ⊆ K := by
      intro E hE
      exact (Finset.mem_filter.mp hE).1
    have hAllPairs : pairRows K = K :=
      Finset.eq_of_subset_of_card_le hPairSubset (by omega)
    have hZ₁K : Z₁ ∈ K := by simp [K]
    have hZ₂K : Z₂ ∈ K := by simp [K]
    have hZ₃K : Z₃ ∈ K := by simp [K]
    have hZ₁Pair : Z₁.card = 2 := by
      have : Z₁ ∈ pairRows K := by simpa [hAllPairs] using hZ₁K
      exact (Finset.mem_filter.mp this).2
    have hZ₂Pair : Z₂.card = 2 := by
      have : Z₂ ∈ pairRows K := by simpa [hAllPairs] using hZ₂K
      exact (Finset.mem_filter.mp this).2
    have hZ₃Pair : Z₃.card = 2 := by
      have : Z₃ ∈ pairRows K := by simpa [hAllPairs] using hZ₃K
      exact (Finset.mem_filter.mp this).2
    have hAllH : H ⊆ pairRows H := by
      intro T hT
      apply Finset.mem_filter.mpr
      refine ⟨hT, ?_⟩
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · simp [hpq]
      · exact hZ₁Pair
      · exact hZ₂Pair
      · exact hZ₃Pair
    have hFour := Finset.card_le_card hAllH
    omega
  have hAvoidP : avoidPoint H p = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₃H, hpZ₃⟩
  have hAvoidQ : avoidPoint H q = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₃H, hqZ₃⟩
  have hDeleteQ : deletePoint K q = K := by
    ext T
    simp [deletePoint, K, hqZ₁, hqZ₂, hqZ₃]
  have hDeleteP : deletePoint K p = K := by
    ext T
    simp [deletePoint, K, hpZ₁, hpZ₂, hpZ₃]
  have hSideP : pairSide H p q = K := by
    rw [pairSide, residual, hAvoidP, hDeleteQ, minimize_eq_self_of_isClutter hKclutter]
  have hSideQ : pairSide H q p = K := by
    rw [pairSide, residual, hAvoidQ, hDeleteP, minimize_eq_self_of_isClutter hKclutter]
  have hKBlockerRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hSideP] using pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hKFour : 4 ≤ (blocker K).card :=
    threeRow_blocker_card_ge_four_of_pairRows_card_le_two
      hKclutter hKcard hKRows hKBlockerRows hKPairRows
  have hSum := pairSide_blocker_card_add_le hpq hPair
  rw [hSideP, hSideQ] at hSum
  omega

theorem fourRow_pair_bound_of_one_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X Y Z : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X, Y, Z}) (hHcard : H.card = 4)
    (hHclutter : IsClutter H) (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX : p ∈ X) (hqX : q ∉ X)
    (hpY : p ∉ Y) (hqY : q ∈ Y)
    (hpZ : p ∉ Z) (hqZ : q ∉ Z) :
    6 ≤ (blocker H).card := by
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hPairQP : ({q, p} : Row α) ∈ H := by simpa [Finset.pair_comm] using hPair
  have hXH : X ∈ H := by simp [hH]
  have hYH : Y ∈ H := by simp [hH]
  have hZH : Z ∈ H := by simp [hH]
  have hXcard := hHRows X hXH
  have hYcard := hHRows Y hYH
  have hZcard := hHRows Z hZH
  have hXerasePositive : 1 ≤ (X.erase p).card := by
    rw [Finset.card_erase_of_mem hpX]
    omega
  have hYerasePositive : 1 ≤ (Y.erase q).card := by
    rw [Finset.card_erase_of_mem hqY]
    omega
  have hYeraseNotSubset : ¬Y.erase q ⊆ Z := by
    intro hSubset
    obtain ⟨y, hyErase⟩ := Finset.card_pos.mp hYerasePositive
    apply false_of_two_point_transversal (p := p) (q := y) hBRows
    intro T hTH
    simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
    rcases hTH with rfl | rfl | rfl | rfl
    · exact ⟨p, by simp, by simp⟩
    · exact ⟨p, by simp, hpX⟩
    · exact ⟨y, by simp, Finset.mem_of_mem_erase hyErase⟩
    · exact ⟨y, by simp, hSubset hyErase⟩
  have hZNotSubsetYerase : ¬Z ⊆ Y.erase q := by
    intro hSubset
    have hZY : Z ⊆ Y := fun _ hz ↦ Finset.mem_of_mem_erase (hSubset hz)
    have hEq : Z = Y := hHclutter hZH hYH hZY
    exact hqZ (hEq ▸ hqY)
  have hXeraseNotSubset : ¬X.erase p ⊆ Z := by
    intro hSubset
    obtain ⟨x, hxErase⟩ := Finset.card_pos.mp hXerasePositive
    apply false_of_two_point_transversal (p := q) (q := x) hBRows
    intro T hTH
    simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
    rcases hTH with rfl | rfl | rfl | rfl
    · exact ⟨q, by simp, by simp⟩
    · exact ⟨x, by simp, Finset.mem_of_mem_erase hxErase⟩
    · exact ⟨q, by simp, hqY⟩
    · exact ⟨x, by simp, hSubset hxErase⟩
  have hZNotSubsetXerase : ¬Z ⊆ X.erase p := by
    intro hSubset
    have hZX : Z ⊆ X := fun _ hz ↦ Finset.mem_of_mem_erase (hSubset hz)
    have hEq : Z = X := hHclutter hZH hXH hZX
    exact hpZ (hEq ▸ hpX)
  have hLeftClutter : IsClutter ({Y.erase q, Z} : Hypergraph α) := by
    intro A hA B hB hAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · rfl
    · exact (hYeraseNotSubset hAB).elim
    · exact (hZNotSubsetYerase hAB).elim
    · rfl
  have hRightClutter : IsClutter ({X.erase p, Z} : Hypergraph α) := by
    intro A hA B hB hAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · rfl
    · exact (hXeraseNotSubset hAB).elim
    · exact (hZNotSubsetXerase hAB).elim
    · rfl
  have hAvoidP : avoidPoint H p = {Y, Z} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX).elim
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hYH, hpY⟩
      · exact mem_avoidPoint.mpr ⟨hZH, hpZ⟩
  have hAvoidQ : avoidPoint H q = {X, Z} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · exact (hqT hqY).elim
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hXH, hqX⟩
      · exact mem_avoidPoint.mpr ⟨hZH, hqZ⟩
  have hDeleteQ : deletePoint ({Y, Z} : Hypergraph α) q = {Y.erase q, Z} := by
    ext T
    simp [deletePoint, hqZ]
  have hDeleteP : deletePoint ({X, Z} : Hypergraph α) p = {X.erase p, Z} := by
    ext T
    simp [deletePoint, hpZ]
  have hSideP : pairSide H p q = {Y.erase q, Z} := by
    rw [pairSide, residual, hAvoidP, hDeleteQ,
      minimize_eq_self_of_isClutter hLeftClutter]
  have hSideQ : pairSide H q p = {X.erase p, Z} := by
    rw [pairSide, residual, hAvoidQ, hDeleteP,
      minimize_eq_self_of_isClutter hRightClutter]
  have hSidePBlockerRows :
      RowsCardAtLeast (blocker ({Y.erase q, Z} : Hypergraph α)) 2 := by
    have hRows := pairSide_blocker_rows_cardAtLeast_two hPair hBRows
    rw [hSideP] at hRows
    exact hRows
  have hSideQBlockerRows :
      RowsCardAtLeast (blocker ({X.erase p, Z} : Hypergraph α)) 2 := by
    have hRows := pairSide_blocker_rows_cardAtLeast_two hPairQP hBRows
    rw [hSideQ] at hRows
    exact hRows
  have hSidePProduct :
      (Y.erase q).card * Z.card ≤ (blocker (pairSide H p q)).card := by
    rw [hSideP]
    exact twoRow_blocker_card_ge_product hSidePBlockerRows
  have hSideQProduct :
      (X.erase p).card * Z.card ≤ (blocker (pairSide H q p)).card := by
    rw [hSideQ]
    exact twoRow_blocker_card_ge_product hSideQBlockerRows
  have hZThreeOfBothPairs (hXPair : X.card = 2) (hYPair : Y.card = 2) :
      3 ≤ Z.card := by
    by_contra hnot
    have hZPair : Z.card = 2 := by omega
    have hAllH : H ⊆ pairRows H := by
      intro T hT
      apply Finset.mem_filter.mpr
      refine ⟨hT, ?_⟩
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · simp [hpq]
      · exact hXPair
      · exact hYPair
      · exact hZPair
    have hFour := Finset.card_le_card hAllH
    omega
  have hSum := pairSide_blocker_card_add_le hpq hPair
  by_cases hXPair : X.card = 2
  · by_cases hYPair : Y.card = 2
    · have hZThree := hZThreeOfBothPairs hXPair hYPair
      have hPThree : 3 ≤ (blocker (pairSide H p q)).card := by
        exact (Nat.mul_le_mul hYerasePositive hZThree).trans hSidePProduct
      have hQThree : 3 ≤ (blocker (pairSide H q p)).card := by
        exact (Nat.mul_le_mul hXerasePositive hZThree).trans hSideQProduct
      omega
    · have hYeraseTwo : 2 ≤ (Y.erase q).card := by
        rw [Finset.card_erase_of_mem hqY]
        omega
      have hPFour : 4 ≤ (blocker (pairSide H p q)).card := by
        calc
          4 = 2 * 2 := rfl
          _ ≤ (Y.erase q).card * Z.card := Nat.mul_le_mul hYeraseTwo hZcard
          _ ≤ (blocker (pairSide H p q)).card := hSidePProduct
      have hQTwo : 2 ≤ (blocker (pairSide H q p)).card := by
        exact (Nat.mul_le_mul hXerasePositive hZcard).trans hSideQProduct
      omega
  · have hXeraseTwo : 2 ≤ (X.erase p).card := by
      rw [Finset.card_erase_of_mem hpX]
      omega
    by_cases hYPair : Y.card = 2
    · have hPTwo : 2 ≤ (blocker (pairSide H p q)).card := by
        exact (Nat.mul_le_mul hYerasePositive hZcard).trans hSidePProduct
      have hQFour : 4 ≤ (blocker (pairSide H q p)).card := by
        calc
          4 = 2 * 2 := rfl
          _ ≤ (X.erase p).card * Z.card := Nat.mul_le_mul hXeraseTwo hZcard
          _ ≤ (blocker (pairSide H q p)).card := hSideQProduct
      omega
    · have hYeraseTwo : 2 ≤ (Y.erase q).card := by
        rw [Finset.card_erase_of_mem hqY]
        omega
      have hPFour : 4 ≤ (blocker (pairSide H p q)).card := by
        calc
          4 = 2 * 2 := rfl
          _ ≤ (Y.erase q).card * Z.card := Nat.mul_le_mul hYeraseTwo hZcard
          _ ≤ (blocker (pairSide H p q)).card := hSidePProduct
      have hQFour : 4 ≤ (blocker (pairSide H q p)).card := by
        calc
          4 = 2 * 2 := rfl
          _ ≤ (X.erase p).card * Z.card := Nat.mul_le_mul hXeraseTwo hZcard
          _ ≤ (blocker (pairSide H q p)).card := hSideQProduct
      omega

theorem false_of_fourRow_pair_no_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {A B C : Row α}
    (hH : H = {{p, q}, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hA : p ∈ A ∨ q ∈ A) (hB : p ∈ B ∨ q ∈ B) (hC : p ∈ C ∨ q ∈ C) :
    False := by
  apply false_of_two_point_transversal (p := p) (q := q) hBRows
  intro T hTH
  simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
  rcases hTH with rfl | rfl | rfl | rfl
  · exact ⟨p, by simp, by simp⟩
  · rcases hA with hpA | hqA
    · exact ⟨p, by simp, hpA⟩
    · exact ⟨q, by simp, hqA⟩
  · rcases hB with hpB | hqB
    · exact ⟨p, by simp, hpB⟩
    · exact ⟨q, by simp, hqB⟩
  · rcases hC with hpC | hqC
    · exact ⟨p, by simp, hpC⟩
    · exact ⟨q, by simp, hqC⟩

theorem false_of_fourRow_pair_one_avoiding_same_side {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X₁ X₂ Z : Row α}
    (hH : H = {{p, q}, X₁, X₂, Z})
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX₁ : p ∈ X₁) (hpX₂ : p ∈ X₂) (hpZ : p ∉ Z) (hqZ : q ∉ Z) :
    False := by
  have hZH : Z ∈ H := by simp [hH]
  have hZpositive : 0 < Z.card := by have := hHRows Z hZH; omega
  obtain ⟨z, hzZ⟩ := Finset.card_pos.mp hZpositive
  apply false_of_two_point_transversal (p := p) (q := z) hBRows
  intro T hTH
  simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
  rcases hTH with rfl | rfl | rfl | rfl
  · exact ⟨p, by simp, by simp⟩
  · exact ⟨p, by simp, hpX₁⟩
  · exact ⟨p, by simp, hpX₂⟩
  · exact ⟨z, by simp, hzZ⟩

theorem fourRow_pair_residual_bound {α : Type*}
    [Fintype α]
    (H : Hypergraph α)
    (hHclutter : IsClutter H) (hHcard : H.card = 4)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hPairExists : ∃ E ∈ H, E.card = 2) :
    6 ≤ (blocker H).card := by
  classical
  obtain ⟨E, hEH, hEcard⟩ := hPairExists
  obtain ⟨p, q, hpq, hE⟩ := Finset.card_eq_two.mp hEcard
  subst E
  have hEraseCard : (H.erase {p, q}).card = 3 := by
    rw [Finset.card_erase_of_mem hEH]
    omega
  obtain ⟨A, B, C, hAB, hAC, hBC, hErase⟩ := Finset.card_eq_three.mp hEraseCard
  have hHform : H = {{p, q}, A, B, C} := by
    calc
      H = insert {p, q} (H.erase {p, q}) := (Finset.insert_erase hEH).symm
      _ = {{p, q}, A, B, C} := by rw [hErase]
  have hAerase : A ∈ H.erase {p, q} := by simp [hErase]
  have hBerase : B ∈ H.erase {p, q} := by simp [hErase]
  have hCerase : C ∈ H.erase {p, q} := by simp [hErase]
  have hANe : A ≠ ({p, q} : Row α) := (Finset.mem_erase.mp hAerase).1
  have hBNe : B ≠ ({p, q} : Row α) := (Finset.mem_erase.mp hBerase).1
  have hCNe : C ≠ ({p, q} : Row α) := (Finset.mem_erase.mp hCerase).1
  have hAH : A ∈ H := (Finset.mem_erase.mp hAerase).2
  have hBH : B ∈ H := (Finset.mem_erase.mp hBerase).2
  have hCH : C ∈ H := (Finset.mem_erase.mp hCerase).2
  have hNoBothA : ¬(p ∈ A ∧ q ∈ A) := by
    rintro ⟨hpA, hqA⟩
    have hSubset : ({p, q} : Row α) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpA
      · exact hqA
    exact hANe (hHclutter hEH hAH hSubset).symm
  have hNoBothB : ¬(p ∈ B ∧ q ∈ B) := by
    rintro ⟨hpB, hqB⟩
    have hSubset : ({p, q} : Row α) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpB
      · exact hqB
    exact hBNe (hHclutter hEH hBH hSubset).symm
  have hNoBothC : ¬(p ∈ C ∧ q ∈ C) := by
    rintro ⟨hpC, hqC⟩
    have hSubset : ({p, q} : Row α) ⊆ C := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpC
      · exact hqC
    exact hCNe (hHclutter hEH hCH hSubset).symm
  have hAClass :
      (p ∈ A ∧ q ∉ A) ∨ (p ∉ A ∧ q ∈ A) ∨ (p ∉ A ∧ q ∉ A) := by
    by_cases hpA : p ∈ A
    · exact Or.inl ⟨hpA, fun hqA ↦ hNoBothA ⟨hpA, hqA⟩⟩
    · by_cases hqA : q ∈ A
      · exact Or.inr (Or.inl ⟨hpA, hqA⟩)
      · exact Or.inr (Or.inr ⟨hpA, hqA⟩)
  have hBClass :
      (p ∈ B ∧ q ∉ B) ∨ (p ∉ B ∧ q ∈ B) ∨ (p ∉ B ∧ q ∉ B) := by
    by_cases hpB : p ∈ B
    · exact Or.inl ⟨hpB, fun hqB ↦ hNoBothB ⟨hpB, hqB⟩⟩
    · by_cases hqB : q ∈ B
      · exact Or.inr (Or.inl ⟨hpB, hqB⟩)
      · exact Or.inr (Or.inr ⟨hpB, hqB⟩)
  have hCClass :
      (p ∈ C ∧ q ∉ C) ∨ (p ∉ C ∧ q ∈ C) ∨ (p ∉ C ∧ q ∉ C) := by
    by_cases hpC : p ∈ C
    · exact Or.inl ⟨hpC, fun hqC ↦ hNoBothC ⟨hpC, hqC⟩⟩
    · by_cases hqC : q ∈ C
      · exact Or.inr (Or.inl ⟨hpC, hqC⟩)
      · exact Or.inr (Or.inr ⟨hpC, hqC⟩)
  rcases hAClass with hAX | hAY | hAZ
  · rcases hBClass with hBX | hBY | hBZ
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inl hAX.1) (Or.inl hBX.1) (Or.inl hCX.1)).elim
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inl hAX.1) (Or.inl hBX.1) (Or.inr hCY.2)).elim
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          hHform hHRows hBRows hAX.1 hBX.1 hCZ.1 hCZ.2).elim
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inl hAX.1) (Or.inr hBY.2) (Or.inl hCX.1)).elim
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inl hAX.1) (Or.inr hBY.2) (Or.inr hCY.2)).elim
      · exact fourRow_pair_bound_of_one_avoiding hpq hHform hHcard hHclutter
          hHRows hPairRows hBRows hAX.1 hAX.2 hBY.1 hBY.2 hCZ.1 hCZ.2
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          (by
            rw [hHform]
            ext T
            simp [or_comm])
          hHRows hBRows hAX.1 hCX.1 hBZ.1 hBZ.2).elim
      · exact fourRow_pair_bound_of_one_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm])
          hHcard hHclutter hHRows hPairRows hBRows
          hAX.1 hAX.2 hCY.1 hCY.2 hBZ.1 hBZ.2
      · exact fourRow_pair_bound_of_two_avoiding hpq hHform hHclutter hHRows hBRows
          hAX.1 hAX.2 hBZ.1 hBZ.2 hCZ.1 hCZ.2
  · rcases hBClass with hBX | hBY | hBZ
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inr hAY.2) (Or.inl hBX.1) (Or.inl hCX.1)).elim
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inr hAY.2) (Or.inl hBX.1) (Or.inr hCY.2)).elim
      · exact fourRow_pair_bound_of_one_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHcard hHclutter hHRows hPairRows hBRows
          hBX.1 hBX.2 hAY.1 hAY.2 hCZ.1 hCZ.2
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inr hAY.2) (Or.inr hBY.2) (Or.inl hCX.1)).elim
      · exact (false_of_fourRow_pair_no_avoiding hHform hBRows
          (Or.inr hAY.2) (Or.inr hBY.2) (Or.inr hCY.2)).elim
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          (p := q) (q := p)
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm])
          hHRows hBRows hAY.2 hBY.2 hCZ.2 hCZ.1).elim
    · rcases hCClass with hCX | hCY | hCZ
      · exact fourRow_pair_bound_of_one_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHcard hHclutter hHRows hPairRows hBRows
          hCX.1 hCX.2 hAY.1 hAY.2 hBZ.1 hBZ.2
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          (p := q) (q := p)
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm])
          hHRows hBRows hAY.2 hCY.2 hBZ.2 hBZ.1).elim
      · exact fourRow_pair_bound_of_two_avoiding hpq.symm
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm])
          hHclutter hHRows hBRows hAY.2 hAY.1 hBZ.2 hBZ.1 hCZ.2 hCZ.1
  · rcases hBClass with hBX | hBY | hBZ
    · rcases hCClass with hCX | hCY | hCZ
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHRows hBRows hBX.1 hCX.1 hAZ.1 hAZ.2).elim
      · exact fourRow_pair_bound_of_one_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHcard hHclutter hHRows hPairRows hBRows
          hBX.1 hBX.2 hCY.1 hCY.2 hAZ.1 hAZ.2
      · exact fourRow_pair_bound_of_two_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHclutter hHRows hBRows hBX.1 hBX.2 hAZ.1 hAZ.2 hCZ.1 hCZ.2
    · rcases hCClass with hCX | hCY | hCZ
      · exact fourRow_pair_bound_of_one_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHcard hHclutter hHRows hPairRows hBRows
          hCX.1 hCX.2 hBY.1 hBY.2 hAZ.1 hAZ.2
      · exact (false_of_fourRow_pair_one_avoiding_same_side
          (p := q) (q := p)
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm, or_left_comm])
          hHRows hBRows hBY.2 hCY.2 hAZ.2 hAZ.1).elim
      · exact fourRow_pair_bound_of_two_avoiding hpq.symm
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm, or_left_comm])
          hHclutter hHRows hBRows hBY.2 hBY.1 hAZ.2 hAZ.1 hCZ.2 hCZ.1
    · rcases hCClass with hCX | hCY | hCZ
      · exact fourRow_pair_bound_of_two_avoiding hpq
          (by
            rw [hHform]
            ext T
            simp [or_comm, or_left_comm])
          hHclutter hHRows hBRows hCX.1 hCX.2 hAZ.1 hAZ.2 hBZ.1 hBZ.2
      · exact fourRow_pair_bound_of_two_avoiding hpq.symm
          (by
            rw [hHform]
            ext T
            simp [Finset.pair_comm, or_comm, or_left_comm])
          hHclutter hHRows hBRows hCY.2 hCY.1 hAZ.2 hAZ.1 hBZ.2 hBZ.1
      · exact fourRow_pair_bound_of_three_avoiding hpq hHform hHcard hHclutter
          hHRows hPairRows hBRows hAZ.1 hAZ.2 hBZ.1 hBZ.2 hCZ.1 hCZ.2

end AiMathLab.P0054.G413
