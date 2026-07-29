import AiMathLab.P0054G413.FourRowPair

namespace AiMathLab.P0054.G413

theorem pairRows_card_add_one_le_of_pair_mem {α : Type*}
    [Fintype α]
    {H K : Hypergraph α} {E : Row α}
    (hKH : K ⊆ H) (hEH : E ∈ H) (hEcard : E.card = 2) (hEK : E ∉ K) :
    (pairRows K).card + 1 ≤ (pairRows H).card := by
  classical
  have hPairSubset : pairRows K ⊆ pairRows H := by
    intro T hT
    obtain ⟨hTK, hTcard⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨hKH hTK, hTcard⟩
  have hEPairH : E ∈ pairRows H := Finset.mem_filter.mpr ⟨hEH, hEcard⟩
  have hEPairK : E ∉ pairRows K := fun h ↦ hEK (Finset.mem_filter.mp h).1
  have hInsertSubset : insert E (pairRows K) ⊆ pairRows H :=
    Finset.insert_subset hEPairH hPairSubset
  have hCard := Finset.card_le_card hInsertSubset
  rw [Finset.card_insert_of_notMem hEPairK] at hCard
  omega

theorem fourRow_blocker_card_ge_three_of_pairRows_card_le_two {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 4)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hPairs : (pairRows H).card ≤ 2) :
    3 ≤ (blocker H).card := by
  classical
  have hHnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hBtwo : 2 ≤ (blocker H).card :=
    blocker_card_ge_two_of_rows_cardAtLeast_two hH hHnonempty hHRows
  by_contra hnot
  have hBcard : (blocker H).card = 2 := by omega
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker H := by simp [hBQ]
  have hQ₂b : Q₂ ∈ blocker H := by simp [hBQ]
  have hQ₁card : 2 ≤ Q₁.card := hBRows Q₁ hQ₁b
  have hQ₂card : 2 ≤ Q₂.card := hBRows Q₂ hQ₂b
  have hHtwo : H = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair hH hBQ
  have hDisjoint : Disjoint Q₁ Q₂ := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hzInter
    have hSingleton : ({z} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨z, hzInter, rfl⟩)
    have hLarge := hHRows {z} hSingleton
    simp at hLarge
  have hCrossSubset : crossPairRows Q₁ Q₂ ⊆ H := by
    intro E hE
    rw [hHtwo, twoRowBlockers, Finset.sdiff_eq_self_of_disjoint hDisjoint,
      Finset.sdiff_eq_self_of_disjoint hDisjoint.symm]
    exact Finset.mem_union_right _ hE
  have hCrossLower : 4 ≤ (crossPairRows Q₁ Q₂).card := by
    calc
      4 = 2 * 2 := rfl
      _ ≤ Q₁.card * Q₂.card := Nat.mul_le_mul hQ₁card hQ₂card
      _ ≤ (crossPairRows Q₁ Q₂).card :=
        card_mul_le_crossPairRows_card_of_disjoint hDisjoint
  have hCrossUpper : (crossPairRows Q₁ Q₂).card ≤ 4 := by
    simpa [hHcard] using Finset.card_le_card hCrossSubset
  have hCrossEqH : crossPairRows Q₁ Q₂ = H := by
    apply Finset.eq_of_subset_of_card_le hCrossSubset
    omega
  have hAllPairs : H ⊆ pairRows H := by
    intro E hEH
    have hECross : E ∈ crossPairRows Q₁ Q₂ := by simpa [hCrossEqH] using hEH
    obtain ⟨a, haQ₁, b, hbQ₂, hPairEq⟩ := mem_crossPairRows.mp hECross
    have hab : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp hDisjoint haQ₁ hbQ₂
    exact Finset.mem_filter.mpr ⟨hEH, by simp [← hPairEq, hab]⟩
  have hFourPairs := Finset.card_le_card hAllPairs
  omega

theorem triple_card_eq_three_of_quad_card_eq_four {α : Type*}
    [DecidableEq α]
    (A B C D : Row α)
    (hQuad : ({A, B, C, D} : Hypergraph α).card = 4) :
    ({A, B, C} : Hypergraph α).card = 3 := by
  have hLower : 4 ≤ ({A, B, C} : Hypergraph α).card + 1 := by
    have hLe := Finset.card_insert_le D ({A, B, C} : Hypergraph α)
    have hEq : ({A, B, C, D} : Hypergraph α) = insert D {A, B, C} := by
      ext T
      simp [or_comm, or_left_comm]
    rw [← hEq, hQuad] at hLe
    omega
  have hUpper : ({A, B, C} : Hypergraph α).card ≤ 3 := by
    calc
      ({A, B, C} : Hypergraph α).card ≤ ({B, C} : Hypergraph α).card + 1 :=
        Finset.card_insert_le A {B, C}
      _ ≤ ({C} : Hypergraph α).card + 2 := by
        have := Finset.card_insert_le B ({C} : Hypergraph α)
        omega
      _ = 3 := by simp
  omega

theorem third_row_large_of_pair_budget {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {E A B C : Row α}
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hEH : E ∈ H) (hAH : A ∈ H) (hBH : B ∈ H) (hCH : C ∈ H)
    (hEcard : E.card = 2) (hAcard : A.card = 2) (hBcard : B.card = 2)
    (hTripleCard : ({A, B, C} : Hypergraph α).card = 3)
    (hENotTriple : E ∉ ({A, B, C} : Hypergraph α)) :
    3 ≤ C.card := by
  classical
  by_contra hnot
  have hCcard : C.card = 2 := by
    have := hHRows C hCH
    omega
  let J : Hypergraph α := {A, B, C}
  have hJsubset : J ⊆ H := by
    intro T hT
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact hAH
    · exact hBH
    · exact hCH
  have hJpairs : pairRows J = J := by
    ext T
    simp only [pairRows, Finset.mem_filter]
    constructor
    · exact fun h ↦ h.1
    · intro hTJ
      refine ⟨hTJ, ?_⟩
      simp only [J, Finset.mem_insert, Finset.mem_singleton] at hTJ
      rcases hTJ with rfl | rfl | rfl
      · exact hAcard
      · exact hBcard
      · exact hCcard
  have hAdd := pairRows_card_add_one_le_of_pair_mem
    hJsubset hEH hEcard (by simpa [J] using hENotTriple)
  rw [hJpairs] at hAdd
  have hTooMany := hAdd.trans hPairRows
  have hJcard : J.card = 3 := by simpa [J] using hTripleCard
  omega

theorem fiveRow_pair_bound_of_four_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {Z₁ Z₂ Z₃ Z₄ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, Z₁, Z₂, Z₃, Z₄})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂)
    (hpZ₃ : p ∉ Z₃) (hqZ₃ : q ∉ Z₃)
    (hpZ₄ : p ∉ Z₄) (hqZ₄ : q ∉ Z₄) :
    6 ≤ (blocker H).card := by
  let K : Hypergraph α := {Z₁, Z₂, Z₃, Z₄}
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hZ₃H : Z₃ ∈ H := by simp [hH]
  have hZ₄H : Z₄ ∈ H := by simp [hH]
  have hKsubset : K ⊆ H := by
    intro T hT
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact hZ₁H
    · exact hZ₂H
    · exact hZ₃H
    · exact hZ₄H
  have hKclutter : IsClutter K := hHclutter.mono hKsubset
  have hPairNotK : ({p, q} : Row α) ∉ K := by
    intro hPairK
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hPairK
    rcases hPairK with hEq | hEq | hEq | hEq
    · exact hpZ₁ (hEq ▸ (by simp))
    · exact hpZ₂ (hEq ▸ (by simp))
    · exact hpZ₃ (hEq ▸ (by simp))
    · exact hpZ₄ (hEq ▸ (by simp))
  have hKcard : K.card = 4 := by
    rw [hH] at hHcard
    rw [Finset.card_insert_of_notMem hPairNotK] at hHcard
    omega
  have hKRows : RowsCardAtLeast K 2 := by
    intro T hT
    exact hHRows T (hKsubset hT)
  have hKPairRows : (pairRows K).card ≤ 2 := by
    have hAdd := pairRows_card_add_one_le_of_pair_mem hKsubset hPair (by simp [hpq]) hPairNotK
    omega
  have hAvoidP : avoidPoint H p = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · simp [K]
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₃H, hpZ₃⟩
      · exact mem_avoidPoint.mpr ⟨hZ₄H, hpZ₄⟩
  have hAvoidQ : avoidPoint H q = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp [K]
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₃H, hqZ₃⟩
      · exact mem_avoidPoint.mpr ⟨hZ₄H, hqZ₄⟩
  have hDeleteQ : deletePoint K q = K := by
    ext T
    simp [deletePoint, K, hqZ₁, hqZ₂, hqZ₃, hqZ₄]
  have hDeleteP : deletePoint K p = K := by
    ext T
    simp [deletePoint, K, hpZ₁, hpZ₂, hpZ₃, hpZ₄]
  have hSideP : pairSide H p q = K := by
    rw [pairSide, residual, hAvoidP, hDeleteQ, minimize_eq_self_of_isClutter hKclutter]
  have hSideQ : pairSide H q p = K := by
    rw [pairSide, residual, hAvoidQ, hDeleteP, minimize_eq_self_of_isClutter hKclutter]
  have hKBlockerRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hSideP] using pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hKThree : 3 ≤ (blocker K).card :=
    fourRow_blocker_card_ge_three_of_pairRows_card_le_two
      hKclutter hKcard hKRows hKBlockerRows hKPairRows
  have hSum := pairSide_blocker_card_add_le hpq hPair
  rw [hSideP, hSideQ] at hSum
  omega

theorem fiveRow_pair_bound_of_three_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X Z₁ Z₂ Z₃ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X, Z₁, Z₂, Z₃})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX : p ∈ X) (hqX : q ∉ X)
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
  have hXNotK : X ∉ K := by
    intro hXK
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hXK
    rcases hXK with hEq | hEq | hEq
    · exact hpZ₁ (hEq ▸ hpX)
    · exact hpZ₂ (hEq ▸ hpX)
    · exact hpZ₃ (hEq ▸ hpX)
  have hKcard : K.card = 3 := by
    have hXH : X ∈ H := by simp [hH]
    have hPairNeX : ({p, q} : Row α) ≠ X := by
      intro hEq
      exact hqX (hEq ▸ (by simp))
    have hPairNotInsert : ({p, q} : Row α) ∉ insert X K := by
      simp [hPairNeX, hPairNotK]
    have hXInsert : X ∉ K := hXNotK
    rw [hH, Finset.card_insert_of_notMem hPairNotInsert,
      Finset.card_insert_of_notMem hXInsert] at hHcard
    omega
  have hKRows : RowsCardAtLeast K 2 := by
    intro T hT
    exact hHRows T (hKsubset hT)
  have hKPairRows : (pairRows K).card ≤ 2 := by
    have hAdd := pairRows_card_add_one_le_of_pair_mem hKsubset hPair (by simp [hpq]) hPairNotK
    omega
  have hAvoidP : avoidPoint H p = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX).elim
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₃H, hpZ₃⟩
  have hDeleteQ : deletePoint K q = K := by
    ext T
    simp [deletePoint, K, hqZ₁, hqZ₂, hqZ₃]
  have hSideP : pairSide H p q = K := by
    rw [pairSide, residual, hAvoidP, hDeleteQ, minimize_eq_self_of_isClutter hKclutter]
  have hKBlockerRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hSideP] using pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hKFour : 4 ≤ (blocker K).card :=
    threeRow_blocker_card_ge_four_of_pairRows_card_le_two
      hKclutter hKcard hKRows hKBlockerRows hKPairRows
  have hAvoidQ : avoidPoint H q = insert X K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · simp [K]
      · simp [K]
      · simp [K]
    · intro hT
      simp only [Finset.mem_insert] at hT
      rcases hT with rfl | hTK
      · exact mem_avoidPoint.mpr ⟨by simp [hH], hqX⟩
      · exact mem_avoidPoint.mpr ⟨hKsubset hTK, by
          simp only [K, Finset.mem_insert, Finset.mem_singleton] at hTK
          rcases hTK with rfl | rfl | rfl
          · exact hqZ₁
          · exact hqZ₂
          · exact hqZ₃⟩
  have hSideQSingleton : (rowsCardAtMost (pairSide H q p) 1).card ≤ 1 := by
    calc
      (rowsCardAtMost (pairSide H q p) 1).card ≤ ({X.erase p} : Hypergraph α).card := by
        apply Finset.card_le_card
        intro T hT
        obtain ⟨hTSide, hTcard⟩ := mem_rowsCardAtMost.mp hT
        have hTsource : T ∈ deletePoint (avoidPoint H q) p :=
          minimize_subset _ hTSide
        rw [hAvoidQ] at hTsource
        simp only [deletePoint, Finset.mem_image, Finset.mem_insert] at hTsource
        obtain ⟨A, hA, hAerase⟩ := hTsource
        rcases hA with rfl | hAK
        · simp [hAerase]
        · have hAH : A ∈ H := hKsubset hAK
          have hpA : p ∉ A := by
            simp only [K, Finset.mem_insert, Finset.mem_singleton] at hAK
            rcases hAK with rfl | rfl | rfl
            · exact hpZ₁
            · exact hpZ₂
            · exact hpZ₃
          have hAcard := hHRows A hAH
          have hEq : T = A := by simpa [hpA] using hAerase.symm
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
  rw [hSideP] at hSum
  omega

theorem fiveRow_pair_bound_of_two_avoiding_same_side {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X₁ X₂ Z₁ Z₂ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X₁, X₂, Z₁, Z₂})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX₁ : p ∈ X₁) (hqX₁ : q ∉ X₁)
    (hpX₂ : p ∈ X₂) (hqX₂ : q ∉ X₂)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂) :
    6 ≤ (blocker H).card := by
  let K : Hypergraph α := {Z₁, Z₂}
  let R : Hypergraph α := {X₁, X₂, Z₁, Z₂}
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hX₁H : X₁ ∈ H := by simp [hH]
  have hX₂H : X₂ ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hKsubset : K ⊆ H := by
    intro T hT
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hZ₁H
    · exact hZ₂H
  have hKclutter : IsClutter K := hHclutter.mono hKsubset
  have hPairNotR : ({p, q} : Row α) ∉ R := by
    intro hPairR
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hPairR
    rcases hPairR with hEq | hEq | hEq | hEq
    · exact hqX₁ (hEq ▸ (by simp))
    · exact hqX₂ (hEq ▸ (by simp))
    · exact hpZ₁ (hEq ▸ (by simp))
    · exact hpZ₂ (hEq ▸ (by simp))
  have hRcard : R.card = 4 := by
    have hHinsert : H = insert {p, q} R := by simp [hH, R]
    rw [hHinsert, Finset.card_insert_of_notMem hPairNotR] at hHcard
    omega
  have hZ₁card := hHRows Z₁ hZ₁H
  have hZ₂card := hHRows Z₂ hZ₂H
  have hX₁card := hHRows X₁ hX₁H
  have hX₂card := hHRows X₂ hX₂H
  have hX₁erasePositive : 1 ≤ (X₁.erase p).card := by
    rw [Finset.card_erase_of_mem hpX₁]
    omega
  have hX₂erasePositive : 1 ≤ (X₂.erase p).card := by
    rw [Finset.card_erase_of_mem hpX₂]
    omega
  have hAvoidP : avoidPoint H p = K := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX₁).elim
      · exact (hpT hpX₂).elim
      · simp [K]
      · simp [K]
    · intro hT
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
  have hDeleteQ : deletePoint K q = K := by
    ext T
    simp [deletePoint, K, hqZ₁, hqZ₂]
  have hSideP : pairSide H p q = K := by
    rw [pairSide, residual, hAvoidP, hDeleteQ, minimize_eq_self_of_isClutter hKclutter]
  have hSidePBlockerRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hSideP] using pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hSidePProduct : Z₁.card * Z₂.card ≤ (blocker K).card :=
    twoRow_blocker_card_ge_product hSidePBlockerRows
  have hSidePFour : 4 ≤ (blocker K).card := by
    calc
      4 = 2 * 2 := rfl
      _ ≤ Z₁.card * Z₂.card := Nat.mul_le_mul hZ₁card hZ₂card
      _ ≤ (blocker K).card := hSidePProduct
  have hAvoidQ : avoidPoint H q = R := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp [R]
      · simp [R]
      · simp [R]
      · simp [R]
    · intro hT
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hX₁H, hqX₁⟩
      · exact mem_avoidPoint.mpr ⟨hX₂H, hqX₂⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
  have hSideQNonempty : (blocker (pairSide H q p)).Nonempty := by
    exact blocker_nonempty (pairSide_rows_nonempty hHRows q p)
  have hSideQPositive : 1 ≤ (blocker (pairSide H q p)).card :=
    Finset.card_pos.mpr hSideQNonempty
  have hSum := pairSide_blocker_card_add_le hpq hPair
  rw [hSideP] at hSum
  by_cases hSideQTwo : 2 ≤ (blocker (pairSide H q p)).card
  · omega
  · have hSideQcard : (blocker (pairSide H q p)).card = 1 := by omega
    obtain ⟨Q, hBQ⟩ := Finset.card_eq_one.mp hSideQcard
    have hQb : Q ∈ blocker (pairSide H q p) := by simp [hBQ]
    have hQcard : 2 ≤ Q.card :=
      pairSide_blocker_rows_cardAtLeast_two
        (by simpa [Finset.pair_comm] using hPair) hBRows Q hQb
    obtain ⟨a, haQ, b, hbQ, hab⟩ := Finset.one_lt_card.mp hQcard
    have hSideQSingleton : pairSide H q p = singletonRows Q :=
      family_eq_singletonRows_of_blocker_eq_singleton
        (residual_isClutter _ _) hBQ
    have haSide : ({a} : Row α) ∈ pairSide H q p := by
      rw [hSideQSingleton]
      exact mem_singletonRows.mpr ⟨a, haQ, rfl⟩
    have hbSide : ({b} : Row α) ∈ pairSide H q p := by
      rw [hSideQSingleton]
      exact mem_singletonRows.mpr ⟨b, hbQ, rfl⟩
    have hSmallSource : rowsCardAtMost (pairSide H q p) 1 ⊆
        ({X₁.erase p, X₂.erase p} : Hypergraph α) := by
      intro T hT
      obtain ⟨hTSide, hTcard⟩ := mem_rowsCardAtMost.mp hT
      have hTsource : T ∈ deletePoint (avoidPoint H q) p :=
        minimize_subset _ hTSide
      rw [hAvoidQ] at hTsource
      simp only [deletePoint, R, Finset.mem_image, Finset.mem_insert,
        Finset.mem_singleton] at hTsource
      obtain ⟨A, hA, hAerase⟩ := hTsource
      rcases hA with hAX₁ | hAX₂ | hAZ₁ | hAZ₂
      · subst A
        simp [hAerase]
      · subst A
        simp [hAerase]
      · subst A
        have hEq : T = Z₁ := by simpa [hpZ₁] using hAerase.symm
        rw [hEq] at hTcard
        omega
      · subst A
        have hEq : T = Z₂ := by simpa [hpZ₂] using hAerase.symm
        rw [hEq] at hTcard
        omega
    have hTwoSmall : 2 ≤ (rowsCardAtMost (pairSide H q p) 1).card := by
      have hPairSubset : ({{a}, {b}} : Hypergraph α) ⊆
          rowsCardAtMost (pairSide H q p) 1 := by
        intro T hT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl
        · exact mem_rowsCardAtMost.mpr ⟨haSide, by simp⟩
        · exact mem_rowsCardAtMost.mpr ⟨hbSide, by simp⟩
      have hCard := Finset.card_le_card hPairSubset
      simpa [Finset.singleton_inj, hab] using hCard
    have hSourceUpper : ({X₁.erase p, X₂.erase p} : Hypergraph α).card ≤ 2 := by
      calc
        ({X₁.erase p, X₂.erase p} : Hypergraph α).card ≤
            ({X₂.erase p} : Hypergraph α).card + 1 :=
          Finset.card_insert_le (X₁.erase p) ({X₂.erase p} : Hypergraph α)
        _ = 2 := by simp
    have hSmallEq : rowsCardAtMost (pairSide H q p) 1 =
        ({X₁.erase p, X₂.erase p} : Hypergraph α) := by
      apply Finset.eq_of_subset_of_card_le hSmallSource
      have hSmallCard := Finset.card_le_card hSmallSource
      omega
    have hX₁eraseSmall : (X₁.erase p).card ≤ 1 := by
      have : X₁.erase p ∈ rowsCardAtMost (pairSide H q p) 1 := by
        rw [hSmallEq]
        simp
      exact (mem_rowsCardAtMost.mp this).2
    have hX₂eraseSmall : (X₂.erase p).card ≤ 1 := by
      have : X₂.erase p ∈ rowsCardAtMost (pairSide H q p) 1 := by
        rw [hSmallEq]
        simp
      exact (mem_rowsCardAtMost.mp this).2
    have hX₁Pair : X₁.card = 2 := by
      rw [Finset.card_erase_of_mem hpX₁] at hX₁eraseSmall hX₁erasePositive
      omega
    have hX₂Pair : X₂.card = 2 := by
      rw [Finset.card_erase_of_mem hpX₂] at hX₂eraseSmall hX₂erasePositive
      omega
    have hZ₁Large : 3 ≤ Z₁.card := by
      by_contra hnot
      have hZ₁Pair : Z₁.card = 2 := by omega
      let J : Hypergraph α := {X₁, X₂, Z₁}
      have hJsubset : J ⊆ H := by
        intro T hT
        simp only [J, Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl | rfl
        · exact hX₁H
        · exact hX₂H
        · exact hZ₁H
      have hJcard : J.card = 3 := by
        have hRinsert : R = insert Z₂ J := by
          ext T
          simp [R, J, or_comm, or_left_comm]
        have hLe : R.card ≤ J.card + 1 := by
          rw [hRinsert]
          exact Finset.card_insert_le Z₂ J
        have hJupper : J.card ≤ 3 := by
          calc
            J.card ≤ ({X₂, Z₁} : Hypergraph α).card + 1 :=
              Finset.card_insert_le X₁ {X₂, Z₁}
            _ ≤ ({Z₁} : Hypergraph α).card + 2 := by
              have := Finset.card_insert_le (s := ({Z₁} : Hypergraph α)) X₂
              omega
            _ = 3 := by simp
        omega
      have hJpairs : pairRows J = J := by
        ext T
        simp only [pairRows, Finset.mem_filter]
        constructor
        · exact fun h ↦ h.1
        · intro hTJ
          refine ⟨hTJ, ?_⟩
          simp only [J, Finset.mem_insert, Finset.mem_singleton] at hTJ
          rcases hTJ with rfl | rfl | rfl
          · exact hX₁Pair
          · exact hX₂Pair
          · exact hZ₁Pair
      have hAdd := pairRows_card_add_one_le_of_pair_mem
        hJsubset hPair (by simp [hpq]) (by
          intro hEJ
          simp only [J, Finset.mem_insert, Finset.mem_singleton] at hEJ
          rcases hEJ with hEq | hEq | hEq
          · exact hqX₁ (hEq ▸ (by simp))
          · exact hqX₂ (hEq ▸ (by simp))
          · exact hpZ₁ (hEq ▸ (by simp)))
      rw [hJpairs, hJcard] at hAdd
      omega
    have hZ₂Large : 3 ≤ Z₂.card := by
      by_contra hnot
      have hZ₂Pair : Z₂.card = 2 := by omega
      let J : Hypergraph α := {X₁, X₂, Z₂}
      have hJsubset : J ⊆ H := by
        intro T hT
        simp only [J, Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl | rfl
        · exact hX₁H
        · exact hX₂H
        · exact hZ₂H
      have hJcard : J.card = 3 := by
        have hRinsert : R = insert Z₁ J := by simp [R, J, Finset.insert_comm]
        have hLe : R.card ≤ J.card + 1 := by
          rw [hRinsert]
          exact Finset.card_insert_le Z₁ J
        have hJupper : J.card ≤ 3 := by
          calc
            J.card ≤ ({X₂, Z₂} : Hypergraph α).card + 1 :=
              Finset.card_insert_le X₁ {X₂, Z₂}
            _ ≤ ({Z₂} : Hypergraph α).card + 2 := by
              have := Finset.card_insert_le (s := ({Z₂} : Hypergraph α)) X₂
              omega
            _ = 3 := by simp
        omega
      have hJpairs : pairRows J = J := by
        ext T
        simp only [pairRows, Finset.mem_filter]
        constructor
        · exact fun h ↦ h.1
        · intro hTJ
          refine ⟨hTJ, ?_⟩
          simp only [J, Finset.mem_insert, Finset.mem_singleton] at hTJ
          rcases hTJ with rfl | rfl | rfl
          · exact hX₁Pair
          · exact hX₂Pair
          · exact hZ₂Pair
      have hAdd := pairRows_card_add_one_le_of_pair_mem
        hJsubset hPair (by simp [hpq]) (by
          intro hEJ
          simp only [J, Finset.mem_insert, Finset.mem_singleton] at hEJ
          rcases hEJ with hEq | hEq | hEq
          · exact hqX₁ (hEq ▸ (by simp))
          · exact hqX₂ (hEq ▸ (by simp))
          · exact hpZ₂ (hEq ▸ (by simp)))
      rw [hJpairs, hJcard] at hAdd
      omega
    have hSidePNine : 9 ≤ (blocker K).card := by
      calc
        9 = 3 * 3 := rfl
        _ ≤ Z₁.card * Z₂.card := Nat.mul_le_mul hZ₁Large hZ₂Large
        _ ≤ (blocker K).card := hSidePProduct
    omega


theorem fiveRow_pair_split_other_side_four_of_first_side_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X Y Z₁ Z₂ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X, Y, Z₁, Z₂})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX : p ∈ X) (hqX : q ∉ X)
    (hpY : p ∉ Y) (hqY : q ∈ Y)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂)
    (hFirstSideTwo : (blocker (pairSide H p q)).card = 2) :
    4 ≤ (blocker (pairSide H q p)).card := by
  let P : Row α := Y.erase q
  let S : Hypergraph α := {P, Z₁, Z₂}
  let R : Hypergraph α := {X, Y, Z₁, Z₂}
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hXH : X ∈ H := by simp [hH]
  have hYH : Y ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hXcard := hHRows X hXH
  have hYcard := hHRows Y hYH
  have hZ₁card := hHRows Z₁ hZ₁H
  have hZ₂card := hHRows Z₂ hZ₂H
  have hPpositive : 1 ≤ P.card := by
    simp only [P, Finset.card_erase_of_mem hqY]
    omega
  have hAvoidP : avoidPoint H p = {Y, Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX).elim
      · simp
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hYH, hpY⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
  have hDeleteQ : deletePoint ({Y, Z₁, Z₂} : Hypergraph α) q = S := by
    ext T
    simp [deletePoint, S, P, hqZ₁, hqZ₂]
  have hSideP : pairSide H p q = minimize S := by
    rw [pairSide, residual, hAvoidP, hDeleteQ]
  have hSupper : S.card ≤ 3 := by
    calc
      S.card ≤ ({Z₁, Z₂} : Hypergraph α).card + 1 := by
        simpa [S] using Finset.card_insert_le P ({Z₁, Z₂} : Hypergraph α)
      _ ≤ ({Z₂} : Hypergraph α).card + 2 := by
        have := Finset.card_insert_le Z₁ ({Z₂} : Hypergraph α)
        omega
      _ = 3 := by simp
  have hSidePupper : (pairSide H p q).card ≤ 3 := by
    rw [hSideP]
    exact (Finset.card_le_card (minimize_subset S)).trans hSupper
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hFirstSideTwo
  have hQ₁b : Q₁ ∈ blocker (pairSide H p q) := by simp [hBQ]
  have hQ₂b : Q₂ ∈ blocker (pairSide H p q) := by simp [hBQ]
  have hSidePBlockerRows := pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hQ₁card : 2 ≤ Q₁.card := hSidePBlockerRows Q₁ hQ₁b
  have hQ₂card : 2 ≤ Q₂.card := hSidePBlockerRows Q₂ hQ₂b
  have hSidePTwo : pairSide H p q = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair
      (residual_isClutter _ _) hBQ
  have hInter : (Q₁ ∩ Q₂).Nonempty := by
    by_contra hnot
    have hDisjoint : Disjoint Q₁ Q₂ := disjoint_of_inter_not_nonempty hnot
    have hCrossSubset : crossPairRows Q₁ Q₂ ⊆ pairSide H p q := by
      intro T hT
      obtain ⟨a, haQ₁, b, hbQ₂, hTpair⟩ := mem_crossPairRows.mp hT
      rw [hSidePTwo]
      exact mem_twoRowBlockers.mpr (Or.inr
        ⟨a, Finset.mem_sdiff.mpr
            ⟨haQ₁, fun haQ₂ ↦ Finset.disjoint_left.mp hDisjoint haQ₁ haQ₂⟩,
          b, Finset.mem_sdiff.mpr
            ⟨hbQ₂, fun hbQ₁ ↦ Finset.disjoint_left.mp hDisjoint hbQ₁ hbQ₂⟩,
          hTpair⟩)
    have hCrossLower : 4 ≤ (crossPairRows Q₁ Q₂).card := by
      calc
        4 = 2 * 2 := rfl
        _ ≤ Q₁.card * Q₂.card := Nat.mul_le_mul hQ₁card hQ₂card
        _ ≤ (crossPairRows Q₁ Q₂).card :=
          card_mul_le_crossPairRows_card_of_disjoint hDisjoint
    have hCrossUpper := Finset.card_le_card hCrossSubset
    omega
  obtain ⟨u, huInter⟩ := hInter
  have hSingletonSide : ({u} : Row α) ∈ pairSide H p q := by
    rw [hSidePTwo]
    exact mem_twoRowBlockers.mpr (Or.inl ⟨u, huInter, rfl⟩)
  have hSingletonSource : ({u} : Row α) ∈ S := by
    exact minimize_subset S (by simpa [hSideP] using hSingletonSide)
  have hPcard : P.card = 1 := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hSingletonSource
    rcases hSingletonSource with hEq | hEq | hEq
    · simpa [← hEq]
    · have : Z₁.card = 1 := by simp [← hEq]
      omega
    · have : Z₂.card = 1 := by simp [← hEq]
      omega
  have hYPair : Y.card = 2 := by
    simp only [P, Finset.card_erase_of_mem hqY] at hPcard
    omega
  have hQ₁NotSubset : ¬Q₁ ⊆ Q₂ := by
    intro hSubset
    exact hQNe ((blocker_isClutter (pairSide H p q)) hQ₁b hQ₂b hSubset)
  have hQ₂NotSubset : ¬Q₂ ⊆ Q₁ := by
    intro hSubset
    exact hQNe.symm ((blocker_isClutter (pairSide H p q)) hQ₂b hQ₁b hSubset)
  obtain ⟨a, haQ₁, haQ₂⟩ := Finset.not_subset.mp hQ₁NotSubset
  obtain ⟨b, hbQ₂, hbQ₁⟩ := Finset.not_subset.mp hQ₂NotSubset
  have hab : a ≠ b := by
    intro hab
    subst b
    exact haQ₂ hbQ₂
  have hCrossSide : ({a, b} : Row α) ∈ pairSide H p q := by
    rw [hSidePTwo]
    exact mem_twoRowBlockers.mpr (Or.inr
      ⟨a, Finset.mem_sdiff.mpr ⟨haQ₁, haQ₂⟩,
        b, Finset.mem_sdiff.mpr ⟨hbQ₂, hbQ₁⟩, rfl⟩)
  have hCrossSource : ({a, b} : Row α) ∈ S := by
    exact minimize_subset S (by simpa [hSideP] using hCrossSide)
  have hZPair : Z₁.card = 2 ∨ Z₂.card = 2 := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hCrossSource
    rcases hCrossSource with hEq | hEq | hEq
    · have hPairCard : ({a, b} : Row α).card = 2 := by simp [hab]
      have : P.card = 2 := by simpa [← hEq]
      omega
    · exact Or.inl (by simpa [← hEq, hab])
    · exact Or.inr (by simpa [← hEq, hab])
  have hPairNotR : ({p, q} : Row α) ∉ R := by
    intro hPairR
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hPairR
    rcases hPairR with hEq | hEq | hEq | hEq
    · exact hqX (hEq ▸ (by simp))
    · exact hpY (hEq ▸ (by simp))
    · exact hpZ₁ (hEq ▸ (by simp))
    · exact hpZ₂ (hEq ▸ (by simp))
  have hRcard : R.card = 4 := by
    have hHinsert : H = insert {p, q} R := by simp [hH, R]
    rw [hHinsert, Finset.card_insert_of_notMem hPairNotR] at hHcard
    omega
  have hAvoidQ : avoidPoint H q = {X, Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · exact (hqT hqY).elim
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hXH, hqX⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
  have hOtherFour (ZPair ZLarge : Row α)
      (hSideQ : pairSide H q p = minimize {X.erase p, ZPair, ZLarge})
      (hXLarge : 3 ≤ X.card) (hZPairCard : ZPair.card = 2)
      (hZLargeCard : 3 ≤ ZLarge.card) :
      4 ≤ (blocker (pairSide H q p)).card := by
    let U : Hypergraph α := {X.erase p, ZPair, ZLarge}
    have hXerase : 2 ≤ (X.erase p).card := by
      rw [Finset.card_erase_of_mem hpX]
      omega
    have hURows : RowsCardAtLeast (pairSide H q p) 2 := by
      intro T hT
      have hTsource : T ∈ U := minimize_subset U (by
        simpa [hSideQ, U] using hT)
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hTsource
      rcases hTsource with hEq | hEq | hEq
      · simpa [← hEq] using hXerase
      · simpa [← hEq] using hZPairCard.ge
      · simpa [← hEq] using hZLargeCard.trans' (by omega)
    have hUupper : U.card ≤ 3 := by
      calc
        U.card ≤ ({ZPair, ZLarge} : Hypergraph α).card + 1 := by
          simpa [U] using
            Finset.card_insert_le (X.erase p) ({ZPair, ZLarge} : Hypergraph α)
        _ ≤ ({ZLarge} : Hypergraph α).card + 2 := by
          have := Finset.card_insert_le ZPair ({ZLarge} : Hypergraph α)
          omega
        _ = 3 := by simp
    have hSideQupper : (pairSide H q p).card ≤ 3 := by
      rw [hSideQ]
      simpa [U] using (Finset.card_le_card (minimize_subset U)).trans hUupper
    have hSideQnonempty : (pairSide H q p).Nonempty := by
      have hXsource : X.erase p ∈ U := by simp [U]
      obtain ⟨T, hTmin, -⟩ := exists_minimize_subset hXsource
      exact ⟨T, by simpa [hSideQ, U] using hTmin⟩
    have hSideQpositive : 0 < (pairSide H q p).card :=
      Finset.card_pos.mpr hSideQnonempty
    have hSideQBlockerRows := pairSide_blocker_rows_cardAtLeast_two
      (H := H) (p := q) (q := p)
      (by simpa [Finset.pair_comm] using hPair) hBRows
    have hSideQlower : 2 ≤ (pairSide H q p).card := by
      by_contra hnot
      have hSideQcard : (pairSide H q p).card = 1 := by omega
      obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hSideQcard
      have hASide : A ∈ pairSide H q p := by simp [hA]
      have hAcard : 2 ≤ A.card := hURows A hASide
      obtain ⟨a, haA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      have hSingletonBlocker : ({a} : Row α) ∈ blocker (pairSide H q p) := by
        rw [hA, blocker_singletonFamily]
        exact mem_singletonRows.mpr ⟨a, haA, rfl⟩
      have hLarge := hSideQBlockerRows {a} hSingletonBlocker
      simp at hLarge
    have hSideQPairRows : (pairRows (pairSide H q p)).card ≤ 2 := by
      have hPairSource : pairRows (pairSide H q p) ⊆
          ({X.erase p, ZPair} : Hypergraph α) := by
        intro T hT
        obtain ⟨hTSide, hTcard⟩ := Finset.mem_filter.mp hT
        have hTsource : T ∈ U := minimize_subset U (by
          simpa [hSideQ, U] using hTSide)
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hTsource
        rcases hTsource with hEq | hEq | hEq
        · simp [hEq]
        · simp [hEq]
        · have : T.card = ZLarge.card := congrArg Finset.card hEq
          omega
      have hCard := Finset.card_le_card hPairSource
      have hUpper : ({X.erase p, ZPair} : Hypergraph α).card ≤ 2 := by
        calc
          ({X.erase p, ZPair} : Hypergraph α).card ≤
              ({ZPair} : Hypergraph α).card + 1 :=
            Finset.card_insert_le (X.erase p) ({ZPair} : Hypergraph α)
          _ = 2 := by simp
      omega
    have hCases : (pairSide H q p).card = 2 ∨ (pairSide H q p).card = 3 := by
      omega
    rcases hCases with hCard | hCard
    · obtain ⟨A, B, hAB, hSideQAB⟩ := Finset.card_eq_two.mp hCard
      have hArows : 2 ≤ A.card := hURows A (by simp [hSideQAB])
      have hBrows : 2 ≤ B.card := hURows B (by simp [hSideQAB])
      have hProduct : A.card * B.card ≤ (blocker (pairSide H q p)).card := by
        rw [hSideQAB]
        exact twoRow_blocker_card_ge_product (by simpa [hSideQAB] using hSideQBlockerRows)
      calc
        4 = 2 * 2 := rfl
        _ ≤ A.card * B.card := Nat.mul_le_mul hArows hBrows
        _ ≤ (blocker (pairSide H q p)).card := hProduct
    · exact threeRow_blocker_card_ge_four_of_pairRows_card_le_two
        (residual_isClutter _ _) hCard hURows hSideQBlockerRows hSideQPairRows
  rcases hZPair with hZ₁Pair | hZ₂Pair
  · have hTripleX : ({Y, Z₁, X} : Hypergraph α).card = 3 := by
      apply triple_card_eq_three_of_quad_card_eq_four Y Z₁ X Z₂
      have hEq : ({Y, Z₁, X, Z₂} : Hypergraph α) = R := by
        ext T
        simp [R, or_comm, or_left_comm]
      simpa [hEq] using hRcard
    have hTripleZ₂ : ({Y, Z₁, Z₂} : Hypergraph α).card = 3 := by
      apply triple_card_eq_three_of_quad_card_eq_four Y Z₁ Z₂ X
      have hEq : ({Y, Z₁, Z₂, X} : Hypergraph α) = R := by
        ext T
        simp [R, or_comm, or_left_comm]
      simpa [hEq] using hRcard
    have hXlarge : 3 ≤ X.card :=
      third_row_large_of_pair_budget hHRows hPairRows hPair hYH hZ₁H hXH
        (by simp [hpq]) hYPair hZ₁Pair hTripleX (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpZ₁ (h ▸ (by simp)),
            fun h ↦ hqX (h ▸ (by simp))⟩)
    have hZ₂large : 3 ≤ Z₂.card :=
      third_row_large_of_pair_budget hHRows hPairRows hPair hYH hZ₁H hZ₂H
        (by simp [hpq]) hYPair hZ₁Pair hTripleZ₂ (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpZ₁ (h ▸ (by simp)),
            fun h ↦ hpZ₂ (h ▸ (by simp))⟩)
    have hDeleteP : deletePoint ({X, Z₁, Z₂} : Hypergraph α) p =
        {X.erase p, Z₁, Z₂} := by
      ext T
      simp [deletePoint, hpZ₁, hpZ₂]
    have hSideQ : pairSide H q p = minimize {X.erase p, Z₁, Z₂} := by
      rw [pairSide, residual, hAvoidQ, hDeleteP]
    exact hOtherFour Z₁ Z₂ hSideQ hXlarge hZ₁Pair hZ₂large
  · have hTripleX : ({Y, Z₂, X} : Hypergraph α).card = 3 := by
      apply triple_card_eq_three_of_quad_card_eq_four Y Z₂ X Z₁
      have hEq : ({Y, Z₂, X, Z₁} : Hypergraph α) = R := by
        ext T
        simp [R, or_comm, or_left_comm]
      simpa [hEq] using hRcard
    have hTripleZ₁ : ({Y, Z₂, Z₁} : Hypergraph α).card = 3 := by
      apply triple_card_eq_three_of_quad_card_eq_four Y Z₂ Z₁ X
      have hEq : ({Y, Z₂, Z₁, X} : Hypergraph α) = R := by
        ext T
        simp [R, or_comm, or_left_comm]
      simpa [hEq] using hRcard
    have hXlarge : 3 ≤ X.card :=
      third_row_large_of_pair_budget hHRows hPairRows hPair hYH hZ₂H hXH
        (by simp [hpq]) hYPair hZ₂Pair hTripleX (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpZ₂ (h ▸ (by simp)),
            fun h ↦ hqX (h ▸ (by simp))⟩)
    have hZ₁large : 3 ≤ Z₁.card :=
      third_row_large_of_pair_budget hHRows hPairRows hPair hYH hZ₂H hZ₁H
        (by simp [hpq]) hYPair hZ₂Pair hTripleZ₁ (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpZ₂ (h ▸ (by simp)),
            fun h ↦ hpZ₁ (h ▸ (by simp))⟩)
    have hDeleteP : deletePoint ({X, Z₁, Z₂} : Hypergraph α) p =
        {X.erase p, Z₂, Z₁} := by
      ext T
      simp [deletePoint, hpZ₁, hpZ₂, or_comm, or_left_comm]
    have hSideQ : pairSide H q p = minimize {X.erase p, Z₂, Z₁} := by
      rw [pairSide, residual, hAvoidQ, hDeleteP]
    exact hOtherFour Z₂ Z₁ hSideQ hXlarge hZ₂Pair hZ₁large

theorem fiveRow_pair_bound_of_two_avoiding_split {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X Y Z₁ Z₂ : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X, Y, Z₁, Z₂})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX : p ∈ X) (hqX : q ∉ X)
    (hpY : p ∉ Y) (hqY : q ∈ Y)
    (hpZ₁ : p ∉ Z₁) (hqZ₁ : q ∉ Z₁)
    (hpZ₂ : p ∉ Z₂) (hqZ₂ : q ∉ Z₂) :
    6 ≤ (blocker H).card := by
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hXH : X ∈ H := by simp [hH]
  have hYH : Y ∈ H := by simp [hH]
  have hZ₁H : Z₁ ∈ H := by simp [hH]
  have hZ₂H : Z₂ ∈ H := by simp [hH]
  have hZ₁card := hHRows Z₁ hZ₁H
  have hZ₂card := hHRows Z₂ hZ₂H
  have hAvoidP : avoidPoint H p = {Y, Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX).elim
      · simp
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hYH, hpY⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hpZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hpZ₂⟩
  have hAvoidQ : avoidPoint H q = {X, Z₁, Z₂} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · exact (hqT hqY).elim
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hXH, hqX⟩
      · exact mem_avoidPoint.mpr ⟨hZ₁H, hqZ₁⟩
      · exact mem_avoidPoint.mpr ⟨hZ₂H, hqZ₂⟩
  have hSidePSingleton : (rowsCardAtMost (pairSide H p q) 1).card ≤ 1 := by
    calc
      (rowsCardAtMost (pairSide H p q) 1).card ≤ ({Y.erase q} : Hypergraph α).card := by
        apply Finset.card_le_card
        intro T hT
        obtain ⟨hTSide, hTcard⟩ := mem_rowsCardAtMost.mp hT
        have hTsource : T ∈ deletePoint (avoidPoint H p) q :=
          minimize_subset _ hTSide
        rw [hAvoidP] at hTsource
        simp only [deletePoint, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at hTsource
        obtain ⟨A, hA, hAerase⟩ := hTsource
        rcases hA with hAY | hAZ₁ | hAZ₂
        · subst A
          simp [hAerase]
        · subst A
          have hEq : T = Z₁ := by simpa [hqZ₁] using hAerase.symm
          rw [hEq] at hTcard
          omega
        · subst A
          have hEq : T = Z₂ := by simpa [hqZ₂] using hAerase.symm
          rw [hEq] at hTcard
          omega
      _ = 1 := by simp
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
          have hEq : T = Z₁ := by simpa [hpZ₁] using hAerase.symm
          rw [hEq] at hTcard
          omega
        · subst A
          have hEq : T = Z₂ := by simpa [hpZ₂] using hAerase.symm
          rw [hEq] at hTcard
          omega
      _ = 1 := by simp
  have hSidePTwo : 2 ≤ (blocker (pairSide H p q)).card :=
    blocker_card_ge_two_of_atMostOne_singletonRow
      (residual_isClutter _ _)
      (pairSide_rows_nonempty hHRows p q)
      (pairSide_blocker_rows_cardAtLeast_two hPair hBRows)
      hSidePSingleton
  have hSideQTwo : 2 ≤ (blocker (pairSide H q p)).card :=
    blocker_card_ge_two_of_atMostOne_singletonRow
      (residual_isClutter _ _)
      (pairSide_rows_nonempty hHRows q p)
      (pairSide_blocker_rows_cardAtLeast_two
        (by simpa [Finset.pair_comm] using hPair) hBRows)
      hSideQSingleton
  have hSum := pairSide_blocker_card_add_le hpq hPair
  by_cases hSidePThree : 3 ≤ (blocker (pairSide H p q)).card
  · by_cases hSideQThree : 3 ≤ (blocker (pairSide H q p)).card
    · omega
    · have hSideQcard : (blocker (pairSide H q p)).card = 2 := by omega
      have hSidePFour := fiveRow_pair_split_other_side_four_of_first_side_two
        (H := H) (p := q) (q := p) (X := Y) (Y := X) (Z₁ := Z₁) (Z₂ := Z₂)
        hpq.symm (by
          rw [hH]
          ext T
          simp [Finset.pair_comm, or_comm, or_left_comm])
        hHcard hHclutter hHRows hPairRows hBRows
        hqY hpY hqX hpX hqZ₁ hpZ₁ hqZ₂ hpZ₂ hSideQcard
      omega
  · have hSidePcard : (blocker (pairSide H p q)).card = 2 := by omega
    have hSideQFour := fiveRow_pair_split_other_side_four_of_first_side_two
      hpq hH hHcard hHclutter hHRows hPairRows hBRows
      hpX hqX hpY hqY hpZ₁ hqZ₁ hpZ₂ hqZ₂ hSidePcard
    omega

theorem pairSide_blocker_card_add_one_le {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {T : Row α}
    (hpq : p ≠ q) (hPair : ({p, q} : Row α) ∈ H)
    (hT : T ∈ blocker H) (hpT : p ∈ T) (hqT : q ∈ T) :
    (blocker (pairSide H p q)).card +
        (blocker (pairSide H q p)).card + 1 ≤ (blocker H).card := by
  let liftP : Row α → Row α := insert p
  let liftQ : Row α → Row α := insert q
  let left : Hypergraph α := (blocker (pairSide H p q)).image liftP
  let right : Hypergraph α := (blocker (pairSide H q p)).image liftQ
  let sides : Hypergraph α := left ∪ right
  have hLeftSubset : left ⊆ blocker H := by
    intro S hS
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hS
    exact pairSide_blocker_lift hPair hD
  have hRightSubset : right ⊆ blocker H := by
    intro S hS
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hS
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
    intro S hSleft hSright
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hSleft
    obtain ⟨F, hF, hEq⟩ := Finset.mem_image.mp hSright
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
  have hTNotSides : T ∉ sides := by
    intro hTSides
    simp only [sides, Finset.mem_union] at hTSides
    rcases hTSides with hTleft | hTright
    · obtain ⟨D, hD, hEq⟩ := Finset.mem_image.mp hTleft
      have hqD : q ∉ D :=
        (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H p q)
      have hqLift : q ∈ liftP D := hEq ▸ hqT
      simp only [liftP, Finset.mem_insert] at hqLift
      rcases hqLift with hqp | hqD'
      · exact hpq hqp.symm
      · exact hqD hqD'
    · obtain ⟨D, hD, hEq⟩ := Finset.mem_image.mp hTright
      have hpD : p ∉ D :=
        (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H q p)
      have hpLift : p ∈ liftQ D := hEq ▸ hpT
      simp only [liftQ, Finset.mem_insert] at hpLift
      rcases hpLift with hpq' | hpD'
      · exact hpq hpq'
      · exact hpD hpD'
  have hInsertSubset : insert T sides ⊆ blocker H := by
    apply Finset.insert_subset hT
    exact Finset.union_subset hLeftSubset hRightSubset
  have hSidesCard : sides.card =
      (blocker (pairSide H p q)).card + (blocker (pairSide H q p)).card := by
    calc
      sides.card = left.card + right.card := by
        change (left ∪ right).card = left.card + right.card
        exact Finset.card_union_of_disjoint hDisjoint
      _ = (blocker (pairSide H p q)).card +
          (blocker (pairSide H q p)).card := by
        rw [Finset.card_image_iff.mpr hLiftPInjective,
          Finset.card_image_iff.mpr hLiftQInjective]
  have hCard := Finset.card_le_card hInsertSubset
  rw [Finset.card_insert_of_notMem hTNotSides, hSidesCard] at hCard
  omega

theorem exists_singleton_row_of_blocker_card_eq_two_of_card_le_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBcard : (blocker H).card = 2) :
    ∃ x, ({x} : Row α) ∈ H := by
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker H := by simp [hBQ]
  have hQ₂b : Q₂ ∈ blocker H := by simp [hBQ]
  have hQ₁card : 2 ≤ Q₁.card := hBRows Q₁ hQ₁b
  have hQ₂card : 2 ≤ Q₂.card := hBRows Q₂ hQ₂b
  have hHtwo : H = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair hH hBQ
  have hInter : (Q₁ ∩ Q₂).Nonempty := by
    by_contra hnot
    have hDisjoint : Disjoint Q₁ Q₂ := disjoint_of_inter_not_nonempty hnot
    have hCrossSubset : crossPairRows Q₁ Q₂ ⊆ H := by
      intro T hT
      obtain ⟨a, haQ₁, b, hbQ₂, hTpair⟩ := mem_crossPairRows.mp hT
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inr
        ⟨a, Finset.mem_sdiff.mpr
            ⟨haQ₁, fun haQ₂ ↦ Finset.disjoint_left.mp hDisjoint haQ₁ haQ₂⟩,
          b, Finset.mem_sdiff.mpr
            ⟨hbQ₂, fun hbQ₁ ↦ Finset.disjoint_left.mp hDisjoint hbQ₁ hbQ₂⟩,
          hTpair⟩)
    have hCrossLower : 4 ≤ (crossPairRows Q₁ Q₂).card := by
      calc
        4 = 2 * 2 := rfl
        _ ≤ Q₁.card * Q₂.card := Nat.mul_le_mul hQ₁card hQ₂card
        _ ≤ (crossPairRows Q₁ Q₂).card :=
          card_mul_le_crossPairRows_card_of_disjoint hDisjoint
    have hCrossUpper := Finset.card_le_card hCrossSubset
    omega
  obtain ⟨x, hx⟩ := hInter
  refine ⟨x, ?_⟩
  rw [hHtwo]
  exact mem_twoRowBlockers.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem fiveRow_pair_bound_of_one_avoiding {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X₁ X₂ Y N : Row α}
    (hpq : p ≠ q) (hH : H = {{p, q}, X₁, X₂, Y, N})
    (hHcard : H.card = 5) (hHclutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX₁ : p ∈ X₁) (hqX₁ : q ∉ X₁)
    (hpX₂ : p ∈ X₂) (hqX₂ : q ∉ X₂)
    (hpY : p ∉ Y) (hqY : q ∈ Y)
    (hpN : p ∉ N) (hqN : q ∉ N) :
    6 ≤ (blocker H).card := by
  let P : Row α := Y.erase q
  let U : Hypergraph α := {X₁.erase p, X₂.erase p, N}
  let R : Hypergraph α := {X₁, X₂, Y, N}
  have hPair : ({p, q} : Row α) ∈ H := by simp [hH]
  have hX₁H : X₁ ∈ H := by simp [hH]
  have hX₂H : X₂ ∈ H := by simp [hH]
  have hYH : Y ∈ H := by simp [hH]
  have hNH : N ∈ H := by simp [hH]
  have hX₁card := hHRows X₁ hX₁H
  have hX₂card := hHRows X₂ hX₂H
  have hYcard := hHRows Y hYH
  have hNcard := hHRows N hNH
  have hX₁erasePositive : 1 ≤ (X₁.erase p).card := by
    rw [Finset.card_erase_of_mem hpX₁]
    omega
  have hX₂erasePositive : 1 ≤ (X₂.erase p).card := by
    rw [Finset.card_erase_of_mem hpX₂]
    omega
  have hPerasePositive : 1 ≤ P.card := by
    simp only [P, Finset.card_erase_of_mem hqY]
    omega
  have hPNotSubsetN : ¬P ⊆ N := by
    intro hSubset
    obtain ⟨y, hyP⟩ := Finset.card_pos.mp hPerasePositive
    apply false_of_two_point_transversal (p := p) (q := y) hBRows
    intro T hTH
    simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
    rcases hTH with rfl | rfl | rfl | rfl | rfl
    · exact ⟨p, by simp, by simp⟩
    · exact ⟨p, by simp, hpX₁⟩
    · exact ⟨p, by simp, hpX₂⟩
    · exact ⟨y, by simp, Finset.mem_of_mem_erase hyP⟩
    · exact ⟨y, by simp, hSubset hyP⟩
  have hNNotSubsetP : ¬N ⊆ P := by
    intro hSubset
    have hNY : N ⊆ Y := fun _ hx ↦ Finset.mem_of_mem_erase (hSubset hx)
    have hEq : N = Y := hHclutter hNH hYH hNY
    exact hqN (hEq ▸ hqY)
  have hLeftClutter : IsClutter ({P, N} : Hypergraph α) := by
    intro A hA B hB hAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · rfl
    · exact (hPNotSubsetN hAB).elim
    · exact (hNNotSubsetP hAB).elim
    · rfl
  have hAvoidP : avoidPoint H p = {Y, N} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hpT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hpT (by simp)).elim
      · exact (hpT hpX₁).elim
      · exact (hpT hpX₂).elim
      · simp
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hYH, hpY⟩
      · exact mem_avoidPoint.mpr ⟨hNH, hpN⟩
  have hDeleteQ : deletePoint ({Y, N} : Hypergraph α) q = {P, N} := by
    ext T
    simp [deletePoint, P, hqN]
  have hSideP : pairSide H p q = {P, N} := by
    rw [pairSide, residual, hAvoidP, hDeleteQ,
      minimize_eq_self_of_isClutter hLeftClutter]
  have hSidePBlockerRows : RowsCardAtLeast (blocker ({P, N} : Hypergraph α)) 2 := by
    simpa [hSideP] using pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  have hSidePProduct : P.card * N.card ≤ (blocker (pairSide H p q)).card := by
    rw [hSideP]
    exact twoRow_blocker_card_ge_product hSidePBlockerRows
  have hPNDisjoint : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro y hyP hyN
    have hSingleton : ({y} : Row α) ∈ blocker ({P, N} : Hypergraph α) := by
      rw [blocker_pairFamily]
      exact mem_twoRowBlockers.mpr
        (Or.inl ⟨y, Finset.mem_inter.mpr ⟨hyP, hyN⟩, rfl⟩)
    have hLarge := hSidePBlockerRows {y} hSingleton
    simp at hLarge
  have hAvoidQ : avoidPoint H q = {X₁, X₂, N} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTH, hqT⟩ := mem_avoidPoint.mp hT
      simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
      rcases hTH with rfl | rfl | rfl | rfl | rfl
      · exact (hqT (by simp)).elim
      · simp
      · simp
      · exact (hqT hqY).elim
      · simp
    · intro hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact mem_avoidPoint.mpr ⟨hX₁H, hqX₁⟩
      · exact mem_avoidPoint.mpr ⟨hX₂H, hqX₂⟩
      · exact mem_avoidPoint.mpr ⟨hNH, hqN⟩
  have hDeleteP : deletePoint ({X₁, X₂, N} : Hypergraph α) p = U := by
    ext T
    simp [deletePoint, U, hpN]
  have hSideQ : pairSide H q p = minimize U := by
    rw [pairSide, residual, hAvoidQ, hDeleteP]
  have hUupper : U.card ≤ 3 := by
    calc
      U.card ≤ ({X₂.erase p, N} : Hypergraph α).card + 1 := by
        simpa [U] using
          Finset.card_insert_le (X₁.erase p) ({X₂.erase p, N} : Hypergraph α)
      _ ≤ ({N} : Hypergraph α).card + 2 := by
        have := Finset.card_insert_le (X₂.erase p) ({N} : Hypergraph α)
        omega
      _ = 3 := by simp
  have hSideQupper : (pairSide H q p).card ≤ 3 := by
    rw [hSideQ]
    simpa [U] using (Finset.card_le_card (minimize_subset U)).trans hUupper
  have hPairNotR : ({p, q} : Row α) ∉ R := by
    intro hPairR
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hPairR
    rcases hPairR with hEq | hEq | hEq | hEq
    · exact hqX₁ (hEq ▸ (by simp))
    · exact hqX₂ (hEq ▸ (by simp))
    · exact hpY (hEq ▸ (by simp))
    · exact hpN (hEq ▸ (by simp))
  have hRcard : R.card = 4 := by
    have hHinsert : H = insert {p, q} R := by simp [hH, R]
    rw [hHinsert, Finset.card_insert_of_notMem hPairNotR] at hHcard
    omega
  have hNotBothXPairs (hKnown : Y.card = 2 ∨ N.card = 2) :
      ¬(X₁.card = 2 ∧ X₂.card = 2) := by
    rintro ⟨hX₁Pair, hX₂Pair⟩
    rcases hKnown with hYPair | hNPair
    · have hTriple : ({Y, X₁, X₂} : Hypergraph α).card = 3 := by
        apply triple_card_eq_three_of_quad_card_eq_four Y X₁ X₂ N
        have hEq : ({Y, X₁, X₂, N} : Hypergraph α) = R := by
          ext T
          simp [R, or_comm, or_left_comm]
        simpa [hEq] using hRcard
      have hLarge := third_row_large_of_pair_budget hHRows hPairRows
        hPair hYH hX₁H hX₂H (by simp [hpq]) hYPair hX₁Pair hTriple (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hqX₁ (h ▸ (by simp)),
            fun h ↦ hqX₂ (h ▸ (by simp))⟩)
      omega
    · have hTriple : ({N, X₁, X₂} : Hypergraph α).card = 3 := by
        apply triple_card_eq_three_of_quad_card_eq_four N X₁ X₂ Y
        have hEq : ({N, X₁, X₂, Y} : Hypergraph α) = R := by
          ext T
          simp [R, or_comm, or_left_comm]
        simpa [hEq] using hRcard
      have hLarge := third_row_large_of_pair_budget hHRows hPairRows
        hPair hNH hX₁H hX₂H (by simp [hpq]) hNPair hX₁Pair hTriple (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpN (h ▸ (by simp)),
            fun h ↦ hqX₁ (h ▸ (by simp)),
            fun h ↦ hqX₂ (h ▸ (by simp))⟩)
      omega
  have hSideQTwo (hNotBoth : ¬(X₁.card = 2 ∧ X₂.card = 2)) :
      2 ≤ (blocker (pairSide H q p)).card := by
    have hSmallSource : rowsCardAtMost (pairSide H q p) 1 ⊆
        ({X₁.erase p, X₂.erase p} : Hypergraph α) := by
      intro T hT
      obtain ⟨hTSide, hTcard⟩ := mem_rowsCardAtMost.mp hT
      have hTsource : T ∈ U := minimize_subset U (by simpa [hSideQ, U] using hTSide)
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hTsource
      rcases hTsource with hEq | hEq | hEq
      · simp [hEq]
      · simp [hEq]
      · have : T.card = N.card := congrArg Finset.card hEq
        omega
    have hSmallCard : (rowsCardAtMost (pairSide H q p) 1).card ≤ 1 := by
      by_contra hnot
      have hTwoSmall : 2 ≤ (rowsCardAtMost (pairSide H q p) 1).card := by omega
      have hSourceUpper : ({X₁.erase p, X₂.erase p} : Hypergraph α).card ≤ 2 := by
        calc
          ({X₁.erase p, X₂.erase p} : Hypergraph α).card ≤
              ({X₂.erase p} : Hypergraph α).card + 1 :=
            Finset.card_insert_le (X₁.erase p) ({X₂.erase p} : Hypergraph α)
          _ = 2 := by simp
      have hSmallEq : rowsCardAtMost (pairSide H q p) 1 =
          ({X₁.erase p, X₂.erase p} : Hypergraph α) := by
        apply Finset.eq_of_subset_of_card_le hSmallSource
        have hCard := Finset.card_le_card hSmallSource
        omega
      have hX₁small : (X₁.erase p).card ≤ 1 := by
        have : X₁.erase p ∈ rowsCardAtMost (pairSide H q p) 1 := by
          rw [hSmallEq]
          simp
        exact (mem_rowsCardAtMost.mp this).2
      have hX₂small : (X₂.erase p).card ≤ 1 := by
        have : X₂.erase p ∈ rowsCardAtMost (pairSide H q p) 1 := by
          rw [hSmallEq]
          simp
        exact (mem_rowsCardAtMost.mp this).2
      have hX₁Pair : X₁.card = 2 := by
        rw [Finset.card_erase_of_mem hpX₁] at hX₁small
        omega
      have hX₂Pair : X₂.card = 2 := by
        rw [Finset.card_erase_of_mem hpX₂] at hX₂small
        omega
      exact hNotBoth ⟨hX₁Pair, hX₂Pair⟩
    exact blocker_card_ge_two_of_atMostOne_singletonRow
      (residual_isClutter _ _)
      (pairSide_rows_nonempty hHRows q p)
      (pairSide_blocker_rows_cardAtLeast_two
        (by simpa [Finset.pair_comm] using hPair) hBRows)
      hSmallCard
  have hSum := pairSide_blocker_card_add_le hpq hPair
  by_cases hYPair : Y.card = 2
  · by_cases hNPair : N.card = 2
    · have hTripleX₁ : ({Y, N, X₁} : Hypergraph α).card = 3 := by
        apply triple_card_eq_three_of_quad_card_eq_four Y N X₁ X₂
        have hEq : ({Y, N, X₁, X₂} : Hypergraph α) = R := by
          ext T
          simp [R, or_comm, or_left_comm]
        simpa [hEq] using hRcard
      have hTripleX₂ : ({Y, N, X₂} : Hypergraph α).card = 3 := by
        apply triple_card_eq_three_of_quad_card_eq_four Y N X₂ X₁
        have hEq : ({Y, N, X₂, X₁} : Hypergraph α) = R := by
          ext T
          simp [R, or_comm, or_left_comm]
        simpa [hEq] using hRcard
      have hX₁Large := third_row_large_of_pair_budget hHRows hPairRows
        hPair hYH hNH hX₁H (by simp [hpq]) hYPair hNPair hTripleX₁ (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpN (h ▸ (by simp)),
            fun h ↦ hqX₁ (h ▸ (by simp))⟩)
      have hX₂Large := third_row_large_of_pair_budget hHRows hPairRows
        hPair hYH hNH hX₂H (by simp [hpq]) hYPair hNPair hTripleX₂ (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨fun h ↦ hpY (h ▸ (by simp)),
            fun h ↦ hpN (h ▸ (by simp)),
            fun h ↦ hqX₂ (h ▸ (by simp))⟩)
      have hURows : RowsCardAtLeast (pairSide H q p) 2 := by
        intro T hT
        have hTsource : T ∈ U := minimize_subset U (by simpa [hSideQ, U] using hT)
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hTsource
        rcases hTsource with hEq | hEq | hEq
        · have hErase : 2 ≤ (X₁.erase p).card := by
            rw [Finset.card_erase_of_mem hpX₁]
            omega
          simpa [← hEq] using hErase
        · have hErase : 2 ≤ (X₂.erase p).card := by
            rw [Finset.card_erase_of_mem hpX₂]
            omega
          simpa [← hEq] using hErase
        · simpa [← hEq] using hNPair.ge
      have hSideQnonempty : (pairSide H q p).Nonempty := by
        have hSource : X₁.erase p ∈ U := by simp [U]
        obtain ⟨T, hTmin, -⟩ := exists_minimize_subset hSource
        exact ⟨T, by simpa [hSideQ, U] using hTmin⟩
      have hSideQlower : 2 ≤ (pairSide H q p).card := by
        by_contra hnot
        have hCard : (pairSide H q p).card = 1 := by
          have := Finset.card_pos.mpr hSideQnonempty
          omega
        obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hCard
        have hASide : A ∈ pairSide H q p := by simp [hA]
        have hApositive : A.Nonempty := Finset.card_pos.mp (by
          have := hURows A hASide
          omega)
        obtain ⟨a, haA⟩ := hApositive
        have hSingleton : ({a} : Row α) ∈ blocker (pairSide H q p) := by
          rw [hA, blocker_singletonFamily]
          exact mem_singletonRows.mpr ⟨a, haA, rfl⟩
        have hLarge := pairSide_blocker_rows_cardAtLeast_two
          (H := H) (p := q) (q := p)
          (by simpa [Finset.pair_comm] using hPair) hBRows {a} hSingleton
        simp at hLarge
      have hSideQThree : 3 ≤ (blocker (pairSide H q p)).card := by
        have hCases : (pairSide H q p).card = 2 ∨ (pairSide H q p).card = 3 := by omega
        rcases hCases with hCard | hCard
        · obtain ⟨A, B, hAB, hSideQAB⟩ := Finset.card_eq_two.mp hCard
          have hArows := hURows A (by simp [hSideQAB])
          have hBrows := hURows B (by simp [hSideQAB])
          have hProduct : A.card * B.card ≤ (blocker (pairSide H q p)).card := by
            rw [hSideQAB]
            exact twoRow_blocker_card_ge_product (by
              simpa [hSideQAB] using pairSide_blocker_rows_cardAtLeast_two
                (H := H) (p := q) (q := p)
                (by simpa [Finset.pair_comm] using hPair) hBRows)
          have : 4 ≤ (blocker (pairSide H q p)).card := by
            calc
              4 = 2 * 2 := rfl
              _ ≤ A.card * B.card := Nat.mul_le_mul hArows hBrows
              _ ≤ (blocker (pairSide H q p)).card := hProduct
          omega
        · exact threeRow_blocker_card_ge_three
            (residual_isClutter _ _) hCard hURows
            (pairSide_blocker_rows_cardAtLeast_two
              (by simpa [Finset.pair_comm] using hPair) hBRows)
      obtain ⟨z, hzN⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
      have hExtra : ({p, q, z} : Row α) ∈ blocker H := by
        apply mem_blocker.mpr
        have hTransversal : IsTransversal H {p, q, z} := by
          intro A hAH
          simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hAH
          rcases hAH with rfl | rfl | rfl | rfl | rfl
          · exact ⟨p, by simp, by simp⟩
          · exact ⟨p, by simp, hpX₁⟩
          · exact ⟨p, by simp, hpX₂⟩
          · exact ⟨q, by simp, hqY⟩
          · exact ⟨z, by simp, hzN⟩
        apply hTransversal.minimal_of_privateRows
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxp | hxq | hxz
        · subst x
          have hAvoid : z ∉ X₁ ∨ z ∉ X₂ := by
            by_contra hnot
            push Not at hnot
            apply false_of_two_point_transversal (p := q) (q := z) hBRows
            intro A hAH
            simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hAH
            rcases hAH with rfl | rfl | rfl | rfl | rfl
            · exact ⟨q, by simp, by simp⟩
            · exact ⟨z, by simp, hnot.1⟩
            · exact ⟨z, by simp, hnot.2⟩
            · exact ⟨q, by simp, hqY⟩
            · exact ⟨z, by simp, hzN⟩
          rcases hAvoid with hzX₁ | hzX₂
          · exact ⟨X₁, hX₁H, by simp, hpX₁, by
              intro y hyT hyX₁
              simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
              rcases hyT with hyp | hyq | hyz
              · exact hyp
              · exact (hqX₁ (hyq ▸ hyX₁)).elim
              · exact (hzX₁ (hyz ▸ hyX₁)).elim⟩
          · exact ⟨X₂, hX₂H, by simp, hpX₂, by
              intro y hyT hyX₂
              simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
              rcases hyT with hyp | hyq | hyz
              · exact hyp
              · exact (hqX₂ (hyq ▸ hyX₂)).elim
              · exact (hzX₂ (hyz ▸ hyX₂)).elim⟩
        · subst x
          exact ⟨Y, hYH, by simp, hqY, by
            intro y hyT hyY
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
            rcases hyT with hyp | hyq | hyz
            · exact (hpY (hyp ▸ hyY)).elim
            · exact hyq
            · have hzP : z ∉ P := fun hzP ↦
                Finset.disjoint_left.mp hPNDisjoint hzP hzN
              have hzNotY : z ∉ Y := by
                intro hzY
                have hzq : z ≠ q := fun hzq ↦ hqN (hzq ▸ hzN)
                exact hzP (Finset.mem_erase.mpr ⟨hzq, hzY⟩)
              exact (hzNotY (hyz ▸ hyY)).elim⟩
        · subst x
          exact ⟨N, hNH, by simp, hzN, by
            intro y hyT hyN
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
            rcases hyT with hyp | hyq | hyz
            · exact (hpN (hyp ▸ hyN)).elim
            · exact (hqN (hyq ▸ hyN)).elim
            · exact hyz⟩
      have hAdd := pairSide_blocker_card_add_one_le hpq hPair hExtra (by simp) (by simp)
      have hSidePTwo : 2 ≤ (blocker (pairSide H p q)).card := by
        exact (Nat.mul_le_mul hPerasePositive hNcard).trans hSidePProduct
      omega
    · have hNLarge : 3 ≤ N.card := by omega
      have hSidePThree : 3 ≤ (blocker (pairSide H p q)).card := by
        exact (Nat.mul_le_mul hPerasePositive hNLarge).trans hSidePProduct
      have hNotBoth := hNotBothXPairs (Or.inl hYPair)
      have hSideQTwo' := hSideQTwo hNotBoth
      by_cases hSideQThree : 3 ≤ (blocker (pairSide H q p)).card
      · omega
      · have hSideQcard : (blocker (pairSide H q p)).card = 2 := by omega
        obtain ⟨u, huSide⟩ :=
          exists_singleton_row_of_blocker_card_eq_two_of_card_le_three
            (residual_isClutter _ _) hSideQupper
            (pairSide_blocker_rows_cardAtLeast_two
              (by simpa [Finset.pair_comm] using hPair) hBRows)
            hSideQcard
        have huSource : ({u} : Row α) ∈ U :=
          minimize_subset U (by
            change ({u} : Row α) ∈ pairSide H q p at huSide
            rw [hSideQ] at huSide
            exact huSide)
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at huSource
        rcases huSource with hEq | hEq | hEq
        · have hEraseEq : X₁.erase p = {u} := hEq.symm
          obtain ⟨z, hzN, hzu⟩ := Finset.exists_mem_ne (by omega : 1 < N.card) u
          have hExtra : ({p, q, z} : Row α) ∈ blocker H := by
            apply mem_blocker.mpr
            have hTransversal : IsTransversal H {p, q, z} := by
              intro A hAH
              simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hAH
              rcases hAH with rfl | rfl | rfl | rfl | rfl
              · exact ⟨p, by simp, by simp⟩
              · exact ⟨p, by simp, hpX₁⟩
              · exact ⟨p, by simp, hpX₂⟩
              · exact ⟨q, by simp, hqY⟩
              · exact ⟨z, by simp, hzN⟩
            apply hTransversal.minimal_of_privateRows
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with hxp | hxq | hxz
            · subst x
              exact ⟨X₁, hX₁H, by simp, hpX₁, by
                intro y hyT hyX₁
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact hyp
                · exact (hqX₁ (hyq ▸ hyX₁)).elim
                · have hzErase : z ∈ X₁.erase p :=
                    Finset.mem_erase.mpr
                      ⟨fun h ↦ hpN (h ▸ hzN), hyz ▸ hyX₁⟩
                  have hzu' : z = u := by simpa [hEraseEq] using hzErase
                  exact (hzu hzu').elim⟩
            · subst x
              exact ⟨Y, hYH, by simp, hqY, by
                intro y hyT hyY
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact (hpY (hyp ▸ hyY)).elim
                · exact hyq
                · have hzP : z ∉ P := fun hzP ↦
                    Finset.disjoint_left.mp hPNDisjoint hzP hzN
                  have hzNotY : z ∉ Y := by
                    intro hzY
                    exact hzP (Finset.mem_erase.mpr
                      ⟨fun h ↦ hqN (h ▸ hzN), hzY⟩)
                  exact (hzNotY (hyz ▸ hyY)).elim⟩
            · subst x
              exact ⟨N, hNH, by simp, hzN, by
                intro y hyT hyN
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact (hpN (hyp ▸ hyN)).elim
                · exact (hqN (hyq ▸ hyN)).elim
                · exact hyz⟩
          have hAdd := pairSide_blocker_card_add_one_le hpq hPair hExtra (by simp) (by simp)
          omega
        · have hEraseEq : X₂.erase p = {u} := hEq.symm
          obtain ⟨z, hzN, hzu⟩ := Finset.exists_mem_ne (by omega : 1 < N.card) u
          have hExtra : ({p, q, z} : Row α) ∈ blocker H := by
            apply mem_blocker.mpr
            have hTransversal : IsTransversal H {p, q, z} := by
              intro A hAH
              simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hAH
              rcases hAH with rfl | rfl | rfl | rfl | rfl
              · exact ⟨p, by simp, by simp⟩
              · exact ⟨p, by simp, hpX₁⟩
              · exact ⟨p, by simp, hpX₂⟩
              · exact ⟨q, by simp, hqY⟩
              · exact ⟨z, by simp, hzN⟩
            apply hTransversal.minimal_of_privateRows
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with hxp | hxq | hxz
            · subst x
              exact ⟨X₂, hX₂H, by simp, hpX₂, by
                intro y hyT hyX₂
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact hyp
                · exact (hqX₂ (hyq ▸ hyX₂)).elim
                · have hzErase : z ∈ X₂.erase p :=
                    Finset.mem_erase.mpr
                      ⟨fun h ↦ hpN (h ▸ hzN), hyz ▸ hyX₂⟩
                  have hzu' : z = u := by simpa [hEraseEq] using hzErase
                  exact (hzu hzu').elim⟩
            · subst x
              exact ⟨Y, hYH, by simp, hqY, by
                intro y hyT hyY
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact (hpY (hyp ▸ hyY)).elim
                · exact hyq
                · have hzP : z ∉ P := fun hzP ↦
                    Finset.disjoint_left.mp hPNDisjoint hzP hzN
                  have hzNotY : z ∉ Y := by
                    intro hzY
                    exact hzP (Finset.mem_erase.mpr
                      ⟨fun h ↦ hqN (h ▸ hzN), hzY⟩)
                  exact (hzNotY (hyz ▸ hyY)).elim⟩
            · subst x
              exact ⟨N, hNH, by simp, hzN, by
                intro y hyT hyN
                simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
                rcases hyT with hyp | hyq | hyz
                · exact (hpN (hyp ▸ hyN)).elim
                · exact (hqN (hyq ▸ hyN)).elim
                · exact hyz⟩
          have hAdd := pairSide_blocker_card_add_one_le hpq hPair hExtra (by simp) (by simp)
          omega
        · have : ({u} : Row α).card = N.card := congrArg Finset.card hEq
          simp at this
          omega
  · have hYLarge : 3 ≤ Y.card := by omega
    have hPEraseTwo : 2 ≤ P.card := by
      simp only [P, Finset.card_erase_of_mem hqY]
      omega
    by_cases hNPair : N.card = 2
    · have hSidePFour : 4 ≤ (blocker (pairSide H p q)).card := by
        calc
          4 = 2 * 2 := rfl
          _ ≤ P.card * N.card := Nat.mul_le_mul hPEraseTwo hNPair.ge
          _ ≤ (blocker (pairSide H p q)).card := hSidePProduct
      have hSideQTwo' := hSideQTwo (hNotBothXPairs (Or.inr hNPair))
      omega
    · have hNLarge : 3 ≤ N.card := by omega
      have hSidePSix : 6 ≤ (blocker (pairSide H p q)).card := by
        calc
          6 = 2 * 3 := rfl
          _ ≤ P.card * N.card := Nat.mul_le_mul hPEraseTwo hNLarge
          _ ≤ (blocker (pairSide H p q)).card := hSidePProduct
      omega

theorem false_of_fiveRow_pair_one_avoiding_same_side {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α} {X₁ X₂ X₃ N : Row α}
    (hH : H = {{p, q}, X₁, X₂, X₃, N})
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hpX₁ : p ∈ X₁) (hpX₂ : p ∈ X₂) (hpX₃ : p ∈ X₃)
    (hpN : p ∉ N) :
    False := by
  have hNH : N ∈ H := by simp [hH]
  have hNpositive : 0 < N.card := by
    have := hHRows N hNH
    omega
  obtain ⟨z, hzN⟩ := Finset.card_pos.mp hNpositive
  apply false_of_two_point_transversal (p := p) (q := z) hBRows
  intro T hTH
  simp only [hH, Finset.mem_insert, Finset.mem_singleton] at hTH
  rcases hTH with rfl | rfl | rfl | rfl | rfl
  · exact ⟨p, by simp, by simp⟩
  · exact ⟨p, by simp, hpX₁⟩
  · exact ⟨p, by simp, hpX₂⟩
  · exact ⟨p, by simp, hpX₃⟩
  · exact ⟨z, by simp, hzN⟩

theorem fiveRow_pair_residual_bound {α : Type*}
    [Fintype α]
    (H : Hypergraph α)
    (hHclutter : IsClutter H) (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hPairExists : ∃ E ∈ H, E.card = 2) :
    6 ≤ (blocker H).card := by
  classical
  obtain ⟨E, hEH, hEcard⟩ := hPairExists
  obtain ⟨p, q, hpq, hE⟩ := Finset.card_eq_two.mp hEcard
  subst E
  let K : Hypergraph α := H.erase {p, q}
  let X : Hypergraph α := K.filter fun A ↦ p ∈ A
  let Y : Hypergraph α := K.filter fun A ↦ q ∈ A
  let Z : Hypergraph α := K.filter fun A ↦ p ∉ A ∧ q ∉ A
  have hKcard : K.card = 4 := by
    simp only [K, Finset.card_erase_of_mem hEH]
    omega
  have hHbase : H = insert {p, q} K := by
    simpa [K] using (Finset.insert_erase hEH).symm
  have hNoBoth {A : Row α} (hAK : A ∈ K) : ¬(p ∈ A ∧ q ∈ A) := by
    rintro ⟨hpA, hqA⟩
    have hAE : A ≠ ({p, q} : Row α) := (Finset.mem_erase.mp (by simpa [K] using hAK)).1
    have hAH : A ∈ H := (Finset.mem_erase.mp (by simpa [K] using hAK)).2
    have hSubset : ({p, q} : Row α) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpA
      · exact hqA
    exact hAE (hHclutter hEH hAH hSubset).symm
  have hXProps {A : Row α} (hAX : A ∈ X) : A ∈ K ∧ p ∈ A ∧ q ∉ A := by
    have hAX' : A ∈ K.filter (fun B ↦ p ∈ B) := by simpa only [X] using hAX
    obtain ⟨hAK, hpA⟩ := Finset.mem_filter.mp hAX'
    exact ⟨hAK, hpA, fun hqA ↦ hNoBoth hAK ⟨hpA, hqA⟩⟩
  have hYProps {A : Row α} (hAY : A ∈ Y) : A ∈ K ∧ p ∉ A ∧ q ∈ A := by
    have hAY' : A ∈ K.filter (fun B ↦ q ∈ B) := by simpa only [Y] using hAY
    obtain ⟨hAK, hqA⟩ := Finset.mem_filter.mp hAY'
    exact ⟨hAK, fun hpA ↦ hNoBoth hAK ⟨hpA, hqA⟩, hqA⟩
  have hZProps {A : Row α} (hAZ : A ∈ Z) : A ∈ K ∧ p ∉ A ∧ q ∉ A := by
    have hAZ' : A ∈ K.filter (fun B ↦ p ∉ B ∧ q ∉ B) := by
      simpa only [Z] using hAZ
    obtain ⟨hAK, hpA, hqA⟩ := Finset.mem_filter.mp hAZ'
    exact ⟨hAK, hpA, hqA⟩
  have hPartition : K = X ∪ Y ∪ Z := by
    ext A
    constructor
    · intro hAK
      by_cases hpA : p ∈ A
      · have hAX : A ∈ X := by
          change A ∈ K.filter (fun B ↦ p ∈ B)
          exact Finset.mem_filter.mpr ⟨hAK, hpA⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hAX)
      · by_cases hqA : q ∈ A
        · have hAY : A ∈ Y := by
            change A ∈ K.filter (fun B ↦ q ∈ B)
            exact Finset.mem_filter.mpr ⟨hAK, hqA⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hAY)
        · have hAZ : A ∈ Z := by
            change A ∈ K.filter (fun B ↦ p ∉ B ∧ q ∉ B)
            exact Finset.mem_filter.mpr ⟨hAK, hpA, hqA⟩
          exact Finset.mem_union_right _ hAZ
    · intro hA
      simp only [Finset.mem_union] at hA
      rcases hA with (hAX | hAY) | hAZ
      · exact (hXProps hAX).1
      · exact (hYProps hAY).1
      · exact (hZProps hAZ).1
  have hXYDisjoint : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro A hAX hAY
    exact (hXProps hAX).2.2 (hYProps hAY).2.2
  have hXZDisjoint : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro A hAX hAZ
    exact (hZProps hAZ).2.1 (hXProps hAX).2.1
  have hYZDisjoint : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro A hAY hAZ
    exact (hZProps hAZ).2.2 (hYProps hAY).2.2
  have hXYZDisjoint : Disjoint (X ∪ Y) Z := by
    apply Finset.disjoint_left.mpr
    intro A hAXY hAZ
    simp only [Finset.mem_union] at hAXY
    rcases hAXY with hAX | hAY
    · exact Finset.disjoint_left.mp hXZDisjoint hAX hAZ
    · exact Finset.disjoint_left.mp hYZDisjoint hAY hAZ
  have hCardSum : X.card + Y.card + Z.card = 4 := by
    have hCard : K.card = (X ∪ Y).card + Z.card := by
      rw [hPartition, Finset.card_union_of_disjoint hXYZDisjoint]
    rw [Finset.card_union_of_disjoint hXYDisjoint] at hCard
    omega
  have hZcases : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 2 ∨ Z.card = 3 ∨ Z.card = 4 := by
    have hZupper : Z.card ≤ K.card := Finset.card_le_card (by
      intro A hAZ
      exact (hZProps hAZ).1)
    omega
  rcases hZcases with hZcard | hZcard | hZcard | hZcard | hZcard
  · have hZempty : Z = ∅ := Finset.card_eq_zero.mp hZcard
    exfalso
    apply false_of_two_point_transversal (p := p) (q := q) hBRows
    intro A hAH
    by_cases hAeq : A = ({p, q} : Row α)
    · subst A
      exact ⟨p, by simp, by simp⟩
    · have hAK : A ∈ K := by
        simpa [K, hAeq] using Finset.mem_erase.mpr ⟨hAeq, hAH⟩
      have hAXY : A ∈ X ∪ Y := by
        have : A ∈ X ∪ Y ∪ Z := by simpa [hPartition] using hAK
        simpa [hZempty] using this
      simp only [Finset.mem_union] at hAXY
      rcases hAXY with hAX | hAY
      · exact ⟨p, by simp, (hXProps hAX).2.1⟩
      · exact ⟨q, by simp, (hYProps hAY).2.2⟩
  · obtain ⟨N, hZ⟩ := Finset.card_eq_one.mp hZcard
    have hNZ : N ∈ Z := by simp [hZ]
    obtain ⟨hNK, hpN, hqN⟩ := hZProps hNZ
    have hXYcard : X.card + Y.card = 3 := by omega
    have hXcases : X.card = 0 ∨ X.card = 1 ∨ X.card = 2 ∨ X.card = 3 := by omega
    rcases hXcases with hXcard | hXcard | hXcard | hXcard
    · have hXempty : X = ∅ := Finset.card_eq_zero.mp hXcard
      have hYcard : Y.card = 3 := by omega
      obtain ⟨Y₁, Y₂, Y₃, -, -, -, hY⟩ := Finset.card_eq_three.mp hYcard
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      obtain ⟨-, hpY₂, hqY₂⟩ := hYProps (A := Y₂) (by simp [hY])
      obtain ⟨-, hpY₃, hqY₃⟩ := hYProps (A := Y₃) (by simp [hY])
      have hForm : H = {{q, p}, Y₁, Y₂, Y₃, N} := by
        rw [hHbase, hPartition, hXempty, hY, hZ]
        ext T
        simp [Finset.pair_comm, or_comm, or_left_comm]
      exact (false_of_fiveRow_pair_one_avoiding_same_side
        hForm hHRows hBRows hqY₁ hqY₂ hqY₃ hqN).elim
    · have hYcard : Y.card = 2 := by omega
      obtain ⟨X₁, hX⟩ := Finset.card_eq_one.mp hXcard
      obtain ⟨Y₁, Y₂, -, hY⟩ := Finset.card_eq_two.mp hYcard
      obtain ⟨-, hpX₁, hqX₁⟩ := hXProps (A := X₁) (by simp [hX])
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      obtain ⟨-, hpY₂, hqY₂⟩ := hYProps (A := Y₂) (by simp [hY])
      have hForm : H = {{q, p}, Y₁, Y₂, X₁, N} := by
        rw [hHbase, hPartition, hX, hY, hZ]
        ext T
        simp [Finset.pair_comm, or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_one_avoiding hpq.symm hForm hHcard hHclutter
        hHRows hPairRows hBRows hqY₁ hpY₁ hqY₂ hpY₂ hqX₁ hpX₁ hqN hpN
    · have hYcard : Y.card = 1 := by omega
      obtain ⟨X₁, X₂, -, hX⟩ := Finset.card_eq_two.mp hXcard
      obtain ⟨Y₁, hY⟩ := Finset.card_eq_one.mp hYcard
      obtain ⟨-, hpX₁, hqX₁⟩ := hXProps (A := X₁) (by simp [hX])
      obtain ⟨-, hpX₂, hqX₂⟩ := hXProps (A := X₂) (by simp [hX])
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      have hForm : H = {{p, q}, X₁, X₂, Y₁, N} := by
        rw [hHbase, hPartition, hX, hY, hZ]
        ext T
        simp [or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_one_avoiding hpq hForm hHcard hHclutter
        hHRows hPairRows hBRows hpX₁ hqX₁ hpX₂ hqX₂ hpY₁ hqY₁ hpN hqN
    · have hYempty : Y = ∅ := Finset.card_eq_zero.mp (by omega : Y.card = 0)
      obtain ⟨X₁, X₂, X₃, -, -, -, hX⟩ := Finset.card_eq_three.mp hXcard
      obtain ⟨-, hpX₁, -⟩ := hXProps (A := X₁) (by simp [hX])
      obtain ⟨-, hpX₂, -⟩ := hXProps (A := X₂) (by simp [hX])
      obtain ⟨-, hpX₃, -⟩ := hXProps (A := X₃) (by simp [hX])
      have hForm : H = {{p, q}, X₁, X₂, X₃, N} := by
        rw [hHbase, hPartition, hX, hYempty, hZ]
        ext T
        simp [or_comm, or_left_comm]
      exact (false_of_fiveRow_pair_one_avoiding_same_side
        hForm hHRows hBRows hpX₁ hpX₂ hpX₃ hpN).elim
  · obtain ⟨Z₁, Z₂, -, hZ⟩ := Finset.card_eq_two.mp hZcard
    obtain ⟨-, hpZ₁, hqZ₁⟩ := hZProps (A := Z₁) (by simp [hZ])
    obtain ⟨-, hpZ₂, hqZ₂⟩ := hZProps (A := Z₂) (by simp [hZ])
    have hXYcard : X.card + Y.card = 2 := by omega
    have hXcases : X.card = 0 ∨ X.card = 1 ∨ X.card = 2 := by omega
    rcases hXcases with hXcard | hXcard | hXcard
    · have hXempty : X = ∅ := Finset.card_eq_zero.mp hXcard
      have hYcard : Y.card = 2 := by omega
      obtain ⟨Y₁, Y₂, -, hY⟩ := Finset.card_eq_two.mp hYcard
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      obtain ⟨-, hpY₂, hqY₂⟩ := hYProps (A := Y₂) (by simp [hY])
      have hForm : H = {{q, p}, Y₁, Y₂, Z₁, Z₂} := by
        rw [hHbase, hPartition, hXempty, hY, hZ]
        ext T
        simp [Finset.pair_comm, or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_two_avoiding_same_side hpq.symm hForm hHcard
        hHclutter hHRows hPairRows hBRows hqY₁ hpY₁ hqY₂ hpY₂
        hqZ₁ hpZ₁ hqZ₂ hpZ₂
    · have hYcard : Y.card = 1 := by omega
      obtain ⟨X₁, hX⟩ := Finset.card_eq_one.mp hXcard
      obtain ⟨Y₁, hY⟩ := Finset.card_eq_one.mp hYcard
      obtain ⟨-, hpX₁, hqX₁⟩ := hXProps (A := X₁) (by simp [hX])
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      have hForm : H = {{p, q}, X₁, Y₁, Z₁, Z₂} := by
        rw [hHbase, hPartition, hX, hY, hZ]
        ext T
        simp [or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_two_avoiding_split hpq hForm hHcard hHclutter
        hHRows hPairRows hBRows hpX₁ hqX₁ hpY₁ hqY₁ hpZ₁ hqZ₁ hpZ₂ hqZ₂
    · have hYempty : Y = ∅ := Finset.card_eq_zero.mp (by omega : Y.card = 0)
      obtain ⟨X₁, X₂, -, hX⟩ := Finset.card_eq_two.mp hXcard
      obtain ⟨-, hpX₁, hqX₁⟩ := hXProps (A := X₁) (by simp [hX])
      obtain ⟨-, hpX₂, hqX₂⟩ := hXProps (A := X₂) (by simp [hX])
      have hForm : H = {{p, q}, X₁, X₂, Z₁, Z₂} := by
        rw [hHbase, hPartition, hX, hYempty, hZ]
        ext T
        simp [or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_two_avoiding_same_side hpq hForm hHcard
        hHclutter hHRows hPairRows hBRows hpX₁ hqX₁ hpX₂ hqX₂
        hpZ₁ hqZ₁ hpZ₂ hqZ₂
  · obtain ⟨Z₁, Z₂, Z₃, -, -, -, hZ⟩ := Finset.card_eq_three.mp hZcard
    obtain ⟨-, hpZ₁, hqZ₁⟩ := hZProps (A := Z₁) (by simp [hZ])
    obtain ⟨-, hpZ₂, hqZ₂⟩ := hZProps (A := Z₂) (by simp [hZ])
    obtain ⟨-, hpZ₃, hqZ₃⟩ := hZProps (A := Z₃) (by simp [hZ])
    have hXYcard : X.card + Y.card = 1 := by omega
    by_cases hXzero : X.card = 0
    · have hXempty : X = ∅ := Finset.card_eq_zero.mp hXzero
      have hYcard : Y.card = 1 := by omega
      obtain ⟨Y₁, hY⟩ := Finset.card_eq_one.mp hYcard
      obtain ⟨-, hpY₁, hqY₁⟩ := hYProps (A := Y₁) (by simp [hY])
      have hForm : H = {{q, p}, Y₁, Z₁, Z₂, Z₃} := by
        rw [hHbase, hPartition, hXempty, hY, hZ]
        ext T
        simp [Finset.pair_comm, or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_three_avoiding hpq.symm hForm hHcard hHclutter
        hHRows hPairRows hBRows hqY₁ hpY₁ hqZ₁ hpZ₁ hqZ₂ hpZ₂ hqZ₃ hpZ₃
    · have hXcard : X.card = 1 := by omega
      have hYempty : Y = ∅ := Finset.card_eq_zero.mp (by omega : Y.card = 0)
      obtain ⟨X₁, hX⟩ := Finset.card_eq_one.mp hXcard
      obtain ⟨-, hpX₁, hqX₁⟩ := hXProps (A := X₁) (by simp [hX])
      have hForm : H = {{p, q}, X₁, Z₁, Z₂, Z₃} := by
        rw [hHbase, hPartition, hX, hYempty, hZ]
        ext T
        simp [or_comm, or_left_comm]
      exact fiveRow_pair_bound_of_three_avoiding hpq hForm hHcard hHclutter
        hHRows hPairRows hBRows hpX₁ hqX₁ hpZ₁ hqZ₁ hpZ₂ hqZ₂ hpZ₃ hqZ₃
  · obtain ⟨Z₁, Z₂, Z₃, Z₄, -, -, -, -, -, -, hZ⟩ :=
      Finset.card_eq_four.mp hZcard
    have hXempty : X = ∅ := Finset.card_eq_zero.mp (by omega : X.card = 0)
    have hYempty : Y = ∅ := Finset.card_eq_zero.mp (by omega : Y.card = 0)
    obtain ⟨-, hpZ₁, hqZ₁⟩ := hZProps (A := Z₁) (by simp [hZ])
    obtain ⟨-, hpZ₂, hqZ₂⟩ := hZProps (A := Z₂) (by simp [hZ])
    obtain ⟨-, hpZ₃, hqZ₃⟩ := hZProps (A := Z₃) (by simp [hZ])
    obtain ⟨-, hpZ₄, hqZ₄⟩ := hZProps (A := Z₄) (by simp [hZ])
    have hForm : H = {{p, q}, Z₁, Z₂, Z₃, Z₄} := by
      rw [hHbase, hPartition, hXempty, hYempty, hZ]
      ext T
      simp [or_comm, or_left_comm]
    exact fiveRow_pair_bound_of_four_avoiding hpq hForm hHcard hHclutter
      hHRows hPairRows hBRows hpZ₁ hqZ₁ hpZ₂ hqZ₂ hpZ₃ hqZ₃ hpZ₄ hqZ₄
end AiMathLab.P0054.G413
