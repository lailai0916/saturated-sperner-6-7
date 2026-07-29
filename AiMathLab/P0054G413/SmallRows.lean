import AiMathLab.P0054G413.Residual
import Mathlib.Data.Finset.Prod

namespace AiMathLab.P0054.G413

noncomputable def singletonRows {α : Type*} [DecidableEq α] (E : Row α) : Hypergraph α := by
  classical
  exact E.image fun x ↦ {x}

noncomputable def crossPairRows {α : Type*} [DecidableEq α] (A B : Row α) : Hypergraph α := by
  classical
  exact A.biUnion fun a ↦ B.image fun b ↦ {a, b}

noncomputable def twoRowBlockers {α : Type*} [DecidableEq α]
    (A B : Row α) : Hypergraph α := by
  classical
  exact singletonRows (A ∩ B) ∪ crossPairRows (A \ B) (B \ A)

def rowsCardAtMost {α : Type*} (H : Hypergraph α) (n : Nat) : Hypergraph α :=
  H.filter fun E ↦ E.card ≤ n

@[simp]
theorem mem_singletonRows {α : Type*} [DecidableEq α] {E T : Row α} :
    T ∈ singletonRows E ↔ ∃ x ∈ E, {x} = T := by
  classical
  simp [singletonRows]

@[simp]
theorem mem_crossPairRows {α : Type*} [DecidableEq α] {A B T : Row α} :
    T ∈ crossPairRows A B ↔ ∃ a ∈ A, ∃ b ∈ B, {a, b} = T := by
  classical
  simp [crossPairRows]

@[simp]
theorem mem_twoRowBlockers {α : Type*} [DecidableEq α] {A B T : Row α} :
    T ∈ twoRowBlockers A B ↔
      (∃ x ∈ A ∩ B, {x} = T) ∨
      ∃ a ∈ A \ B, ∃ b ∈ B \ A, {a, b} = T := by
  classical
  simp [twoRowBlockers]

@[simp]
theorem mem_rowsCardAtMost {α : Type*} {H : Hypergraph α} {n : Nat} {E : Row α} :
    E ∈ rowsCardAtMost H n ↔ E ∈ H ∧ E.card ≤ n := by
  simp [rowsCardAtMost]

theorem blocker_singletonFamily {α : Type*} [Fintype α] [DecidableEq α] (E : Row α) :
    blocker {E} = singletonRows E := by
  classical
  ext T
  constructor
  · intro hT
    have hTmin := mem_blocker.mp hT
    obtain ⟨x, hxT, hxE⟩ := hTmin.prop E (by simp)
    have hsingle : IsTransversal ({E} : Hypergraph α) {x} := by
      intro A hA
      have hAE : A = E := by simpa using hA
      subst A
      exact ⟨x, by simp, hxE⟩
    have hsubset : ({x} : Row α) ⊆ T := Finset.singleton_subset_iff.mpr hxT
    have hreverse : T ⊆ {x} := hTmin.le_of_le hsingle hsubset
    have hEq : {x} = T := Finset.Subset.antisymm hsubset hreverse
    exact mem_singletonRows.mpr ⟨x, hxE, hEq⟩
  · intro hT
    obtain ⟨x, hxE, rfl⟩ := mem_singletonRows.mp hT
    apply mem_blocker.mpr
    refine ⟨?_, ?_⟩
    · intro A hA
      have hAE : A = E := by simpa using hA
      subst A
      exact ⟨x, by simp, hxE⟩
    · intro S hS hsub
      obtain ⟨y, hyS, hyE⟩ := hS E (by simp)
      have hyx : y = x := by simpa using hsub hyS
      simpa [hyx] using hyS

theorem blocker_pairFamily {α : Type*} [Fintype α] [DecidableEq α] (A B : Row α) :
    blocker {A, B} = twoRowBlockers A B := by
  classical
  ext T
  constructor
  · intro hT
    have hTmin := mem_blocker.mp hT
    obtain ⟨a, haT, haA⟩ := hTmin.prop A (by simp)
    obtain ⟨b, hbT, hbB⟩ := hTmin.prop B (by simp)
    by_cases hab : a = b
    · subst b
      have hsingle : IsTransversal ({A, B} : Hypergraph α) {a} := by
        intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        rcases hE with rfl | rfl
        · exact ⟨a, by simp, haA⟩
        · exact ⟨a, by simp, hbB⟩
      have hsubset : ({a} : Row α) ⊆ T := Finset.singleton_subset_iff.mpr haT
      have hreverse : T ⊆ {a} := hTmin.le_of_le hsingle hsubset
      have hEq : {a} = T := Finset.Subset.antisymm hsubset hreverse
      exact mem_twoRowBlockers.mpr
        (Or.inl ⟨a, Finset.mem_inter.mpr ⟨haA, hbB⟩, hEq⟩)
    · have hpair : IsTransversal ({A, B} : Hypergraph α) {a, b} := by
        intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        rcases hE with rfl | rfl
        · exact ⟨a, by simp, haA⟩
        · exact ⟨b, by simp, hbB⟩
      have hsubset : ({a, b} : Row α) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haT
        · exact hbT
      have hreverse : T ⊆ {a, b} := hTmin.le_of_le hpair hsubset
      have hEq : {a, b} = T := Finset.Subset.antisymm hsubset hreverse
      have haNotB : a ∉ B := by
        intro haB
        have hsingle : IsTransversal ({A, B} : Hypergraph α) {a} := by
          intro E hE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hE
          rcases hE with rfl | rfl
          · exact ⟨a, by simp, haA⟩
          · exact ⟨a, by simp, haB⟩
        have hTsub : T ⊆ {a} := hTmin.le_of_le hsingle (Finset.singleton_subset_iff.mpr haT)
        have hbEq : b = a := by simpa using hTsub hbT
        exact hab hbEq.symm
      have hbNotA : b ∉ A := by
        intro hbA
        have hsingle : IsTransversal ({A, B} : Hypergraph α) {b} := by
          intro E hE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hE
          rcases hE with rfl | rfl
          · exact ⟨b, by simp, hbA⟩
          · exact ⟨b, by simp, hbB⟩
        have hTsub : T ⊆ {b} := hTmin.le_of_le hsingle (Finset.singleton_subset_iff.mpr hbT)
        have haEq : a = b := by simpa using hTsub haT
        exact hab haEq
      exact mem_twoRowBlockers.mpr
        (Or.inr ⟨a, Finset.mem_sdiff.mpr ⟨haA, haNotB⟩,
          b, Finset.mem_sdiff.mpr ⟨hbB, hbNotA⟩, hEq⟩)
  · intro hT
    apply mem_blocker.mpr
    rcases mem_twoRowBlockers.mp hT with hsingle | hpair
    · obtain ⟨x, hx, rfl⟩ := hsingle
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
      have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
      refine ⟨?_, ?_⟩
      · intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        rcases hE with rfl | rfl
        · exact ⟨x, by simp, hxA⟩
        · exact ⟨x, by simp, hxB⟩
      · intro S hS hsub
        obtain ⟨y, hyS, hyA⟩ := hS A (by simp)
        have hyx : y = x := by simpa using hsub hyS
        simpa [hyx] using hyS
    · obtain ⟨a, ha, b, hb, rfl⟩ := hpair
      have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
      have haNotB : a ∉ B := (Finset.mem_sdiff.mp ha).2
      have hbB : b ∈ B := (Finset.mem_sdiff.mp hb).1
      have hbNotA : b ∉ A := (Finset.mem_sdiff.mp hb).2
      refine ⟨?_, ?_⟩
      · intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        rcases hE with rfl | rfl
        · exact ⟨a, by simp, haA⟩
        · exact ⟨b, by simp, hbB⟩
      · intro S hS hsub
        apply Finset.insert_subset_iff.mpr
        constructor
        · obtain ⟨x, hxS, hxA⟩ := hS A (by simp)
          have hx : x = a ∨ x = b := by simpa using hsub hxS
          rcases hx with rfl | rfl
          · exact hxS
          · exact (hbNotA hxA).elim
        · have hbS : b ∈ S := by
            obtain ⟨x, hxS, hxB⟩ := hS B (by simp)
            have hx : x = a ∨ x = b := by simpa using hsub hxS
            rcases hx with rfl | rfl
            · exact (haNotB hxB).elim
            · exact hxS
          simpa using hbS

theorem card_mul_le_crossPairRows_card_of_disjoint {α : Type*} [DecidableEq α]
    {A B : Row α} (hAB : Disjoint A B) :
    A.card * B.card ≤ (crossPairRows A B).card := by
  classical
  let pairRow : α × α → Row α := fun p ↦ {p.1, p.2}
  have hInjective : Set.InjOn pairRow (↑(A.product B) : Set (α × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ A.product B := hp
    have hq' : q ∈ A.product B := hq
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp hq'
    apply Prod.ext
    · have hpMem : p.1 ∈ pairRow q := by
        rw [← hEq]
        simp [pairRow]
      simp only [pairRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq
      · exact hpq
      · exact (Finset.disjoint_left.mp hAB hpA (hpq ▸ hqB)).elim
    · have hpqFirst : p.1 = q.1 := by
        have hpMem : p.1 ∈ pairRow q := by
          rw [← hEq]
          simp [pairRow]
        simp only [pairRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
        rcases hpMem with hpq | hpq
        · exact hpq
        · exact (Finset.disjoint_left.mp hAB hpA (hpq ▸ hqB)).elim
      have hpSecondMem : p.2 ∈ pairRow q := by
        rw [← hEq]
        simp [pairRow]
      simp only [pairRow, Finset.mem_insert, Finset.mem_singleton] at hpSecondMem
      rcases hpSecondMem with hpq | hpq
      · exact (Finset.disjoint_left.mp hAB (hpq ▸ hqA) hpB).elim
      · exact hpq
  have hImageSubset : (A.product B).image pairRow ⊆ crossPairRows A B := by
    intro E hE
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
    exact mem_crossPairRows.mpr ⟨p.1, hpA, p.2, hpB, rfl⟩
  calc
    A.card * B.card = (A.product B).card := (Finset.card_product A B).symm
    _ = ((A.product B).image pairRow).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (crossPairRows A B).card := Finset.card_le_card hImageSubset

theorem family_eq_singletonRows_of_blocker_eq_singleton {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) {Q : Row α}
    (hB : blocker H = {Q}) : H = singletonRows Q := by
  calc
    H = blocker (blocker H) := (blocker_involution hH).symm
    _ = blocker {Q} := congrArg blocker hB
    _ = singletonRows Q := blocker_singletonFamily Q

theorem family_eq_twoRowBlockers_of_blocker_eq_pair {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) {Q₁ Q₂ : Row α}
    (hB : blocker H = {Q₁, Q₂}) : H = twoRowBlockers Q₁ Q₂ := by
  calc
    H = blocker (blocker H) := (blocker_involution hH).symm
    _ = blocker {Q₁, Q₂} := congrArg blocker hB
    _ = twoRowBlockers Q₁ Q₂ := blocker_pairFamily Q₁ Q₂

theorem rowsCardAtMost_two_card_ge_two_of_blocker_card_eq_one {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBcard : (blocker H).card = 1) :
    2 ≤ (rowsCardAtMost H 2).card := by
  classical
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
  have hpairSubset : ({{q₁}, {q₂}} : Hypergraph α) ⊆ rowsCardAtMost H 2 := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact mem_rowsCardAtMost.mpr ⟨hq₁H, by simp⟩
    · exact mem_rowsCardAtMost.mpr ⟨hq₂H, by simp⟩
  have hcard := Finset.card_le_card hpairSubset
  simpa [Finset.singleton_inj, hqNe] using hcard

theorem rowsCardAtMost_two_card_ge_two_of_blocker_card_eq_two {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBcard : (blocker H).card = 2) :
    2 ≤ (rowsCardAtMost H 2).card := by
  classical
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker H := by simp [hBQ]
  have hQ₂b : Q₂ ∈ blocker H := by simp [hBQ]
  have hQ₁card : 2 ≤ Q₁.card := hBRows Q₁ hQ₁b
  have hQ₂card : 2 ≤ Q₂.card := hBRows Q₂ hQ₂b
  have hHtwo : H = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair hH hBQ
  by_cases hInter : (Q₁ ∩ Q₂).Nonempty
  · obtain ⟨z, hzInter⟩ := hInter
    have hQ₁notSubset : ¬ Q₁ ⊆ Q₂ := by
      intro hsub
      exact hQNe (blocker_isClutter H hQ₁b hQ₂b hsub)
    have hQ₂notSubset : ¬ Q₂ ⊆ Q₁ := by
      intro hsub
      exact hQNe.symm (blocker_isClutter H hQ₂b hQ₁b hsub)
    obtain ⟨a, haQ₁, haQ₂⟩ := Finset.not_subset.mp hQ₁notSubset
    obtain ⟨b, hbQ₂, hbQ₁⟩ := Finset.not_subset.mp hQ₂notSubset
    have hab : a ≠ b := fun hab ↦ haQ₂ (hab ▸ hbQ₂)
    have hsingleH : ({z} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨z, hzInter, rfl⟩)
    have hpairH : ({a, b} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inr
        ⟨a, Finset.mem_sdiff.mpr ⟨haQ₁, haQ₂⟩,
          b, Finset.mem_sdiff.mpr ⟨hbQ₂, hbQ₁⟩, rfl⟩)
    have hrowNe : ({z} : Row α) ≠ {a, b} := by
      intro hEq
      have hcardEq := congrArg Finset.card hEq
      simp [hab] at hcardEq
    have hpairSubset : ({{z}, {a, b}} : Hypergraph α) ⊆ rowsCardAtMost H 2 := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact mem_rowsCardAtMost.mpr ⟨hsingleH, by simp⟩
      · exact mem_rowsCardAtMost.mpr ⟨hpairH, Finset.card_le_two⟩
    have hcard := Finset.card_le_card hpairSubset
    simpa [Finset.card_pair hrowNe] using hcard
  · have hInterEmpty : Q₁ ∩ Q₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hInter
    obtain ⟨a₁, ha₁Q, a₂, ha₂Q, haNe⟩ := Finset.one_lt_card.mp hQ₁card
    obtain ⟨b, hbQ⟩ := Q₂.nonempty_of_ne_empty (by
      intro hQ₂empty
      rw [hQ₂empty] at hQ₂card
      simp at hQ₂card)
    have ha₁NotQ₂ : a₁ ∉ Q₂ := by
      intro ha₁Q₂
      have : a₁ ∈ Q₁ ∩ Q₂ := Finset.mem_inter.mpr ⟨ha₁Q, ha₁Q₂⟩
      rw [hInterEmpty] at this
      simp at this
    have ha₂NotQ₂ : a₂ ∉ Q₂ := by
      intro ha₂Q₂
      have : a₂ ∈ Q₁ ∩ Q₂ := Finset.mem_inter.mpr ⟨ha₂Q, ha₂Q₂⟩
      rw [hInterEmpty] at this
      simp at this
    have hbNotQ₁ : b ∉ Q₁ := by
      intro hbQ₁
      have : b ∈ Q₁ ∩ Q₂ := Finset.mem_inter.mpr ⟨hbQ₁, hbQ⟩
      rw [hInterEmpty] at this
      simp at this
    have hpair₁H : ({a₁, b} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inr
        ⟨a₁, Finset.mem_sdiff.mpr ⟨ha₁Q, ha₁NotQ₂⟩,
          b, Finset.mem_sdiff.mpr ⟨hbQ, hbNotQ₁⟩, rfl⟩)
    have hpair₂H : ({a₂, b} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inr
        ⟨a₂, Finset.mem_sdiff.mpr ⟨ha₂Q, ha₂NotQ₂⟩,
          b, Finset.mem_sdiff.mpr ⟨hbQ, hbNotQ₁⟩, rfl⟩)
    have hpairNe : ({a₁, b} : Row α) ≠ {a₂, b} := by
      intro hEq
      have ha₁mem : a₁ ∈ ({a₂, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁mem
      rcases ha₁mem with haEq | haEq
      · exact haNe haEq
      · exact ha₁NotQ₂ (haEq ▸ hbQ)
    have hpairSubset : ({{a₁, b}, {a₂, b}} : Hypergraph α) ⊆ rowsCardAtMost H 2 := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact mem_rowsCardAtMost.mpr ⟨hpair₁H, Finset.card_le_two⟩
      · exact mem_rowsCardAtMost.mpr ⟨hpair₂H, Finset.card_le_two⟩
    have hcard := Finset.card_le_card hpairSubset
    simpa [Finset.card_pair hpairNe] using hcard

theorem blocker_card_ge_three_of_atMostOne_smallRow {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHnonempty : RowsNonempty H)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hSmall : (rowsCardAtMost H 2).card ≤ 1) :
    3 ≤ (blocker H).card := by
  classical
  have hBpositive : 0 < (blocker H).card := Finset.card_pos.mpr (blocker_nonempty hHnonempty)
  by_contra hnot
  have hBupper : (blocker H).card ≤ 2 := by omega
  have hBcases : (blocker H).card = 0 ∨
      (blocker H).card = 1 ∨ (blocker H).card = 2 := by omega
  rcases hBcases with hBcard | hBcard | hBcard
  · omega
  · have htwo := rowsCardAtMost_two_card_ge_two_of_blocker_card_eq_one hH hBRows hBcard
    omega
  · have htwo := rowsCardAtMost_two_card_ge_two_of_blocker_card_eq_two hH hBRows hBcard
    omega

theorem blocker_card_ge_two_of_rows_cardAtLeast_two {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHnonempty : H.Nonempty)
    (hHRows : RowsCardAtLeast H 2) :
    2 ≤ (blocker H).card := by
  classical
  have hRowsNonempty : RowsNonempty H := by
    intro E hEH
    have hEcard := hHRows E hEH
    exact Finset.card_pos.mp (by omega : 0 < E.card)
  have hBpositive : 0 < (blocker H).card := Finset.card_pos.mpr (blocker_nonempty hRowsNonempty)
  by_contra hnot
  have hBcard : (blocker H).card = 1 := by omega
  obtain ⟨Q, hBQ⟩ := Finset.card_eq_one.mp hBcard
  have hHsingle : H = singletonRows Q :=
    family_eq_singletonRows_of_blocker_eq_singleton hH hBQ
  obtain ⟨E, hEH⟩ := hHnonempty
  have hEsingle : E ∈ singletonRows Q := by simpa [hHsingle] using hEH
  obtain ⟨q, -, hqE⟩ := mem_singletonRows.mp hEsingle
  have hEcard : E.card = 1 := by simp [← hqE]
  have hElarge := hHRows E hEH
  omega

theorem threeRow_blocker_card_ge_three {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
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
    have hsingleH : ({z} : Row α) ∈ H := by
      rw [hHtwo]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨z, hzInter, rfl⟩)
    have hsingleLarge := hHRows {z} hsingleH
    simp at hsingleLarge
  have hCrossSubset : crossPairRows Q₁ Q₂ ⊆ H := by
    intro E hE
    rw [hHtwo]
    rw [twoRowBlockers, Finset.sdiff_eq_self_of_disjoint hDisjoint,
      Finset.sdiff_eq_self_of_disjoint hDisjoint.symm]
    exact Finset.mem_union_right _ hE
  have hCrossLower : 4 ≤ (crossPairRows Q₁ Q₂).card := by
    have hmul := card_mul_le_crossPairRows_card_of_disjoint hDisjoint
    calc
      4 = 2 * 2 := rfl
      _ ≤ Q₁.card * Q₂.card := Nat.mul_le_mul hQ₁card hQ₂card
      _ ≤ (crossPairRows Q₁ Q₂).card := hmul
  have hHLower := Finset.card_le_card hCrossSubset
  omega

theorem blocker_minimize_insert_card_ge_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {D : Hypergraph α} {P : Row α}
    (hDRows : RowsCardAtLeast D 3) (hP : P.Nonempty)
    (hBRows : RowsCardAtLeast (blocker (minimize (insert P D))) 2) :
    3 ≤ (blocker (minimize (insert P D))).card := by
  let H : Hypergraph α := minimize (insert P D)
  have hH : IsClutter H := by
    simpa [H] using minimize_isClutter (insert P D)
  have hHRowsNonempty : RowsNonempty H := by
    intro E hEH
    have hEsource : E ∈ insert P D := minimize_subset _ hEH
    simp only [Finset.mem_insert] at hEsource
    rcases hEsource with rfl | hED
    · exact hP
    · exact Finset.card_pos.mp (by have := hDRows E hED; omega)
  have hSmall : (rowsCardAtMost H 2).card ≤ 1 := by
    calc
      (rowsCardAtMost H 2).card ≤ ({P} : Hypergraph α).card := by
        apply Finset.card_le_card
        intro E hEsmall
        obtain ⟨hEH, hEcard⟩ := mem_rowsCardAtMost.mp hEsmall
        have hEsource : E ∈ insert P D := minimize_subset _ hEH
        simp only [Finset.mem_insert] at hEsource
        rcases hEsource with rfl | hED
        · simp
        · have hElarge := hDRows E hED
          omega
      _ = 1 := Finset.card_singleton P
  exact blocker_card_ge_three_of_atMostOne_smallRow hH hHRowsNonempty
    (by simpa [H] using hBRows) hSmall

theorem blocker_minimize_insert_insert_card_ge_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {D : Hypergraph α} {P₁ P₂ : Row α}
    (hDRows : RowsCardAtLeast D 3) (hP₁ : 2 ≤ P₁.card) (hP₂ : 2 ≤ P₂.card) :
    2 ≤ (blocker (minimize (insert P₁ (insert P₂ D)))).card := by
  let H : Hypergraph α := minimize (insert P₁ (insert P₂ D))
  have hH : IsClutter H := by
    simpa [H] using minimize_isClutter (insert P₁ (insert P₂ D))
  have hHRows : RowsCardAtLeast H 2 := by
    intro E hEH
    have hEsource : E ∈ insert P₁ (insert P₂ D) := minimize_subset _ hEH
    simp only [Finset.mem_insert] at hEsource
    rcases hEsource with rfl | rfl | hED
    · exact hP₁
    · exact hP₂
    · exact (hDRows E hED).trans' (by omega)
  have hHnonempty : H.Nonempty := by
    have hP₁source : P₁ ∈ insert P₁ (insert P₂ D) := by simp
    obtain ⟨E, hEH, -⟩ := exists_minimize_subset hP₁source
    exact ⟨E, by simpa [H] using hEH⟩
  exact blocker_card_ge_two_of_rows_cardAtLeast_two hH hHnonempty hHRows

end AiMathLab.P0054.G413
