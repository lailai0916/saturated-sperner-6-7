import AiMathLab.P0054G413
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases

namespace AiMathLab.P0054.G413

theorem threeRow_count_arithmetic (a₁ a₂ a₃ p₁ p₂ p₃ : Nat)
    (h₁ : 3 ≤ a₁ + p₂ + p₃)
    (h₂ : 3 ≤ a₂ + p₁ + p₃)
    (h₃ : 3 ≤ a₃ + p₁ + p₂) :
    7 ≤ a₁ * a₂ * a₃ + a₁ * p₁ + a₂ * p₂ + a₃ * p₃ +
      p₁ * p₂ + p₁ * p₃ + p₂ * p₃ := by
  have largeFirst (b₁ b₂ b₃ q₁ q₂ q₃ : Nat)
      (r₁ : 3 ≤ b₁ + q₂ + q₃)
      (r₂ : 3 ≤ b₂ + q₁ + q₃)
      (r₃ : 3 ≤ b₃ + q₁ + q₂)
      (hq₁ : 2 ≤ q₁) :
      7 ≤ b₁ * b₂ * b₃ + b₁ * q₁ + b₂ * q₂ + b₃ * q₃ +
        q₁ * q₂ + q₁ * q₃ + q₂ * q₃ := by
    by_contra hnot
    have hProductLower : 6 ≤ q₁ * (b₁ + q₂ + q₃) := by
      calc
        6 = 2 * 3 := rfl
        _ ≤ q₁ * (b₁ + q₂ + q₃) := Nat.mul_le_mul hq₁ r₁
    have hProductUpper : q₁ * (b₁ + q₂ + q₃) < 7 := by
      simp only [Nat.mul_add, Nat.add_assoc, Nat.mul_comm]
      omega
    have hProduct : q₁ * (b₁ + q₂ + q₃) = 6 := by omega
    have hSumPositive : 0 < b₁ + q₂ + q₃ := by omega
    have hq₁Upper : q₁ ≤ 6 := by
      calc
        q₁ = q₁ * 1 := by omega
        _ ≤ q₁ * (b₁ + q₂ + q₃) :=
          Nat.mul_le_mul_left q₁ hSumPositive
        _ = 6 := hProduct
    have hSumUpper : b₁ + q₂ + q₃ ≤ 6 := by
      calc
        b₁ + q₂ + q₃ = 1 * (b₁ + q₂ + q₃) := by omega
        _ ≤ q₁ * (b₁ + q₂ + q₃) :=
          Nat.mul_le_mul_right (b₁ + q₂ + q₃) (by omega)
        _ = 6 := hProduct
    have hFactors : q₁ = 2 ∧ b₁ + q₂ + q₃ = 3 := by
      interval_cases q₁ <;> omega
    obtain ⟨rfl, hSum⟩ := hFactors
    have hRemainder : b₁ * b₂ * b₃ + b₂ * q₂ + b₃ * q₃ + q₂ * q₃ = 0 := by
      simp only [Nat.add_assoc, Nat.mul_comm] at hProductUpper
      omega
    have hq₂q₃ : q₂ * q₃ = 0 := by omega
    rcases Nat.mul_eq_zero.mp hq₂q₃ with rfl | rfl
    · have hb₃ : 1 ≤ b₃ := by omega
      have hq₃ : q₃ = 0 := by
        have : b₃ * q₃ = 0 := by omega
        exact (Nat.mul_eq_zero.mp this).resolve_left (by omega)
      subst q₃
      have hb₂ : 1 ≤ b₂ := by omega
      have hb₁ : b₁ = 3 := by omega
      subst b₁
      have : 1 ≤ 3 * b₂ * b₃ := by
        calc
          1 = 1 * 1 * 1 := by decide
          _ ≤ 3 * b₂ * b₃ :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) hb₂) hb₃
      omega
    · have hb₂ : 1 ≤ b₂ := by omega
      have hq₂ : q₂ = 0 := by
        have : b₂ * q₂ = 0 := by omega
        exact (Nat.mul_eq_zero.mp this).resolve_left (by omega)
      subst q₂
      have hb₃ : 1 ≤ b₃ := by omega
      have hb₁ : b₁ = 3 := by omega
      subst b₁
      have : 1 ≤ 3 * b₂ * b₃ := by
        calc
          1 = 1 * 1 * 1 := by decide
          _ ≤ 3 * b₂ * b₃ :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) hb₂) hb₃
      omega
  by_cases hp₁ : 2 ≤ p₁
  · exact largeFirst a₁ a₂ a₃ p₁ p₂ p₃ h₁ h₂ h₃ hp₁
  by_cases hp₂ : 2 ≤ p₂
  · have := largeFirst a₂ a₁ a₃ p₂ p₁ p₃ h₂ h₁ (by omega) hp₂
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  by_cases hp₃ : 2 ≤ p₃
  · have := largeFirst a₃ a₁ a₂ p₃ p₁ p₂ h₃ (by omega) (by omega) hp₃
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpCases :
      (p₁ = 0 ∧ p₂ = 0 ∧ p₃ = 0) ∨
      (p₁ = 1 ∧ p₂ = 0 ∧ p₃ = 0) ∨
      (p₁ = 0 ∧ p₂ = 1 ∧ p₃ = 0) ∨
      (p₁ = 0 ∧ p₂ = 0 ∧ p₃ = 1) ∨
      (p₁ = 1 ∧ p₂ = 1 ∧ p₃ = 0) ∨
      (p₁ = 1 ∧ p₂ = 0 ∧ p₃ = 1) ∨
      (p₁ = 0 ∧ p₂ = 1 ∧ p₃ = 1) ∨
      (p₁ = 1 ∧ p₂ = 1 ∧ p₃ = 1) := by omega
  rcases hpCases with h | h | h | h | h | h | h | h
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  · have ha₁ : 3 ≤ a₁ := by omega
    have ha₂ : 3 ≤ a₂ := by omega
    have ha₃ : 3 ≤ a₃ := by omega
    have hProduct : 27 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 3 ≤ a₁ := by omega
    have ha₂ : 2 ≤ a₂ := by omega
    have ha₃ : 2 ≤ a₃ := by omega
    have hProduct : 12 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 2 ≤ a₁ := by omega
    have ha₂ : 3 ≤ a₂ := by omega
    have ha₃ : 2 ≤ a₃ := by omega
    have hProduct : 12 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 2 ≤ a₁ := by omega
    have ha₂ : 2 ≤ a₂ := by omega
    have ha₃ : 3 ≤ a₃ := by omega
    have hProduct : 12 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 2 ≤ a₁ := by omega
    have ha₂ : 2 ≤ a₂ := by omega
    have ha₃ : 1 ≤ a₃ := by omega
    have hProduct : 4 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 2 ≤ a₁ := by omega
    have ha₂ : 1 ≤ a₂ := by omega
    have ha₃ : 2 ≤ a₃ := by omega
    have hProduct : 4 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 1 ≤ a₁ := by omega
    have ha₂ : 2 ≤ a₂ := by omega
    have ha₃ : 2 ≤ a₃ := by omega
    have hProduct : 4 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega
  · have ha₁ : 1 ≤ a₁ := by omega
    have ha₂ : 1 ≤ a₂ := by omega
    have ha₃ : 1 ≤ a₃ := by omega
    have hProduct : 1 ≤ a₁ * a₂ * a₃ :=
      Nat.mul_le_mul (Nat.mul_le_mul ha₁ ha₂) ha₃
    omega

theorem firstRow_card_eq_incidence_parts {α : Type*} [DecidableEq α]
    {T₁ T₂ T₃ : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ T₁ ∧ x ∈ T₂ ∧ x ∈ T₃)) :
    T₁.card = (privatePart T₁ T₂ T₃).card +
      (sharedPart T₁ T₂ T₃).card + (sharedPart T₁ T₃ T₂).card := by
  have hPartition :
      T₁ = privatePart T₁ T₂ T₃ ∪
        sharedPart T₁ T₂ T₃ ∪ sharedPart T₁ T₃ T₂ := by
    ext x
    by_cases hx₁ : x ∈ T₁ <;>
      by_cases hx₂ : x ∈ T₂ <;>
      by_cases hx₃ : x ∈ T₃
    all_goals simp [privatePart, sharedPart, hx₁, hx₂, hx₃]
    exact (hNoCommon x ⟨hx₁, hx₂, hx₃⟩).elim
  have hFirstDisjoint :
      Disjoint (privatePart T₁ T₂ T₃) (sharedPart T₁ T₂ T₃) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxP
    have hxNotUnion := (Finset.mem_sdiff.mp hxA).2
    have hxT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxP).1).2
    exact hxNotUnion (Finset.mem_union_left _ hxT₂)
  have hSecondDisjoint :
      Disjoint (privatePart T₁ T₂ T₃ ∪ sharedPart T₁ T₂ T₃)
        (sharedPart T₁ T₃ T₂) := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hxA hxP
      have hxNotUnion := (Finset.mem_sdiff.mp hxA).2
      have hxT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxP).1).2
      exact hxNotUnion (Finset.mem_union_right _ hxT₃)
    · apply Finset.disjoint_left.mpr
      intro x hxP₂ hxP₃
      have hxNotT₃ := (Finset.mem_sdiff.mp hxP₂).2
      have hxT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxP₃).1).2
      exact hxNotT₃ hxT₃
  calc
    T₁.card = (privatePart T₁ T₂ T₃ ∪ sharedPart T₁ T₂ T₃ ∪
        sharedPart T₁ T₃ T₂).card := congrArg Finset.card hPartition
    _ = (privatePart T₁ T₂ T₃ ∪ sharedPart T₁ T₂ T₃).card +
        (sharedPart T₁ T₃ T₂).card :=
      Finset.card_union_of_disjoint hSecondDisjoint
    _ = (privatePart T₁ T₂ T₃).card +
        (sharedPart T₁ T₂ T₃).card +
        (sharedPart T₁ T₃ T₂).card := by
      rw [Finset.card_union_of_disjoint hFirstDisjoint]

theorem crossPairRows_disjoint_of_left_disjoint {α : Type*}
    [DecidableEq α] {A B C D : Row α}
    (hAC : Disjoint A C) (hAD : Disjoint A D) :
    Disjoint (crossPairRows A B) (crossPairRows C D) := by
  apply Finset.disjoint_left.mpr
  intro E hE₁ hE₂
  obtain ⟨a, ha, b, hb, hEq₁⟩ := mem_crossPairRows.mp hE₁
  obtain ⟨c, hc, d, hd, hEq₂⟩ := mem_crossPairRows.mp hE₂
  have hRowsEq : ({a, b} : Row α) = {c, d} := hEq₁.trans hEq₂.symm
  have hacd : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Row α) := by rw [← hRowsEq]; simp
    simpa using this
  rcases hacd with rfl | rfl
  · exact Finset.disjoint_left.mp hAC ha hc
  · exact Finset.disjoint_left.mp hAD ha hd

theorem crossPairRows_disjoint_of_one_side_disjoint {α : Type*}
    [DecidableEq α] {A B C D : Row α}
    (h : (Disjoint A C ∧ Disjoint A D) ∨
      (Disjoint B C ∧ Disjoint B D)) :
    Disjoint (crossPairRows A B) (crossPairRows C D) := by
  rcases h with h | h
  · exact crossPairRows_disjoint_of_left_disjoint h.1 h.2
  · have hComm : crossPairRows A B = crossPairRows B A := by
      ext E
      simp only [mem_crossPairRows]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨b, hb, a, ha, Finset.pair_comm _ _⟩
      · rintro ⟨b, hb, a, ha, rfl⟩
        exact ⟨a, ha, b, hb, Finset.pair_comm _ _⟩
    rw [hComm]
    exact crossPairRows_disjoint_of_left_disjoint (B := A) h.1 h.2

noncomputable def threeRowPairPart {α : Type*} [DecidableEq α]
    (T₁ T₂ T₃ : Row α) : Fin 6 → Hypergraph α
  | 0 => crossPairRows (privatePart T₁ T₂ T₃) (sharedPart T₂ T₃ T₁)
  | 1 => crossPairRows (privatePart T₂ T₁ T₃) (sharedPart T₁ T₃ T₂)
  | 2 => crossPairRows (privatePart T₃ T₁ T₂) (sharedPart T₁ T₂ T₃)
  | 3 => crossPairRows (sharedPart T₂ T₃ T₁) (sharedPart T₁ T₃ T₂)
  | 4 => crossPairRows (sharedPart T₂ T₃ T₁) (sharedPart T₁ T₂ T₃)
  | 5 => crossPairRows (sharedPart T₁ T₃ T₂) (sharedPart T₁ T₂ T₃)

theorem threeRow_pairParts_pairwiseDisjoint {α : Type*} [DecidableEq α]
    (T₁ T₂ T₃ : Row α) :
    (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint
      (threeRowPairPart T₁ T₂ T₃) := by
  intro i hi j hj hij
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.mk_one] at hij ⊢
  all_goals
    apply crossPairRows_disjoint_of_one_side_disjoint
    simp only [Finset.disjoint_left, privatePart, sharedPart,
      Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    aesop (config := { maxRuleApplications := 1000 })

theorem threeRow_pairParts_card_lower {α : Type*} [DecidableEq α]
    (T₁ T₂ T₃ : Row α) :
    (privatePart T₁ T₂ T₃).card * (sharedPart T₂ T₃ T₁).card +
      (privatePart T₂ T₁ T₃).card * (sharedPart T₁ T₃ T₂).card +
      (privatePart T₃ T₁ T₂).card * (sharedPart T₁ T₂ T₃).card +
      (sharedPart T₂ T₃ T₁).card * (sharedPart T₁ T₃ T₂).card +
      (sharedPart T₂ T₃ T₁).card * (sharedPart T₁ T₂ T₃).card +
      (sharedPart T₁ T₃ T₂).card * (sharedPart T₁ T₂ T₃).card ≤
      ((Finset.univ : Finset (Fin 6)).biUnion
        (threeRowPairPart T₁ T₂ T₃)).card := by
  classical
  have hDisjoint := threeRow_pairParts_pairwiseDisjoint T₁ T₂ T₃
  have endpointDisjoint (A B : Row α)
      (h : Disjoint A B) : A.card * B.card ≤ (crossPairRows A B).card :=
    card_mul_le_crossPairRows_card_of_disjoint h
  have h₀ := endpointDisjoint
    (privatePart T₁ T₂ T₃) (sharedPart T₂ T₃ T₁) (by
      simp only [Finset.disjoint_left, privatePart, sharedPart,
        Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      aesop)
  have h₁ := endpointDisjoint
    (privatePart T₂ T₁ T₃) (sharedPart T₁ T₃ T₂) (by
      simp only [Finset.disjoint_left, privatePart, sharedPart,
        Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      aesop)
  have h₂ := endpointDisjoint
    (privatePart T₃ T₁ T₂) (sharedPart T₁ T₂ T₃) (by
      simp only [Finset.disjoint_left, privatePart, sharedPart,
        Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      aesop)
  have h₃ := endpointDisjoint
    (sharedPart T₂ T₃ T₁) (sharedPart T₁ T₃ T₂) (by
      simp only [Finset.disjoint_left, sharedPart,
        Finset.mem_sdiff, Finset.mem_inter]
      aesop)
  have h₄ := endpointDisjoint
    (sharedPart T₂ T₃ T₁) (sharedPart T₁ T₂ T₃) (by
      simp only [Finset.disjoint_left, sharedPart,
        Finset.mem_sdiff, Finset.mem_inter]
      aesop)
  have h₅ := endpointDisjoint
    (sharedPart T₁ T₃ T₂) (sharedPart T₁ T₂ T₃) (by
      simp only [Finset.disjoint_left, sharedPart,
        Finset.mem_sdiff, Finset.mem_inter]
      aesop)
  rw [Finset.card_biUnion hDisjoint]
  simp [Fin.sum_univ_succ, threeRowPairPart] at *
  omega

theorem threeRow_pairParts_subset_pairRows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃}) :
    (Finset.univ : Finset (Fin 6)).biUnion
        (threeRowPairPart T₁ T₂ T₃) ⊆ pairRows (blocker K) := by
  intro E hE
  obtain ⟨i, _, hEPart⟩ := Finset.mem_biUnion.mp hE
  fin_cases i <;>
    simp only [threeRowPairPart, mem_crossPairRows] at hEPart <;>
    obtain ⟨x, hx, y, hy, rfl⟩ := hEPart
  all_goals
    apply Finset.mem_filter.mpr
    constructor
    · apply pair_mem_blocker_threeRows
      · intro T hT
        simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl | rfl <;>
          simp only [privatePart, sharedPart, Finset.mem_sdiff,
            Finset.mem_union, Finset.mem_inter] at hx hy <;>
          aesop
      · simp only [privatePart, sharedPart, Finset.mem_sdiff,
          Finset.mem_union, Finset.mem_inter] at hx hy
        aesop (config := { maxRuleApplications := 1000 })
      · simp only [privatePart, sharedPart, Finset.mem_sdiff,
          Finset.mem_union, Finset.mem_inter] at hx hy
        aesop (config := { maxRuleApplications := 1000 })
    · simp only [privatePart, sharedPart, Finset.mem_sdiff,
        Finset.mem_union, Finset.mem_inter] at hx hy
      have hxy : x ≠ y := by aesop
      simp [hxy]

theorem threeRow_blocker_card_ge_seven {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (_hHclutter : IsClutter H) (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    7 ≤ (blocker H).card := by
  classical
  obtain ⟨T₁, T₂, T₃, hT₁T₂, hT₁T₃, hT₂T₃, hH⟩ :=
    Finset.card_eq_three.mp hHcard
  have hNoCommon :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hH hBRows
  let a₁ := (privatePart T₁ T₂ T₃).card
  let a₂ := (privatePart T₂ T₁ T₃).card
  let a₃ := (privatePart T₃ T₁ T₂).card
  let p₁ := (sharedPart T₂ T₃ T₁).card
  let p₂ := (sharedPart T₁ T₃ T₂).card
  let p₃ := (sharedPart T₁ T₂ T₃).card
  have hT₁H : T₁ ∈ H := by simp [hH]
  have hT₂H : T₂ ∈ H := by simp [hH]
  have hT₃H : T₃ ∈ H := by simp [hH]
  have hRow₁ : 3 ≤ a₁ + p₂ + p₃ := by
    have hCard := firstRow_card_eq_incidence_parts hNoCommon
    have hLower := hHRows T₁ hT₁H
    simp only [a₁, p₂, p₃] at *
    omega
  have hNoCommon₂ : ∀ x, ¬(x ∈ T₂ ∧ x ∈ T₁ ∧ x ∈ T₃) := by
    intro x hx
    exact hNoCommon x ⟨hx.2.1, hx.1, hx.2.2⟩
  have hRow₂ : 3 ≤ a₂ + p₁ + p₃ := by
    have hCard := firstRow_card_eq_incidence_parts hNoCommon₂
    have hLower := hHRows T₂ hT₂H
    simp only [a₂, p₁, p₃] at *
    simpa [privatePart, sharedPart, Finset.union_comm, Finset.inter_comm,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLower.trans_eq hCard
  have hNoCommon₃ : ∀ x, ¬(x ∈ T₃ ∧ x ∈ T₁ ∧ x ∈ T₂) := by
    intro x hx
    exact hNoCommon x ⟨hx.2.1, hx.2.2, hx.1⟩
  have hRow₃ : 3 ≤ a₃ + p₁ + p₂ := by
    have hCard := firstRow_card_eq_incidence_parts hNoCommon₃
    have hLower := hHRows T₃ hT₃H
    simp only [a₃, p₁, p₂] at *
    simpa [privatePart, sharedPart, Finset.union_comm, Finset.inter_comm,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLower.trans_eq hCard
  have hCount := threeRow_count_arithmetic a₁ a₂ a₃ p₁ p₂ p₃
    hRow₁ hRow₂ hRow₃
  let pairParts := (Finset.univ : Finset (Fin 6)).biUnion
    (threeRowPairPart T₁ T₂ T₃)
  have hPairPartsLower := threeRow_pairParts_card_lower T₁ T₂ T₃
  have hPairPartsSubset := threeRow_pairParts_subset_pairRows hH
  have hPairLower :
      a₁ * p₁ + a₂ * p₂ + a₃ * p₃ + p₁ * p₂ + p₁ * p₃ + p₂ * p₃ ≤
        (pairRows (blocker H)).card := by
    calc
      a₁ * p₁ + a₂ * p₂ + a₃ * p₃ + p₁ * p₂ + p₁ * p₃ + p₂ * p₃ ≤
          pairParts.card := by
        simpa [a₁, a₂, a₃, p₁, p₂, p₃, pairParts] using hPairPartsLower
      _ ≤ (pairRows (blocker H)).card :=
        Finset.card_le_card (by simpa [pairParts] using hPairPartsSubset)
  have hTripleCard : (rowsCardExactly (blocker H) 3).card = a₁ * a₂ * a₃ := by
    simpa [a₁, a₂, a₃] using
      threeRow_triple_blockers_card hH hT₁T₂ hT₁T₃ hT₂T₃
  have hBlockerUpper {E : Row α} (hE : E ∈ blocker H) : E.card ≤ 3 := by
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hE)
    omega
  have hPartition :
      pairRows (blocker H) ∪ rowsCardExactly (blocker H) 3 = blocker H := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_union.mp hE with hPair | hTriple
      · exact (Finset.mem_filter.mp hPair).1
      · exact (mem_rowsCardExactly.mp hTriple).1
    · intro hE
      have hLower := hBRows E hE
      have hUpper := hBlockerUpper hE
      have hCases : E.card = 2 ∨ E.card = 3 := by omega
      rcases hCases with hCard | hCard
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE, hCard⟩)
      · exact Finset.mem_union_right _ (mem_rowsCardExactly.mpr ⟨hE, hCard⟩)
  have hDisjoint :
      Disjoint (pairRows (blocker H)) (rowsCardExactly (blocker H) 3) := by
    apply Finset.disjoint_left.mpr
    intro E hPair hTriple
    have hTwo := (Finset.mem_filter.mp hPair).2
    have hThree := (mem_rowsCardExactly.mp hTriple).2
    omega
  have hCardAdd :
      (pairRows (blocker H)).card + (rowsCardExactly (blocker H) 3).card =
        (blocker H).card := by
    calc
      (pairRows (blocker H)).card + (rowsCardExactly (blocker H) 3).card =
          (pairRows (blocker H) ∪ rowsCardExactly (blocker H) 3).card :=
        (Finset.card_union_of_disjoint hDisjoint).symm
      _ = (blocker H).card := congrArg Finset.card hPartition
  omega

theorem isolatedRow_lift_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {H K : Hypergraph α} {A T : Row α} {a : α}
    (hH : H = insert A K)
    (hAK : ∀ E ∈ K, Disjoint A E)
    (haA : a ∈ A) (hT : T ∈ blocker K) :
    insert a T ∈ blocker H := by
  have hTAvoids : ∀ x ∈ T, x ∉ A := by
    intro x hxT hxA
    obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
    exact Finset.disjoint_left.mp (hAK E hPrivate.1) hxA hPrivate.2.2.1
  apply mem_blocker.mpr
  have hTransversal : IsTransversal H (insert a T) := by
    intro E hEH
    simp only [hH, Finset.mem_insert] at hEH
    rcases hEH with rfl | hEK
    · exact ⟨a, by simp, haA⟩
    · obtain ⟨x, hxT, hxE⟩ := (mem_blocker.mp hT).prop E hEK
      exact ⟨x, by simp [hxT], hxE⟩
  apply hTransversal.minimal_of_privateRows
  intro x hx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hxT
  · exact ⟨A, by simp [hH], by simp, haA, by
      intro y hyRow hyA
      simp only [Finset.mem_insert] at hyRow
      rcases hyRow with rfl | hyT
      · rfl
      · exact (hTAvoids y hyT hyA).elim⟩
  · obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
    exact ⟨E, by simp [hH, hPrivate.1], by simp [hxT], hPrivate.2.2.1, by
      intro y hyRow hyE
      simp only [Finset.mem_insert] at hyRow
      rcases hyRow with rfl | hyT
      · exact (Finset.disjoint_left.mp (hAK E hPrivate.1) haA hyE).elim
      · exact hPrivate.2.2.2 hyT hyE⟩

theorem fourRows_blocker_card_ge_six_of_first_isolated {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {A B C D : Row α}
    (hHclutter : IsClutter H) (hHcard : H.card = 4)
    (hH : H = {A, B, C, D})
    (hRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) :
    6 ≤ (blocker H).card := by
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
  have hAH : A ∈ H := by simp [hH]
  have hAPositive : 0 < A.card := by
    have := hRows A hAH
    omega
  obtain ⟨a, haA⟩ := Finset.card_pos.mp hAPositive
  have hKRows : RowsCardAtLeast K 2 := by
    intro E hEK
    exact hRows E (hKsubset hEK)
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    intro T hTb
    have hLift := isolatedRow_lift_blocker hHK hAK haA hTb
    have hLiftCard := hBRows (insert a T) hLift
    have haT : a ∉ T := by
      intro haT
      obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hTb).exists_privateRow haT
      exact Finset.disjoint_left.mp (hAK E hPrivate.1) haA hPrivate.2.2.1
    rw [Finset.card_insert_of_notMem haT] at hLiftCard
    omega
  have hKcard : K.card = 3 := by
    have hErase : H.erase A = K := by
      rw [hHK]
      have hAnotK : A ∉ K := by
        intro hAKmem
        have hAA := hAK A hAKmem
        obtain ⟨x, hxA⟩ := Finset.card_pos.mp hAPositive
        exact Finset.disjoint_left.mp hAA hxA hxA
      simp [hAnotK]
    rw [← hErase, Finset.card_erase_of_mem hAH, hHcard]
  have hKBlockers : 3 ≤ (blocker K).card :=
    threeRow_blocker_card_ge_three hKclutter hKcard hKRows hBKRows
  have hProduct := isolatedRow_product_le_blocker_card hHK hAK
  have hACard := hRows A hAH
  calc
    6 = 2 * 3 := rfl
    _ ≤ A.card * (blocker K).card := Nat.mul_le_mul hACard hKBlockers
    _ ≤ (blocker H).card := hProduct

theorem false_of_pair_center_with_three_disjoint_neighbors {α : Type*}
    [DecidableEq α]
    {A B C D : Row α}
    (hAcard : A.card = 2)
    (hAB : (A ∩ B).Nonempty) (hAC : (A ∩ C).Nonempty)
    (hAD : (A ∩ D).Nonempty)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) : False := by
  obtain ⟨x, hx⟩ := hAB
  obtain ⟨y, hy⟩ := hAC
  obtain ⟨z, hz⟩ := hAD
  have hxA := (Finset.mem_inter.mp hx).1
  have hyA := (Finset.mem_inter.mp hy).1
  have hzA := (Finset.mem_inter.mp hz).1
  have hxy : x ≠ y := by
    intro hxy
    exact Finset.disjoint_left.mp hBC (Finset.mem_inter.mp hx).2
      (hxy ▸ (Finset.mem_inter.mp hy).2)
  have hxz : x ≠ z := by
    intro hxz
    exact Finset.disjoint_left.mp hBD (Finset.mem_inter.mp hx).2
      (hxz ▸ (Finset.mem_inter.mp hz).2)
  have hyz : y ≠ z := by
    intro hyz
    exact Finset.disjoint_left.mp hCD (Finset.mem_inter.mp hy).2
      (hyz ▸ (Finset.mem_inter.mp hz).2)
  have hSubset : ({x, y, z} : Row α) ⊆ A := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxA
    · exact hyA
    · exact hzA
  have hThree : 3 ≤ A.card := by
    have := Finset.card_le_card hSubset
    simpa [hxy, hxz, hyz] using this
  omega

theorem fourPairRows_blocker_card_ge_six {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hHclutter : IsClutter H) (hHcard : H.card = 4)
    (hRows : RowsCardAtLeast H 2)
    (hAllPairs : ∀ E ∈ H, E.card = 2)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    6 ≤ (blocker H).card := by
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
    (by rw [hH]; ext T; simp [or_left_comm]) hBRows
  have hADBC : ¬(ad ∧ bc) := opposite_intersections_not_both_nonempty
    (by rw [hH]; ext T; simp [or_comm, or_left_comm]) hBRows
  have hHB : H = {B, A, C, D} := by
    rw [hH]
    ext T
    simp [or_left_comm]
  have hHC : H = {C, A, B, D} := by
    rw [hH]
    ext T
    simp [or_left_comm]
  have hHD : H = {D, A, B, C} := by
    rw [hH]
    ext T
    simp [or_comm, or_left_comm]
  have isolatedA (h : ¬ab ∧ ¬ac ∧ ¬ad) : 6 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_six_of_first_isolated hHclutter hHcard hH hRows hBRows
      (disjoint_of_inter_not_nonempty h.1)
      (disjoint_of_inter_not_nonempty h.2.1)
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedB (h : ¬ab ∧ ¬bc ∧ ¬bd) : 6 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_six_of_first_isolated
      (A := B) (B := A) (C := C) (D := D) hHclutter hHcard hHB hRows hBRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1)
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedC (h : ¬ac ∧ ¬bc ∧ ¬cd) : 6 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_six_of_first_isolated
      (A := C) (B := A) (C := B) (D := D) hHclutter hHcard hHC hRows hBRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1).symm
      (disjoint_of_inter_not_nonempty h.2.2)
  have isolatedD (h : ¬ad ∧ ¬bd ∧ ¬cd) : 6 ≤ (blocker H).card :=
    fourRows_blocker_card_ge_six_of_first_isolated
      (A := D) (B := A) (C := B) (D := C) hHclutter hHcard hHD hRows hBRows
      (disjoint_of_inter_not_nonempty h.1).symm
      (disjoint_of_inter_not_nonempty h.2.1).symm
      (disjoint_of_inter_not_nonempty h.2.2).symm
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
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
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
      exact (false_of_pair_center_with_three_disjoint_neighbors
        (hAllPairs A hAH) hab hac had
        (disjoint_of_inter_not_nonempty hbc)
        (disjoint_of_inter_not_nonempty hbd)
        (disjoint_of_inter_not_nonempty hcd)).elim
    · have had : ¬ad := fun had ↦ hADBC ⟨had, hbc⟩
      have hbd : bd := by
        rcases hDneighbor with had' | hbd | hcd'
        · exact (had had').elim
        · exact hbd
        · exact (hcd hcd').elim
      have hac : ¬ac := fun hac ↦ hACBD ⟨hac, hbd⟩
      exact (false_of_pair_center_with_three_disjoint_neighbors
        (hAllPairs B hBH) (by simpa [ab, Finset.inter_comm] using hab) hbc hbd
        (disjoint_of_inter_not_nonempty hac)
        (disjoint_of_inter_not_nonempty had)
        (disjoint_of_inter_not_nonempty hcd)).elim
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
      exact (false_of_pair_center_with_three_disjoint_neighbors
        (hAllPairs C hCH) (by simpa [ac, Finset.inter_comm] using hac)
        (by simpa [bc, Finset.inter_comm] using hbc) hcd
        (disjoint_of_inter_not_nonempty hab)
        (disjoint_of_inter_not_nonempty had)
        (disjoint_of_inter_not_nonempty hbd)).elim
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
      exact (false_of_pair_center_with_three_disjoint_neighbors
        (hAllPairs D hDH) (by simpa [ad, Finset.inter_comm] using had)
        (by simpa [bd, Finset.inter_comm] using hbd)
        (by simpa [cd, Finset.inter_comm] using hcd)
        (disjoint_of_inter_not_nonempty hab)
        (disjoint_of_inter_not_nonempty hac)
        (disjoint_of_inter_not_nonempty hbc)).elim

theorem fourRow_blocker_card_ge_six {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hHclutter : IsClutter H) (hHcard : H.card = 4)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    6 ≤ (blocker H).card := by
  classical
  by_cases hPairs : (pairRows H).card ≤ 3
  · exact fourRow_residual_bound H hHclutter hHcard hHRows hPairs hBRows
  · have hPairSubset : pairRows H ⊆ H := fun _ hE ↦ (Finset.mem_filter.mp hE).1
    have hPairUpper := Finset.card_le_card hPairSubset
    have hPairCard : (pairRows H).card = 4 := by omega
    have hPairEq : pairRows H = H :=
      Finset.eq_of_subset_of_card_le hPairSubset (by omega)
    have hAllPairs : ∀ E ∈ H, E.card = 2 := by
      intro E hEH
      have hEPair : E ∈ pairRows H := by simpa [hPairEq] using hEH
      exact (Finset.mem_filter.mp hEPair).2
    exact fourPairRows_blocker_card_ge_six hHclutter hHcard hHRows hAllPairs hBRows

end AiMathLab.P0054.G413
