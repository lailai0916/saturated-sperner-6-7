import AiMathLab.P0054Sat6.LocalBounds

namespace AiMathLab.P0054.Sat6

open G413

abbrev WitnessGround := Fin 6

def witnessSmall : Hypergraph WitnessGround :=
  {{0, 2}, {0, 3}, {1, 2}, {1, 3}, {4, 5}}

def witnessLarge : Hypergraph WitnessGround :=
  {{0, 1, 4}, {0, 1, 5}, {2, 3, 4}, {2, 3, 5}}

theorem witnessSmall_card : witnessSmall.card = 5 := by
  decide

theorem witnessLarge_card : witnessLarge.card = 4 := by
  decide

theorem witnessSmall_isClutter : IsClutter witnessSmall := by
  classical
  simp [witnessSmall, IsClutter, Finset.subset_iff]

theorem witnessLarge_isClutter : IsClutter witnessLarge := by
  classical
  simp [witnessLarge, IsClutter, Finset.subset_iff]

theorem witnessSmall_rows : RowsCardAtLeast witnessSmall 2 := by
  intro E hE
  simp only [witnessSmall, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl <;> decide

theorem witnessLarge_rows : RowsCardAtLeast witnessLarge 3 := by
  intro E hE
  simp only [witnessLarge, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl <;> decide

theorem witnessSmall_transversal {S : Row WitnessGround}
    (hS : S ∈ witnessSmall) : IsTransversal witnessLarge S := by
  simp only [witnessSmall, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    simp [witnessLarge, IsTransversal]

theorem transversal_witnessLarge_contains_small (T : Row WitnessGround)
    (hT : IsTransversal witnessLarge T) :
    ∃ S ∈ witnessSmall, S ⊆ T := by
  simp only [witnessLarge, IsTransversal, Finset.mem_insert,
    Finset.mem_singleton] at hT
  have hChoices :
      (0 ∈ T ∧ 2 ∈ T) ∨ (0 ∈ T ∧ 3 ∈ T) ∨
      (1 ∈ T ∧ 2 ∈ T) ∨ (1 ∈ T ∧ 3 ∈ T) ∨
      (4 ∈ T ∧ 5 ∈ T) := by
    aesop (config := { maxRuleApplications := 1000 })
  have pairSubset {a b : WitnessGround} (h : a ∈ T ∧ b ∈ T) :
      ({a, b} : Row WitnessGround) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h.1
    · exact h.2
  rcases hChoices with h | h | h | h | h
  · exact ⟨{0, 2}, by simp [witnessSmall], pairSubset h⟩
  · exact ⟨{0, 3}, by simp [witnessSmall], pairSubset h⟩
  · exact ⟨{1, 2}, by simp [witnessSmall], pairSubset h⟩
  · exact ⟨{1, 3}, by simp [witnessSmall], pairSubset h⟩
  · exact ⟨{4, 5}, by simp [witnessSmall], pairSubset h⟩

theorem witness_blocker_large : blocker witnessLarge = witnessSmall := by
  classical
  ext T
  constructor
  · intro hT
    have hTmin := mem_blocker.mp hT
    obtain ⟨S, hS, hST⟩ :=
      transversal_witnessLarge_contains_small T hTmin.prop
    have hTS : T ⊆ S := hTmin.le_of_le (witnessSmall_transversal hS) hST
    have hEq : T = S := Finset.Subset.antisymm hTS hST
    simpa [hEq] using hS
  · intro hT
    apply mem_blocker.mpr
    refine ⟨witnessSmall_transversal hT, ?_⟩
    intro R hR hRT
    obtain ⟨S, hS, hSR⟩ := transversal_witnessLarge_contains_small R hR
    have hST : S ⊆ T := hSR.trans hRT
    have hEq : S = T := witnessSmall_isClutter hS hT hST
    simpa [hEq] using hSR

theorem witness_blocker_small : blocker witnessSmall = witnessLarge := by
  rw [← witness_blocker_large, blocker_involution witnessLarge_isClutter]

theorem witness_total_card : witnessSmall.card + witnessLarge.card = 9 := by
  rw [witnessSmall_card, witnessLarge_card]

theorem local_lower_of_three_four_bounds {α : Type*}
    [Fintype α]
    (S C : Hypergraph α)
    (hSClutter : IsClutter S)
    (hCClutter : IsClutter C)
    (hSC : S = blocker C)
    (hCS : C = blocker S)
    (hSRows : RowsCardAtLeast S 2)
    (hCRows : RowsCardAtLeast C 3)
    (hThree : ∀ H : Hypergraph α,
      IsClutter H →
      H.card = 3 →
      RowsCardAtLeast H 3 →
      RowsCardAtLeast (blocker H) 2 →
      7 ≤ (blocker H).card)
    (hFour : ∀ H : Hypergraph α,
      IsClutter H →
      H.card = 4 →
      RowsCardAtLeast H 2 →
      RowsCardAtLeast (blocker H) 3 →
      6 ≤ (blocker H).card) :
    9 ≤ S.card + C.card := by
  classical
  have hSRowsNonempty : RowsNonempty S := by
    intro E hE
    exact Finset.card_pos.mp (by have := hSRows E hE; omega)
  have hCRowsNonempty : RowsNonempty C := by
    intro E hE
    exact Finset.card_pos.mp (by have := hCRows E hE; omega)
  have hSNonempty : S.Nonempty := by
    rw [hSC]
    exact blocker_nonempty hCRowsNonempty
  have hCNonempty : C.Nonempty := by
    rw [hCS]
    exact blocker_nonempty hSRowsNonempty
  have hSCardLower : 3 ≤ S.card := by
    obtain ⟨E, hEC⟩ := hCNonempty
    have hEb : E ∈ blocker S := by simpa [← hCS] using hEC
    have hEle := minimalTransversal_card_le_rows (mem_blocker.mp hEb)
    exact (hCRows E hEC).trans hEle
  have hCCardLower : 2 ≤ C.card := by
    obtain ⟨E, hES⟩ := hSNonempty
    have hEb : E ∈ blocker C := by simpa [← hSC] using hES
    have hEle := minimalTransversal_card_le_rows (mem_blocker.mp hEb)
    exact (hSRows E hES).trans hEle
  have hBlockerCRows : RowsCardAtLeast (blocker C) 2 := by
    simpa [← hSC] using hSRows
  have hBlockerSRows : RowsCardAtLeast (blocker S) 3 := by
    simpa [← hCS] using hCRows
  by_cases hCtwo : C.card = 2
  · obtain ⟨C₁, C₂, hC₁C₂, hC⟩ := Finset.card_eq_two.mp hCtwo
    have hC₁mem : C₁ ∈ C := by simp [hC]
    have hC₂mem : C₂ ∈ C := by simp [hC]
    have hProduct : C₁.card * C₂.card ≤ (blocker C).card := by
      rw [hC]
      exact twoRow_blocker_card_ge_product (by simpa [hC] using hBlockerCRows)
    have hNine : 9 ≤ (blocker C).card := by
      calc
        9 = 3 * 3 := rfl
        _ ≤ C₁.card * C₂.card :=
          Nat.mul_le_mul (hCRows C₁ hC₁mem) (hCRows C₂ hC₂mem)
        _ ≤ (blocker C).card := hProduct
    rw [← hSC] at hNine
    omega
  by_cases hCthree : C.card = 3
  · have hSeven := hThree C hCClutter hCthree hCRows hBlockerCRows
    rw [← hSC] at hSeven
    omega
  have hCFour : 4 ≤ C.card := by omega
  by_cases hSthree : S.card = 3
  · have hEight := threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three
      hSthree hSRows hBlockerSRows
    rw [← hCS] at hEight
    omega
  by_cases hSfour : S.card = 4
  · have hSix := hFour S hSClutter hSfour hSRows hBlockerSRows
    rw [← hCS] at hSix
    omega
  omega

theorem local_lower {α : Type*}
    [Fintype α]
    (S C : Hypergraph α)
    (hSClutter : IsClutter S)
    (hCClutter : IsClutter C)
    (hSC : S = blocker C)
    (hCS : C = blocker S)
    (hSRows : RowsCardAtLeast S 2)
    (hCRows : RowsCardAtLeast C 3) :
    9 ≤ S.card + C.card := by
  exact local_lower_of_three_four_bounds S C hSClutter hCClutter hSC hCS
    hSRows hCRows
    (fun H hH hHcard hHRows hBRows ↦
      threeRow_blocker_card_ge_seven hH hHcard hHRows hBRows)
    (fun H hH hHcard hHRows hBRows ↦
      fourRow_blocker_card_ge_six hH hHcard hHRows hBRows)

end AiMathLab.P0054.Sat6
