import AiMathLab.P0054AdjacentSix
import AiMathLab.P0054AdjacentFour

/-!
# Exact arbitrary-finite adjacent local parameter

This file combines the cardinality branches into the lower bound twelve and
checks an explicit pair of mutual blockers attaining it.  Thus the local
parameter customarily denoted `m(2,4)` is formalized without restricting the
ambient finite type.
-/

namespace AiMathLab.P0054.AdjacentExact

open AiMathLab.P0054.G413

theorem mutual_blocker_total_card_ge_twelve {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHClutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    12 ≤ H.card + (blocker H).card := by
  classical
  have hHRowsNonempty : RowsNonempty H := by
    intro E hE
    exact Finset.card_pos.mp (by
      have := hHRows E hE
      omega)
  obtain ⟨T, hTBlocker⟩ := blocker_nonempty hHRowsNonempty
  have hHCardLower : 4 ≤ H.card := by
    have hTUpper := minimalTransversal_card_le_rows (mem_blocker.mp hTBlocker)
    exact (hBRows T hTBlocker).trans hTUpper
  have hBlockerCardLower : 2 ≤ (blocker H).card := by
    obtain ⟨E, hEH⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
    have hEDouble : E ∈ blocker (blocker H) := by
      rw [blocker_involution hHClutter]
      exact hEH
    have hEUpper := minimalTransversal_card_le_rows (mem_blocker.mp hEDouble)
    exact (hHRows E hEH).trans hEUpper
  have hDoubleRows : RowsCardAtLeast (blocker (blocker H)) 2 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  by_cases hBTwo : (blocker H).card = 2
  · have hSixteen := AiMathLab.P0054.AdjacentLower.blocker_card_ge_sixteen_of_card_eq_two
      (H := blocker H) hBTwo hBRows hDoubleRows
    rw [blocker_involution hHClutter] at hSixteen
    omega
  by_cases hBThree : (blocker H).card = 3
  · have hTwelve := AiMathLab.P0054.AdjacentLower.blocker_card_ge_twelve_of_card_eq_three
      (H := blocker H) hBThree hBRows hDoubleRows
    rw [blocker_involution hHClutter] at hTwelve
    omega
  by_cases hBFour : (blocker H).card = 4
  · have hEight := AiMathLab.P0054.AdjacentFour.four_set_blocker_card_ge_eight
      (H := blocker H) (blocker_isClutter H) hBFour hBRows hDoubleRows
    rw [blocker_involution hHClutter] at hEight
    omega
  have hBAtLeastFive : 5 ≤ (blocker H).card := by omega
  by_cases hHFour : H.card = 4
  · have hSixteen := AiMathLab.P0054.AdjacentLower.blocker_card_ge_sixteen_of_card_eq_four
      hHFour hHRows hBRows
    omega
  by_cases hHFive : H.card = 5
  · have hEight := AiMathLab.P0054.AdjacentLower.blocker_card_ge_eight_of_card_eq_five
      hHFive hHRows hBRows
    omega
  by_cases hHSix : H.card = 6
  · have hSix := AiMathLab.P0054.AdjacentSix.blocker_card_ge_six_of_card_eq_six
      hHClutter hHSix hHRows hBRows
    omega
  omega

abbrev WitnessGround := Fin 8

def witnessTwoRows : G413.Hypergraph WitnessGround :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 0}, {4, 5}, {5, 6}, {6, 7}, {7, 4}}

def witnessFourRows : G413.Hypergraph WitnessGround :=
  {{0, 2, 4, 6}, {0, 2, 5, 7}, {1, 3, 4, 6}, {1, 3, 5, 7}}

theorem witnessTwoRows_card : witnessTwoRows.card = 8 := by
  decide

theorem witnessFourRows_card : witnessFourRows.card = 4 := by
  decide

theorem witnessTwoRows_isClutter : IsClutter witnessTwoRows := by
  classical
  simp [witnessTwoRows, IsClutter, Finset.subset_iff]

theorem witnessFourRows_isClutter : IsClutter witnessFourRows := by
  classical
  simp [witnessFourRows, IsClutter, Finset.subset_iff]

theorem witnessTwoRows_rows : RowsCardAtLeast witnessTwoRows 2 := by
  intro E hE
  simp only [witnessTwoRows, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem witnessFourRows_rows : RowsCardAtLeast witnessFourRows 4 := by
  intro E hE
  simp only [witnessFourRows, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl <;> decide

theorem witnessFourRows_transversal {C : G413.Row WitnessGround}
    (hC : C ∈ witnessFourRows) : IsTransversal witnessTwoRows C := by
  simp only [witnessFourRows, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    simp [witnessTwoRows, IsTransversal]

theorem transversal_witnessTwoRows_contains_four
    (T : G413.Row WitnessGround) (hT : IsTransversal witnessTwoRows T) :
    ∃ C ∈ witnessFourRows, C ⊆ T := by
  simp only [witnessTwoRows, IsTransversal, Finset.mem_insert,
    Finset.mem_singleton] at hT
  have hChoices :
      (((0 : WitnessGround) ∈ T ∧ (2 : WitnessGround) ∈ T) ∨
        ((1 : WitnessGround) ∈ T ∧ (3 : WitnessGround) ∈ T)) ∧
      (((4 : WitnessGround) ∈ T ∧ (6 : WitnessGround) ∈ T) ∨
        ((5 : WitnessGround) ∈ T ∧ (7 : WitnessGround) ∈ T)) := by
    aesop (config := { maxRuleApplications := 2000 })
  have fourSubset {a b c d : WitnessGround}
      (h : a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T) :
      ({a, b, c, d} : G413.Row WitnessGround) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  rcases hChoices with ⟨h02 | h13, h46 | h57⟩
  · exact ⟨{0, 2, 4, 6}, by simp [witnessFourRows],
      fourSubset ⟨h02.1, h02.2, h46.1, h46.2⟩⟩
  · exact ⟨{0, 2, 5, 7}, by simp [witnessFourRows],
      fourSubset ⟨h02.1, h02.2, h57.1, h57.2⟩⟩
  · exact ⟨{1, 3, 4, 6}, by simp [witnessFourRows],
      fourSubset ⟨h13.1, h13.2, h46.1, h46.2⟩⟩
  · exact ⟨{1, 3, 5, 7}, by simp [witnessFourRows],
      fourSubset ⟨h13.1, h13.2, h57.1, h57.2⟩⟩

theorem witness_blocker_two : blocker witnessTwoRows = witnessFourRows := by
  classical
  ext T
  constructor
  · intro hT
    have hTMinimal := mem_blocker.mp hT
    obtain ⟨C, hC, hCT⟩ :=
      transversal_witnessTwoRows_contains_four T hTMinimal.prop
    have hTC : T ⊆ C := hTMinimal.le_of_le (witnessFourRows_transversal hC) hCT
    have hEq : T = C := Finset.Subset.antisymm hTC hCT
    simpa [hEq] using hC
  · intro hT
    apply mem_blocker.mpr
    refine ⟨witnessFourRows_transversal hT, ?_⟩
    intro R hR hRT
    obtain ⟨C, hC, hCR⟩ := transversal_witnessTwoRows_contains_four R hR
    have hCT : C ⊆ T := hCR.trans hRT
    have hEq : C = T := witnessFourRows_isClutter hC hT hCT
    simpa [hEq] using hCR

theorem witness_blocker_four : blocker witnessFourRows = witnessTwoRows := by
  rw [← witness_blocker_two, blocker_involution witnessTwoRows_isClutter]

theorem witness_total_card : witnessTwoRows.card + witnessFourRows.card = 12 := by
  rw [witnessTwoRows_card, witnessFourRows_card]

theorem adjacent_local_parameter_exact :
    (∀ {α : Type} [Fintype α] [DecidableEq α]
      (H : G413.Hypergraph α),
      IsClutter H →
      RowsCardAtLeast H 2 →
      RowsCardAtLeast (blocker H) 4 →
      12 ≤ H.card + (blocker H).card) ∧
    ∃ S C : G413.Hypergraph WitnessGround,
      IsClutter S ∧ IsClutter C ∧
      S = blocker C ∧ C = blocker S ∧
      RowsCardAtLeast S 2 ∧ RowsCardAtLeast C 4 ∧
      S.card + C.card = 12 := by
  constructor
  · intro α _ _ H hClutter hRows hBRows
    exact mutual_blocker_total_card_ge_twelve hClutter hRows hBRows
  · exact ⟨witnessTwoRows, witnessFourRows,
      witnessTwoRows_isClutter, witnessFourRows_isClutter,
      witness_blocker_four.symm, witness_blocker_two.symm,
      witnessTwoRows_rows, witnessFourRows_rows, witness_total_card⟩

end AiMathLab.P0054.AdjacentExact
