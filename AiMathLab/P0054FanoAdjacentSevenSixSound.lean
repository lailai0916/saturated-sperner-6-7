import AiMathLab.P0054FanoAdjacentBasics
import AiMathLab.P0054FanoAdjacentSevenSixFinite

/-!
# Soundness of the finite Fano seven-plus-six certificate

The finite checker ranges over one chosen pair on each line of the fixed
Fano model.  This file proves that every seven-row family with one such pair
on every line is represented by a checked selection.  No restriction is
placed on an ambient ground set here; transport to an actual ground is kept
for the following realization layer.
-/

namespace AiMathLab.P0054.FanoAdjacentSevenSixSound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.FanoAdjacentSevenSixFinite

theorem fanoSevenSixSelectionCheck_sound
    {rows : List (G413.Row MiddleFourModelPoint)}
    (hRows : rows ∈ fanoSevenSixSelections)
    (hDualRows : RowsCardAtLeast (blocker rows.toFinset) 4) :
    7 ≤ (blocker rows.toFinset).card := by
  have hChecked := List.all_eq_true.mp fanoSevenSix_check rows hRows
  have hFastRows : RowsCardAtLeast (fastBlocker rows) 4 := by
    rw [fastBlocker_eq_blocker]
    exact hDualRows
  have hRowsBool : modelRowsCardAtLeast (fastBlocker rows) 4 = true :=
    (modelRowsCardAtLeast_eq_true_iff _ _).2 hFastRows
  unfold fanoSevenSixSelectionCheck at hChecked
  dsimp only at hChecked
  have hMainChecked := (Bool.and_eq_true_iff.mp hChecked).1
  rw [hRowsBool] at hMainChecked
  have hCardBool : decide (7 ≤ (fastBlocker rows).card) = true := by
    simpa using hMainChecked
  rw [fastBlocker_eq_blocker] at hCardBool
  exact of_decide_eq_true hCardBool

theorem mem_fanoSevenSixPairOptions_iff
    {pair line : G413.Row MiddleFourModelPoint} :
    pair ∈ fanoSevenSixPairOptions line ↔
      pair.card = 2 ∧ pair ⊆ line := by
  simp [fanoSevenSixPairOptions, mem_fanoModelPairs_iff, and_comm]

theorem exists_checked_selection_of_one_pair_per_fano_line
    {Q : G413.Hypergraph MiddleFourModelPoint}
    (hQCard : Q.card = 7)
    (hEach : ∀ line ∈ sevenEightFanoBase,
      ∃ pair ∈ Q, pair.card = 2 ∧ pair ⊆ line) :
    ∃ rows ∈ fanoSevenSixSelections, rows.toFinset = Q := by
  classical
  let pick : G413.Row MiddleFourModelPoint →
      G413.Row MiddleFourModelPoint := fun line ↦
    if hLine : line ∈ sevenEightFanoBase then
      (hEach line hLine).choose
    else
      ∅
  have hPickMem {line : G413.Row MiddleFourModelPoint}
      (hLine : line ∈ sevenEightFanoBase) : pick line ∈ Q := by
    simp only [pick, dif_pos hLine]
    exact (hEach line hLine).choose_spec.1
  have hPickCard {line : G413.Row MiddleFourModelPoint}
      (hLine : line ∈ sevenEightFanoBase) : (pick line).card = 2 := by
    simp only [pick, dif_pos hLine]
    exact (hEach line hLine).choose_spec.2.1
  have hPickSubset {line : G413.Row MiddleFourModelPoint}
      (hLine : line ∈ sevenEightFanoBase) : pick line ⊆ line := by
    simp only [pick, dif_pos hLine]
    exact (hEach line hLine).choose_spec.2.2
  have hPickInj : Set.InjOn pick
      (↑sevenEightFanoBase : Set (G413.Row MiddleFourModelPoint)) := by
    intro first hFirst second hSecond hEq
    by_contra hLines
    have hSubset : pick first ⊆ first ∩ second := by
      intro point hPoint
      exact Finset.mem_inter.mpr
        ⟨hPickSubset hFirst hPoint,
          hPickSubset hSecond (hEq ▸ hPoint)⟩
    have hUpper := Finset.card_le_card hSubset
    have hIntersection :=
      sevenEight_fano_pairs first hFirst second hSecond hLines
    have hPairCard := hPickCard hFirst
    omega
  let rows := middleFourDegreeFourVector20Base0.map pick
  have hRowsSelection : rows ∈ fanoSevenSixSelections := by
    unfold fanoSevenSixSelections
    rw [List.mem_sections]
    dsimp only [rows]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro line hLineList
    have hLine : line ∈ sevenEightFanoBase := by
      simpa [sevenEightFanoBase] using hLineList
    exact mem_fanoSevenSixPairOptions_iff.mpr
      ⟨hPickCard hLine, hPickSubset hLine⟩
  have hRowsSubset : rows.toFinset ⊆ Q := by
    intro pair hPair
    have hPairList : pair ∈ rows := List.mem_toFinset.mp hPair
    obtain ⟨line, hLineList, rfl⟩ := List.mem_map.mp hPairList
    have hLine : line ∈ sevenEightFanoBase := by
      simpa [sevenEightFanoBase] using hLineList
    exact hPickMem hLine
  have hRowsCard : rows.toFinset.card = 7 := by
    have hImageCard :
        (sevenEightFanoBase.image pick).card = sevenEightFanoBase.card :=
      Finset.card_image_of_injOn hPickInj
    have hBaseCard := sevenEight_fano_base_card
    have hRowsImage : rows.toFinset = sevenEightFanoBase.image pick := by
      ext pair
      simp [rows, sevenEightFanoBase]
    rw [hRowsImage, hImageCard, hBaseCard]
  have hRowsEq : rows.toFinset = Q :=
    Finset.eq_of_subset_of_card_le hRowsSubset (by omega)
  exact ⟨rows, hRowsSelection, hRowsEq⟩

theorem fano_selected_pair_family_blocker_card_ge_seven
    {Q : G413.Hypergraph MiddleFourModelPoint}
    (hQCard : Q.card = 7)
    (hEach : ∀ line ∈ sevenEightFanoBase,
      ∃ pair ∈ Q, pair.card = 2 ∧ pair ⊆ line)
    (hDualRows : RowsCardAtLeast (blocker Q) 4) :
    7 ≤ (blocker Q).card := by
  obtain ⟨rows, hRowsSelection, hRowsEq⟩ :=
    exists_checked_selection_of_one_pair_per_fano_line hQCard hEach
  rw [← hRowsEq]
  exact fanoSevenSixSelectionCheck_sound hRowsSelection (by
    rw [hRowsEq]
    exact hDualRows)

theorem fanoSevenSixFourSelectionCheck_sound
    {rows : List (G413.Row MiddleFourModelPoint)}
    (hRows : rows ∈ fanoSevenSixSelections) :
    4 ≤ (blocker rows.toFinset).card := by
  have hChecked := List.all_eq_true.mp
    fanoSevenSix_check rows hRows
  unfold fanoSevenSixSelectionCheck at hChecked
  dsimp only at hChecked
  have hCardBool : decide (4 ≤ (fastBlocker rows).card) = true :=
    (Bool.and_eq_true_iff.mp hChecked).2
  have hCard : 4 ≤ (fastBlocker rows).card :=
    of_decide_eq_true hCardBool
  rwa [fastBlocker_eq_blocker] at hCard

theorem fano_selected_pair_family_blocker_card_ge_four
    {Q : G413.Hypergraph MiddleFourModelPoint}
    (hQCard : Q.card = 7)
    (hEach : ∀ line ∈ sevenEightFanoBase,
      ∃ pair ∈ Q, pair.card = 2 ∧ pair ⊆ line) :
    4 ≤ (blocker Q).card := by
  obtain ⟨rows, hRowsSelection, hRowsEq⟩ :=
    exists_checked_selection_of_one_pair_per_fano_line hQCard hEach
  rw [← hRowsEq]
  exact fanoSevenSixFourSelectionCheck_sound hRowsSelection

end AiMathLab.P0054.FanoAdjacentSevenSixSound
