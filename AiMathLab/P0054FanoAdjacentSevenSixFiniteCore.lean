import AiMathLab.P0054MiddleSevenEightFinite
import Mathlib.Data.List.Sections

/-!
# Core definitions for the finite Fano adjacent-layer certificates

The `3 ^ 7` labelled choices are split into 27 consecutive chunks of 81.
The chunk interface is shared by the seven-plus-six and eight-plus-five
certificates so that each kernel computation can be checked in its own Lean
module.
-/

namespace AiMathLab.P0054.FanoAdjacentSevenSixFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420

/-- All unordered pairs of the sixteen-point model, in a computable order. -/
def fanoModelPairs : List (G413.Row MiddleFourModelPoint) :=
  (List.finRange 16).flatMap fun first ↦
    ((List.finRange 16).filter fun second ↦ first.val < second.val).map
      fun second ↦ {first, second}

theorem mem_fanoModelPairs_iff
    {pair : G413.Row MiddleFourModelPoint} :
    pair ∈ fanoModelPairs ↔ pair.card = 2 := by
  constructor
  · intro hPair
    rcases List.mem_flatMap.mp hPair with ⟨first, _hFirst, hPair⟩
    rcases List.mem_map.mp hPair with ⟨second, hSecond, hEq⟩
    have hValue : first.val < second.val :=
      of_decide_eq_true (List.mem_filter.mp hSecond).2
    have hNe : first ≠ second := by
      intro hEqual
      rw [hEqual] at hValue
      omega
    rw [← hEq]
    exact Finset.card_pair hNe
  · intro hCard
    obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hCard
    have hValueNe : first.val ≠ second.val := by
      intro hEqual
      exact hNe (Fin.ext hEqual)
    rcases lt_or_gt_of_ne hValueNe with hValue | hValue
    · apply List.mem_flatMap.mpr
      refine ⟨first, by simp, ?_⟩
      apply List.mem_map.mpr
      refine ⟨second, List.mem_filter.mpr ⟨by simp, decide_eq_true hValue⟩, ?_⟩
      exact hPair.symm
    · apply List.mem_flatMap.mpr
      refine ⟨second, by simp, ?_⟩
      apply List.mem_map.mpr
      refine ⟨first, List.mem_filter.mpr ⟨by simp, decide_eq_true hValue⟩, ?_⟩
      calc
        ({second, first} : G413.Row MiddleFourModelPoint) = {first, second} := by
          ext point
          simp [or_comm]
        _ = pair := hPair.symm

def fanoSevenSixPairOptions
    (line : G413.Row MiddleFourModelPoint) :
    List (G413.Row MiddleFourModelPoint) :=
  fanoModelPairs.filter fun pair ↦ pair ⊆ line

def fanoSevenSixSelections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  (middleFourDegreeFourVector20Base0.map fanoSevenSixPairOptions).sections

def modelRowsCardAtLeast
    (rows : G413.Hypergraph MiddleFourModelPoint) (minimum : Nat) : Bool :=
  decide ((rows.filter fun row ↦ minimum ≤ row.card).card = rows.card)

theorem modelRowsCardAtLeast_eq_true_iff
    (rows : G413.Hypergraph MiddleFourModelPoint) (minimum : Nat) :
    modelRowsCardAtLeast rows minimum = true ↔
      RowsCardAtLeast rows minimum := by
  change decide ((rows.filter fun row ↦ minimum ≤ row.card).card =
      rows.card) = true ↔ ∀ row ∈ rows, minimum ≤ row.card
  rw [decide_eq_true_eq]
  exact Finset.card_filter_eq_iff

def fanoSevenSixSelectionCheck
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  let dual := fastBlocker rows
  (!modelRowsCardAtLeast dual 4 || decide (7 ≤ dual.card)) &&
    decide (4 ≤ dual.card)

def fanoSevenSixCheck : Bool :=
  fanoSevenSixSelections.all fanoSevenSixSelectionCheck

def fanoSelectionChunkWidth : Nat := 81

def fanoSelectionChunkCount : Nat := 27

def fanoSevenSixSelectionChunk (chunkIndex : Nat) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  (fanoSevenSixSelections.drop
    (chunkIndex * fanoSelectionChunkWidth)).take fanoSelectionChunkWidth

def fanoSevenSixChunkCheck (chunkIndex : Nat) : Bool :=
  (fanoSevenSixSelectionChunk chunkIndex).all
    fanoSevenSixSelectionCheck

theorem all_drop_eq_true_of_chunk {α : Type*}
    {xs : List α} {p : α → Bool} {start width : Nat}
    (hChunk : ((xs.drop start).take width).all p = true)
    (hTail : (xs.drop (start + width)).all p = true) :
    (xs.drop start).all p = true := by
  have hTail' : ((xs.drop start).drop width).all p = true := by
    simpa only [List.drop_drop] using hTail
  have hBoth :
      (((xs.drop start).take width).all p &&
        ((xs.drop start).drop width).all p) = true :=
    Bool.and_eq_true_iff.mpr ⟨hChunk, hTail'⟩
  simpa only [← List.all_append, List.take_append_drop] using hBoth

theorem fanoSevenSixAllDropOfChunk (chunkIndex : Nat)
    (hChunk : fanoSevenSixChunkCheck chunkIndex = true)
    (hTail : (fanoSevenSixSelections.drop
      (chunkIndex * fanoSelectionChunkWidth +
        fanoSelectionChunkWidth)).all
          fanoSevenSixSelectionCheck = true) :
    (fanoSevenSixSelections.drop
      (chunkIndex * fanoSelectionChunkWidth)).all
        fanoSevenSixSelectionCheck = true := by
  apply all_drop_eq_true_of_chunk
  · simpa [fanoSevenSixChunkCheck, fanoSevenSixSelectionChunk] using hChunk
  · exact hTail

end AiMathLab.P0054.FanoAdjacentSevenSixFinite
