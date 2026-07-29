import AiMathLab.P0054FanoAdjacentSevenSixFiniteCore

/-!
# Core definitions for the finite Fano eight-plus-five certificate

Each selected Fano pair family is extended by every subset of the seven-point
core together with at most one canonical fresh point.  The expensive check is
split over the shared 27 selection chunks.
-/

namespace AiMathLab.P0054.FanoAdjacentEightFiveFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.FanoAdjacentSevenSixFinite

def fanoEightFiveFresh : MiddleFourModelPoint :=
  ⟨7, by decide⟩

def fanoEightFiveExtendedActive : G413.Row MiddleFourModelPoint :=
  insert fanoEightFiveFresh sevenEightFanoActive

def fanoEightFiveCoreExtras :
    List (G413.Row MiddleFourModelPoint) :=
  (List.finRange 256).map fun mask ↦
    fanoEightFiveExtendedActive.filter fun point ↦ mask.val.testBit point.val

def modelIsClutter
    (rows : G413.Hypergraph MiddleFourModelPoint) : Bool :=
  decide ((rows.filter fun first ↦
    (rows.filter fun second ↦ first ⊆ second → first = second).card =
      rows.card).card = rows.card)

theorem modelIsClutter_eq_true_iff
    (rows : G413.Hypergraph MiddleFourModelPoint) :
    modelIsClutter rows = true ↔ IsClutter rows := by
  change decide ((rows.filter fun first ↦
    (rows.filter fun second ↦ first ⊆ second → first = second).card =
      rows.card).card = rows.card) = true ↔
    ∀ ⦃first⦄, first ∈ rows → ∀ ⦃second⦄, second ∈ rows →
      first ⊆ second → first = second
  rw [decide_eq_true_eq]
  constructor
  · intro hRows first hFirst second hSecond hSubset
    have hFirstGood := Finset.card_filter_eq_iff.mp hRows first hFirst
    have hSecondGood :=
      Finset.card_filter_eq_iff.mp hFirstGood second hSecond
    exact hSecondGood hSubset
  · intro hRows
    rw [Finset.card_filter_eq_iff]
    intro first hFirst
    rw [Finset.card_filter_eq_iff]
    intro second hSecond hSubset
    exact hRows hFirst hSecond hSubset

/-- The same minimization as `fastMinimize`, but its decision procedure only
visits the candidates that actually occur in `rows`. -/
def finiteFastMinimize {alpha : Type*} [DecidableEq alpha]
    (rows : G413.Hypergraph alpha) : G413.Hypergraph alpha :=
  rows.filter fun row ↦
    (rows.filter fun other ↦ other ⊆ row → row ⊆ other).card =
      rows.card

theorem finiteFastMinimize_eq_fastMinimize
    {alpha : Type*} [DecidableEq alpha]
    (rows : G413.Hypergraph alpha) :
    finiteFastMinimize rows = fastMinimize rows := by
  ext row
  simp only [finiteFastMinimize, Finset.mem_filter, mem_fastMinimize]
  constructor
  · rintro ⟨hRow, hCard⟩
    exact ⟨hRow, Finset.card_filter_eq_iff.mp hCard⟩
  · rintro ⟨hRow, hAll⟩
    exact ⟨hRow, Finset.card_filter_eq_iff.mpr hAll⟩

def finiteFastBlockerStep {alpha : Type*} [DecidableEq alpha]
    (candidates : G413.Hypergraph alpha) (row : G413.Row alpha) :
    G413.Hypergraph alpha :=
  finiteFastMinimize (fastBlockerExpand candidates row)

theorem finiteFastBlockerStep_eq_fastBlockerStep
    {alpha : Type*} [DecidableEq alpha]
    (candidates : G413.Hypergraph alpha) (row : G413.Row alpha) :
    finiteFastBlockerStep candidates row =
      fastBlockerStep candidates row := by
  unfold finiteFastBlockerStep fastBlockerStep
  exact finiteFastMinimize_eq_fastMinimize _

def finiteFastBlocker {alpha : Type*} [DecidableEq alpha] :
    List (G413.Row alpha) → G413.Hypergraph alpha
  | [] => {∅}
  | row :: rows => finiteFastBlockerStep (finiteFastBlocker rows) row

theorem finiteFastBlocker_eq_fastBlocker
    {alpha : Type*} [DecidableEq alpha] :
    ∀ rows : List (G413.Row alpha),
      finiteFastBlocker rows = fastBlocker rows := by
  intro rows
  induction rows with
  | nil => rfl
  | cons row rows hRows =>
      simp only [finiteFastBlocker, fastBlocker]
      rw [hRows, finiteFastBlockerStep_eq_fastBlockerStep]

def fanoEightFiveCoreExtraValid
    (rows : List (G413.Row MiddleFourModelPoint))
    (extra : G413.Row MiddleFourModelPoint) : Bool :=
  decide (2 ≤ extra.card) &&
    (decide (extra.card ≤ 5) &&
      rows.all fun row ↦ !decide (row ⊂ extra))

theorem fanoEightFiveCoreExtraValid_eq_true_of_clutter
    (rows : List (G413.Row MiddleFourModelPoint))
    (extra : G413.Row MiddleFourModelPoint)
    (hExtraCardLower : 2 ≤ extra.card)
    (hExtraCardUpper : extra.card ≤ 5)
    (hClutter : IsClutter (insert extra rows.toFinset)) :
    fanoEightFiveCoreExtraValid rows extra = true := by
  unfold fanoEightFiveCoreExtraValid
  rw [Bool.and_eq_true_iff]
  refine ⟨decide_eq_true hExtraCardLower, ?_⟩
  rw [Bool.and_eq_true_iff]
  refine ⟨decide_eq_true hExtraCardUpper, ?_⟩
  rw [List.all_eq_true]
  intro row hRow
  rw [Bool.not_eq_true_eq_eq_false]
  apply decide_eq_false_iff_not.mpr
  intro hProper
  have hRowFamily : row ∈ insert extra rows.toFinset := by
    simp [hRow]
  have hExtraFamily : extra ∈ insert extra rows.toFinset := by
    simp
  have hEqual : row = extra :=
    hClutter hRowFamily hExtraFamily hProper.1
  exact hProper.2 (by simpa [hEqual])

def fanoEightFiveCoreSelectionCheck
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  let baseDual := finiteFastBlocker rows
  fanoEightFiveCoreExtras.all fun extra ↦
    !fanoEightFiveCoreExtraValid rows extra ||
      let dual := finiteFastBlockerStep baseDual extra
      !modelRowsCardAtLeast dual 4 || decide (6 ≤ dual.card)

def fanoEightFiveCoreCheck : Bool :=
  fanoSevenSixSelections.all fanoEightFiveCoreSelectionCheck

def fanoEightFiveCoreChunkCheck (chunkIndex : Nat) : Bool :=
  (fanoSevenSixSelectionChunk chunkIndex).all
    fanoEightFiveCoreSelectionCheck

def fanoEightFiveSubchunkWidth : Nat := 9

def fanoEightFiveCoreSubchunkCheck
    (chunkIndex subchunkIndex : Nat) : Bool :=
  (((fanoSevenSixSelectionChunk chunkIndex).drop
      (subchunkIndex * fanoEightFiveSubchunkWidth)).take
        fanoEightFiveSubchunkWidth).all
    fanoEightFiveCoreSelectionCheck

theorem fanoEightFiveCoreChunkCheck_of_subchunks (chunkIndex : Nat)
    (h0 : fanoEightFiveCoreSubchunkCheck chunkIndex 0 = true)
    (h1 : fanoEightFiveCoreSubchunkCheck chunkIndex 1 = true)
    (h2 : fanoEightFiveCoreSubchunkCheck chunkIndex 2 = true)
    (h3 : fanoEightFiveCoreSubchunkCheck chunkIndex 3 = true)
    (h4 : fanoEightFiveCoreSubchunkCheck chunkIndex 4 = true)
    (h5 : fanoEightFiveCoreSubchunkCheck chunkIndex 5 = true)
    (h6 : fanoEightFiveCoreSubchunkCheck chunkIndex 6 = true)
    (h7 : fanoEightFiveCoreSubchunkCheck chunkIndex 7 = true)
    (h8 : fanoEightFiveCoreSubchunkCheck chunkIndex 8 = true) :
    fanoEightFiveCoreChunkCheck chunkIndex = true := by
  let xs := fanoSevenSixSelectionChunk chunkIndex
  have hLength : xs.length ≤ 81 := by
    simp [xs, fanoSevenSixSelectionChunk, fanoSelectionChunkWidth]
  have hEnd : (xs.drop 81).all
      fanoEightFiveCoreSelectionCheck = true := by
    rw [List.drop_eq_nil_of_le hLength]
    rfl
  have hDrop72 : (xs.drop 72).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h8
    · simpa using hEnd
  have hDrop63 : (xs.drop 63).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h7
    · simpa using hDrop72
  have hDrop54 : (xs.drop 54).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h6
    · simpa using hDrop63
  have hDrop45 : (xs.drop 45).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h5
    · simpa using hDrop54
  have hDrop36 : (xs.drop 36).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h4
    · simpa using hDrop45
  have hDrop27 : (xs.drop 27).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h3
    · simpa using hDrop36
  have hDrop18 : (xs.drop 18).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h2
    · simpa using hDrop27
  have hDrop9 : (xs.drop 9).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h1
    · simpa using hDrop18
  have hDrop0 : (xs.drop 0).all
      fanoEightFiveCoreSelectionCheck = true := by
    apply all_drop_eq_true_of_chunk
    · simpa [fanoEightFiveCoreSubchunkCheck,
        fanoEightFiveSubchunkWidth, xs] using h0
    · simpa using hDrop9
  simpa [fanoEightFiveCoreChunkCheck, xs] using hDrop0

theorem fanoEightFiveAllDropOfChunk (chunkIndex : Nat)
    (hChunk : fanoEightFiveCoreChunkCheck chunkIndex = true)
    (hTail : (fanoSevenSixSelections.drop
      (chunkIndex * fanoSelectionChunkWidth +
        fanoSelectionChunkWidth)).all
          fanoEightFiveCoreSelectionCheck = true) :
    (fanoSevenSixSelections.drop
      (chunkIndex * fanoSelectionChunkWidth)).all
        fanoEightFiveCoreSelectionCheck = true := by
  apply all_drop_eq_true_of_chunk
  · simpa [fanoEightFiveCoreChunkCheck, fanoSevenSixSelectionChunk] using hChunk
  · exact hTail

end AiMathLab.P0054.FanoAdjacentEightFiveFinite
