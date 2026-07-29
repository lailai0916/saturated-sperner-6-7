import AiMathLab.P0054MiddleSevenNineFourCertificate
import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

/-!
# Finite extension check for non-`K₄` four-row kernels in the 7+9 split

For a nine-row kernel blocker no extra row is present.  For an eight-row
kernel blocker one arbitrary extra row is enumerated, including all eligible
old points and every possible fresh-point multiplicity.  The unique
seven-row `K₄` blocker needs two extra rows and is handled separately.
-/

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineModelCandidateRowsForSelection (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint)) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  let base := middleFourModelLiftBaseRows values selected
  if base.toFinset.card = 9 then
    [base]
  else if base.toFinset.card = 8 then
    (middleFourModelExtraRowList values base).map fun extra => extra :: base
  else
    []

def sevenNineModelCandidateRows (values : List Nat) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  (middleFourModelLiftSelectionRows values).flatMap fun selected =>
    sevenNineModelCandidateRowsForSelection values selected

def sevenNineModelMaxDegreeAtMostFour
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  (List.finRange 16).all fun point =>
    decide (degree rows.toFinset point ≤ 4)

def sevenNineModelRowsCardBetweenThreeAndSeven
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  rows.all fun row => decide (3 ≤ row.card ∧ row.card ≤ 7)

def sevenNineModelCandidateCheck
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  !sevenNineModelRowsCardBetweenThreeAndSeven rows ||
    if rows.toFinset.card = 9 then
      !sevenNineModelMaxDegreeAtMostFour rows ||
        decide ((fastBlocker rows).card ≠ 7)
    else
      decide ((fastBlocker rows).card ≠ 7)

def sevenNineModelExtraCandidateCheck
    (base : List (G413.Row MiddleFourModelPoint))
    (baseBlocker : G413.Hypergraph MiddleFourModelPoint)
    (extra : G413.Row MiddleFourModelPoint) : Bool :=
  let rows := extra :: base
  !sevenNineModelRowsCardBetweenThreeAndSeven rows ||
    if rows.toFinset.card = 9 then
      !sevenNineModelMaxDegreeAtMostFour rows ||
        decide ((fastBlockerStep baseBlocker extra).card ≠ 7)
    else
      decide ((fastBlockerStep baseBlocker extra).card ≠ 7)

theorem sevenNineModelExtraCandidateCheck_eq
    (base : List (G413.Row MiddleFourModelPoint))
    (extra : G413.Row MiddleFourModelPoint) :
    sevenNineModelExtraCandidateCheck base (fastBlocker base) extra =
      sevenNineModelCandidateCheck (extra :: base) := by
  rfl

def sevenNineModelSelectionCheck (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint)) : Bool :=
  let base := middleFourModelLiftBaseRows values selected
  if base.toFinset.card = 9 then
    sevenNineModelCandidateCheck base
  else if base.toFinset.card = 8 then
    let baseBlocker := fastBlocker base
    (middleFourModelExtraRowList values base).all
      (sevenNineModelExtraCandidateCheck base baseBlocker)
  else
    true

def sevenNineModelRawOldCheck (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint))
    (baseBlocker : G413.Hypergraph MiddleFourModelPoint)
    (old : List MiddleFourModelPoint) : Bool :=
  (List.range 9).all fun fresh =>
    let extra := old.toFinset ∪
      (middleFourModelFreshPointList values fresh).toFinset
    sevenNineModelExtraCandidateCheck base baseBlocker extra

def sevenNineModelRawChunkCheck (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint))
    (baseBlocker : G413.Hypergraph MiddleFourModelPoint)
    (chunk : List (List MiddleFourModelPoint)) : Bool :=
  chunk.all (sevenNineModelRawOldCheck values base baseBlocker)

theorem sevenNineModelRawSelectionCheck_of_chunks
    (values : List Nat) (base : List (G413.Row MiddleFourModelPoint))
    (baseBlocker : G413.Hypergraph MiddleFourModelPoint)
    (oldSubsets : List (List MiddleFourModelPoint))
    (chunks : List (List (List MiddleFourModelPoint)))
    (hFlatten : chunks.flatMap id = oldSubsets)
    (hChunks : chunks.all
      (sevenNineModelRawChunkCheck values base baseBlocker) = true) :
    oldSubsets.all
      (sevenNineModelRawOldCheck values base baseBlocker) = true := by
  subst oldSubsets
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      change (sevenNineModelRawChunkCheck values base baseBlocker chunk &&
        chunks.all
          (sevenNineModelRawChunkCheck values base baseBlocker)) = true at hChunks
      have hBoth := Bool.and_eq_true_iff.mp hChunks
      rw [List.flatMap_cons, List.all_append]
      apply Bool.and_eq_true_iff.mpr
      constructor
      · change chunk.all
          (sevenNineModelRawOldCheck values base baseBlocker) = true
        simpa only [sevenNineModelRawChunkCheck] using hBoth.1
      · exact ih hBoth.2

theorem sevenNineModelSelectionCheck_of_raw
    (values : List Nat) (selected : List (G413.Row MiddleFourModelPoint))
    (base : List (G413.Row MiddleFourModelPoint))
    (baseBlocker : G413.Hypergraph MiddleFourModelPoint)
    (eligible : List MiddleFourModelPoint)
    (hBase : middleFourModelLiftBaseRows values selected = base)
    (hBaseCard : base.toFinset.card = 8)
    (hBaseBlocker : fastBlocker base = baseBlocker)
    (hEligible : middleFourModelEligibleOldPointList values base = eligible)
    (hRaw : (middleFourListPowerset eligible).all
      (sevenNineModelRawOldCheck values base baseBlocker) = true) :
    sevenNineModelSelectionCheck values selected = true := by
  unfold sevenNineModelSelectionCheck
  rw [hBase, if_neg (by omega), if_pos hBaseCard]
  unfold middleFourModelExtraRowList
  rw [hEligible, hBaseBlocker]
  simpa [sevenNineModelRawOldCheck] using hRaw

def sevenNineExtensionValuesCheck (values : List Nat) : Bool :=
  (middleFourModelLiftSelectionRows values).all
    (sevenNineModelSelectionCheck values)

def sevenNineExtensionCertificateCheck : Bool :=
  MiddleSevenNineFinite.middleFourMultiplicityCertificate.all
    sevenNineExtensionValuesCheck

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
