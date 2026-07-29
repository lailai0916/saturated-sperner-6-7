import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector078

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector080 : List Nat :=
  [0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 0, 2, 0, 0]

theorem sevenNineExtensionVector080_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 80 [] =
      sevenNineExtensionVector080 := by
  decide

def sevenNineExtensionVector080BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 6}, {2, 4, 5}, {2, 3, 6}, {2, 3, 5}, {1, 4}, {1, 3}, {0, 6}, {0, 5}, {0, 1, 2}]

def sevenNineExtensionVector080Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector080Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector080Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector080_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector080 =
      sevenNineExtensionVector080BlockerRows := by
  decide

theorem sevenNineExtensionVector080_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector080 =
      sevenNineExtensionVector080Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector080_blocker_rows]
  decide

def sevenNineExtensionVector080Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 6}, {2, 4, 5}, {2, 3, 6}, {2, 3, 5}, {1, 4, 7}, {1, 3, 7}, {0, 6, 7}, {0, 5, 7}, {0, 1, 2}]

theorem sevenNineExtensionVector080_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector080
        sevenNineExtensionVector080Selected0 =
      sevenNineExtensionVector080Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector080_blocker_rows]
  decide

theorem sevenNineExtensionVector080_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector080
      sevenNineExtensionVector080Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector080_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector080Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector080Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
