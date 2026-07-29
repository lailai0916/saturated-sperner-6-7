import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector051

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector053 : List Nat :=
  [0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector053_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 53 [] =
      sevenNineExtensionVector053 := by
  decide

def sevenNineExtensionVector053BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 3, 6}, {1, 3, 5}, {1, 2, 6}, {1, 2, 5}, {0, 6}, {0, 5}, {0, 1, 4}]

def sevenNineExtensionVector053Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector053Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector053Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector053_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector053 =
      sevenNineExtensionVector053BlockerRows := by
  decide

theorem sevenNineExtensionVector053_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector053 =
      sevenNineExtensionVector053Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector053_blocker_rows]
  decide

def sevenNineExtensionVector053Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 3, 6}, {1, 3, 5}, {1, 2, 6}, {1, 2, 5}, {0, 6, 7}, {0, 5, 7}, {0, 1, 4}]

theorem sevenNineExtensionVector053_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector053
        sevenNineExtensionVector053Selected0 =
      sevenNineExtensionVector053Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector053_blocker_rows]
  decide

theorem sevenNineExtensionVector053_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector053
      sevenNineExtensionVector053Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector053_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector053Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector053Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
