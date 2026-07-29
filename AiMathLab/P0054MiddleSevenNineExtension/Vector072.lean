import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector070

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector072 : List Nat :=
  [0, 0, 2, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector072_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 72 [] =
      sevenNineExtensionVector072 := by
  decide

def sevenNineExtensionVector072BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5}, {2, 4}, {2, 3, 6}, {1, 6}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector072Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector072Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector072Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector072_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector072 =
      sevenNineExtensionVector072BlockerRows := by
  decide

theorem sevenNineExtensionVector072_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector072 =
      sevenNineExtensionVector072Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector072_blocker_rows]
  decide

def sevenNineExtensionVector072Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5, 7}, {2, 4, 7}, {2, 3, 6}, {1, 6, 7}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector072_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector072
        sevenNineExtensionVector072Selected0 =
      sevenNineExtensionVector072Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector072_blocker_rows]
  decide

theorem sevenNineExtensionVector072_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector072
      sevenNineExtensionVector072Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector072_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector072Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector072Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
