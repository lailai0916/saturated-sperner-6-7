import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector122

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector124 : List Nat :=
  [2, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector124_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 124 [] =
      sevenNineExtensionVector124 := by
  decide

def sevenNineExtensionVector124BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector124Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector124Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector124Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector124_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector124 =
      sevenNineExtensionVector124BlockerRows := by
  decide

theorem sevenNineExtensionVector124_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector124 =
      sevenNineExtensionVector124Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector124_blocker_rows]
  decide

def sevenNineExtensionVector124Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector124_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector124
        sevenNineExtensionVector124Selected0 =
      sevenNineExtensionVector124Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector124_blocker_rows]
  decide

theorem sevenNineExtensionVector124_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector124
      sevenNineExtensionVector124Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector124_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector124Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector124Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
