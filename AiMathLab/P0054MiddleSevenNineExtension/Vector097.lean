import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector095

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector097 : List Nat :=
  [1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0]

theorem sevenNineExtensionVector097_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 97 [] =
      sevenNineExtensionVector097 := by
  decide

def sevenNineExtensionVector097BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 4, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector097Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector097Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector097Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector097_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector097 =
      sevenNineExtensionVector097BlockerRows := by
  decide

theorem sevenNineExtensionVector097_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector097 =
      sevenNineExtensionVector097Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector097_blocker_rows]
  decide

def sevenNineExtensionVector097Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 4, 6}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector097_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector097
        sevenNineExtensionVector097Selected0 =
      sevenNineExtensionVector097Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector097_blocker_rows]
  decide

theorem sevenNineExtensionVector097_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector097
      sevenNineExtensionVector097Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector097_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector097Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector097Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
