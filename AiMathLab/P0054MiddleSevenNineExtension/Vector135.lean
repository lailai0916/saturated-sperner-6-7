import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector133

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector135 : List Nat :=
  [2, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1]

theorem sevenNineExtensionVector135_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 135 [] =
      sevenNineExtensionVector135 := by
  decide

def sevenNineExtensionVector135BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 4}, {2, 3, 5}, {1, 6}, {1, 4, 5}, {1, 2, 5}, {0, 6}, {0, 4, 5}, {0, 2, 5}]

def sevenNineExtensionVector135Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector135Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector135Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector135_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector135 =
      sevenNineExtensionVector135BlockerRows := by
  decide

theorem sevenNineExtensionVector135_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector135 =
      sevenNineExtensionVector135Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector135_blocker_rows]
  decide

def sevenNineExtensionVector135Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 4, 7}, {2, 3, 5}, {1, 6, 7}, {1, 4, 5}, {1, 2, 5}, {0, 6, 7}, {0, 4, 5}, {0, 2, 5}]

theorem sevenNineExtensionVector135_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector135
        sevenNineExtensionVector135Selected0 =
      sevenNineExtensionVector135Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector135_blocker_rows]
  decide

theorem sevenNineExtensionVector135_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector135
      sevenNineExtensionVector135Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector135_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector135Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector135Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
