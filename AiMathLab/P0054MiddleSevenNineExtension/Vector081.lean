import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector079

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector081 : List Nat :=
  [0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector081_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 81 [] =
      sevenNineExtensionVector081 := by
  decide

def sevenNineExtensionVector081BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector081Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector081Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector081Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector081_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector081 =
      sevenNineExtensionVector081BlockerRows := by
  decide

theorem sevenNineExtensionVector081_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector081 =
      sevenNineExtensionVector081Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector081_blocker_rows]
  decide

def sevenNineExtensionVector081Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector081_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector081
        sevenNineExtensionVector081Selected0 =
      sevenNineExtensionVector081Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector081_blocker_rows]
  decide

theorem sevenNineExtensionVector081_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector081
      sevenNineExtensionVector081Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector081_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector081Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector081Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
