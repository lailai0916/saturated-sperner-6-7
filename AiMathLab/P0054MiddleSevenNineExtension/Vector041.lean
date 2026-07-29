import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector039

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector041 : List Nat :=
  [1, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector041_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 41 [] =
      sevenNineExtensionVector041 := by
  decide

def sevenNineExtensionVector041BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {4, 5}, {2, 7}, {2, 3, 6}, {2, 3, 5}, {0, 1, 7}, {0, 1, 3, 6}, {0, 1, 3, 5}]

def sevenNineExtensionVector041Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector041Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector041Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector041_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector041 =
      sevenNineExtensionVector041BlockerRows := by
  decide

theorem sevenNineExtensionVector041_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector041 =
      sevenNineExtensionVector041Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector041_blocker_rows]
  decide

def sevenNineExtensionVector041Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {4, 5, 8}, {2, 7, 8}, {2, 3, 6}, {2, 3, 5}, {0, 1, 7}, {0, 1, 3, 6}, {0, 1, 3, 5}]

theorem sevenNineExtensionVector041_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector041
        sevenNineExtensionVector041Selected0 =
      sevenNineExtensionVector041Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector041_blocker_rows]
  decide

theorem sevenNineExtensionVector041_final_card0 :
    (fastBlocker sevenNineExtensionVector041Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector041_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector041
      sevenNineExtensionVector041Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector041_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector041Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector041Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector041_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
