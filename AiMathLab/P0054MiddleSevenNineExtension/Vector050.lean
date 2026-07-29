import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector048

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector050 : List Nat :=
  [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector050_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 50 [] =
      sevenNineExtensionVector050 := by
  decide

def sevenNineExtensionVector050BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {3, 5}, {1, 7}, {1, 6}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

def sevenNineExtensionVector050Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector050Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector050Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector050_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector050 =
      sevenNineExtensionVector050BlockerRows := by
  decide

theorem sevenNineExtensionVector050_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector050 =
      sevenNineExtensionVector050Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector050_blocker_rows]
  decide

def sevenNineExtensionVector050Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 8}, {3, 5, 8}, {1, 7, 8}, {1, 6, 8}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

theorem sevenNineExtensionVector050_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector050
        sevenNineExtensionVector050Selected0 =
      sevenNineExtensionVector050Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector050_blocker_rows]
  decide

theorem sevenNineExtensionVector050_final_card0 :
    (fastBlocker sevenNineExtensionVector050Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector050_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector050
      sevenNineExtensionVector050Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector050_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector050Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector050Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector050_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
