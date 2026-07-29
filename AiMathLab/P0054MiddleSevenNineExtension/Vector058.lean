import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector056

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector058 : List Nat :=
  [0, 1, 2, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector058_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 58 [] =
      sevenNineExtensionVector058 := by
  decide

def sevenNineExtensionVector058BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 6}, {2, 7}, {2, 4, 5}, {2, 3, 5}, {1, 7}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

def sevenNineExtensionVector058Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector058Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector058Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector058_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector058 =
      sevenNineExtensionVector058BlockerRows := by
  decide

theorem sevenNineExtensionVector058_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector058 =
      sevenNineExtensionVector058Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector058_blocker_rows]
  decide

def sevenNineExtensionVector058Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {3, 6, 8}, {2, 7, 8}, {2, 4, 5}, {2, 3, 5}, {1, 7, 8}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

theorem sevenNineExtensionVector058_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector058
        sevenNineExtensionVector058Selected0 =
      sevenNineExtensionVector058Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector058_blocker_rows]
  decide

theorem sevenNineExtensionVector058_final_card0 :
    (fastBlocker sevenNineExtensionVector058Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector058_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector058
      sevenNineExtensionVector058Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector058_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector058Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector058Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector058_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
