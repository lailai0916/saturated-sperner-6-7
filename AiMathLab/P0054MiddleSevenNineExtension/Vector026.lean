import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector024

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector026 : List Nat :=
  [0, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector026_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 26 [] =
      sevenNineExtensionVector026 := by
  decide

def sevenNineExtensionVector026BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5}, {2, 4}, {1, 7}, {1, 6}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

def sevenNineExtensionVector026Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector026Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector026Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector026_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector026 =
      sevenNineExtensionVector026BlockerRows := by
  decide

theorem sevenNineExtensionVector026_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector026 =
      sevenNineExtensionVector026Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector026_blocker_rows]
  decide

def sevenNineExtensionVector026Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5, 8}, {2, 4, 8}, {1, 7, 8}, {1, 6, 8}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

theorem sevenNineExtensionVector026_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector026
        sevenNineExtensionVector026Selected0 =
      sevenNineExtensionVector026Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector026_blocker_rows]
  decide

theorem sevenNineExtensionVector026_final_card0 :
    (fastBlocker sevenNineExtensionVector026Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector026_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector026
      sevenNineExtensionVector026Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector026_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector026Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector026Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector026_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
