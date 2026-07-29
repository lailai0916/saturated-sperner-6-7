import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector067

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector069 : List Nat :=
  [0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector069_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 69 [] =
      sevenNineExtensionVector069 := by
  decide

def sevenNineExtensionVector069BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {3, 5}, {1, 7}, {1, 6}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

def sevenNineExtensionVector069Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector069Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector069Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector069_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector069 =
      sevenNineExtensionVector069BlockerRows := by
  decide

theorem sevenNineExtensionVector069_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector069 =
      sevenNineExtensionVector069Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector069_blocker_rows]
  decide

def sevenNineExtensionVector069Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 8}, {3, 5, 8}, {1, 7, 8}, {1, 6, 8}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

theorem sevenNineExtensionVector069_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector069
        sevenNineExtensionVector069Selected0 =
      sevenNineExtensionVector069Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector069_blocker_rows]
  decide

theorem sevenNineExtensionVector069_final_card0 :
    (fastBlocker sevenNineExtensionVector069Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector069_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector069
      sevenNineExtensionVector069Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector069_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector069Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector069Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector069_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
