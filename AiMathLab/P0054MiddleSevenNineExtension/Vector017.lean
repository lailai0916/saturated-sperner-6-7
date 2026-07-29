import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector015

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector017 : List Nat :=
  [1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector017_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 17 [] =
      sevenNineExtensionVector017 := by
  decide

def sevenNineExtensionVector017BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {4, 5}, {3, 7}, {2, 7}, {1, 3, 6}, {1, 3, 5}, {1, 2, 6}, {1, 2, 5}, {0, 4, 7}]

def sevenNineExtensionVector017Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector017Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector017Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector017_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector017 =
      sevenNineExtensionVector017BlockerRows := by
  decide

theorem sevenNineExtensionVector017_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector017 =
      sevenNineExtensionVector017Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector017_blocker_rows]
  decide

def sevenNineExtensionVector017Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {4, 5, 8}, {3, 7, 8}, {2, 7, 8}, {1, 3, 6}, {1, 3, 5}, {1, 2, 6}, {1, 2, 5}, {0, 4, 7}]

theorem sevenNineExtensionVector017_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector017
        sevenNineExtensionVector017Selected0 =
      sevenNineExtensionVector017Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector017_blocker_rows]
  decide

theorem sevenNineExtensionVector017_final_card0 :
    (fastBlocker sevenNineExtensionVector017Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector017_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector017
      sevenNineExtensionVector017Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector017_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector017Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector017Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector017_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
