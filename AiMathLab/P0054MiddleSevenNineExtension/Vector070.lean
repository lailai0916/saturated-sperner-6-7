import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector068

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector070 : List Nat :=
  [0, 1, 2, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector070_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 70 [] =
      sevenNineExtensionVector070 := by
  decide

def sevenNineExtensionVector070BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {4, 5}, {2, 7}, {2, 3, 6}, {2, 3, 5}, {1, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 7}]

def sevenNineExtensionVector070Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector070Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector070Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector070_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector070 =
      sevenNineExtensionVector070BlockerRows := by
  decide

theorem sevenNineExtensionVector070_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector070 =
      sevenNineExtensionVector070Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector070_blocker_rows]
  decide

def sevenNineExtensionVector070Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {4, 5, 8}, {2, 7, 8}, {2, 3, 6}, {2, 3, 5}, {1, 7, 8}, {1, 3, 6}, {1, 3, 5}, {0, 4, 7}]

theorem sevenNineExtensionVector070_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector070
        sevenNineExtensionVector070Selected0 =
      sevenNineExtensionVector070Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector070_blocker_rows]
  decide

theorem sevenNineExtensionVector070_final_card0 :
    (fastBlocker sevenNineExtensionVector070Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector070_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector070
      sevenNineExtensionVector070Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector070_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector070Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector070Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector070_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
