import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector116

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector118 : List Nat :=
  [2, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem sevenNineExtensionVector118_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 118 [] =
      sevenNineExtensionVector118 := by
  decide

def sevenNineExtensionVector118BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7}, {4, 6}, {2, 3, 6}, {1, 7}, {1, 4, 5}, {1, 2, 3, 5}, {0, 7}, {0, 4, 5}, {0, 2, 3, 5}]

def sevenNineExtensionVector118Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector118Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector118Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector118_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector118 =
      sevenNineExtensionVector118BlockerRows := by
  decide

theorem sevenNineExtensionVector118_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector118 =
      sevenNineExtensionVector118Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector118_blocker_rows]
  decide

def sevenNineExtensionVector118Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7, 8}, {4, 6, 8}, {2, 3, 6}, {1, 7, 8}, {1, 4, 5}, {1, 2, 3, 5}, {0, 7, 8}, {0, 4, 5}, {0, 2, 3, 5}]

theorem sevenNineExtensionVector118_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector118
        sevenNineExtensionVector118Selected0 =
      sevenNineExtensionVector118Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector118_blocker_rows]
  decide

theorem sevenNineExtensionVector118_final_card0 :
    (fastBlocker sevenNineExtensionVector118Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector118_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector118
      sevenNineExtensionVector118Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector118_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector118Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector118Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector118_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
