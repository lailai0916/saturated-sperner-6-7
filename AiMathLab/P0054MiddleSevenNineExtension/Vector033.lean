import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector031

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector033 : List Nat :=
  [1, 1, 0, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0]

theorem sevenNineExtensionVector033_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 33 [] =
      sevenNineExtensionVector033 := by
  decide

def sevenNineExtensionVector033BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {3, 7}, {2, 7}, {1, 4, 5}, {0, 3, 6}, {0, 2, 6}, {0, 1, 3, 5}, {0, 1, 2, 5}]

def sevenNineExtensionVector033Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector033Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector033Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector033_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector033 =
      sevenNineExtensionVector033BlockerRows := by
  decide

theorem sevenNineExtensionVector033_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector033 =
      sevenNineExtensionVector033Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector033_blocker_rows]
  decide

def sevenNineExtensionVector033Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {3, 7, 8}, {2, 7, 8}, {1, 4, 5}, {0, 3, 6}, {0, 2, 6}, {0, 1, 3, 5}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector033_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector033
        sevenNineExtensionVector033Selected0 =
      sevenNineExtensionVector033Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector033_blocker_rows]
  decide

theorem sevenNineExtensionVector033_final_card0 :
    (fastBlocker sevenNineExtensionVector033Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector033_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector033
      sevenNineExtensionVector033Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector033_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector033Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector033Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector033_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
