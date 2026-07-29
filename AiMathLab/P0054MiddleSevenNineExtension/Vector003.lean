import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector001

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector003 : List Nat :=
  [1, 1, 0, 1, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector003_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 3 [] =
      sevenNineExtensionVector003 := by
  decide

def sevenNineExtensionVector003BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {4, 5}, {3, 7}, {1, 2, 7}, {0, 3, 6}, {0, 3, 5}, {0, 1, 2, 6}, {0, 1, 2, 5}]

def sevenNineExtensionVector003Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector003Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector003Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector003_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector003 =
      sevenNineExtensionVector003BlockerRows := by
  decide

theorem sevenNineExtensionVector003_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector003 =
      sevenNineExtensionVector003Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector003_blocker_rows]
  decide

def sevenNineExtensionVector003Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {4, 5, 8}, {3, 7, 8}, {1, 2, 7}, {0, 3, 6}, {0, 3, 5}, {0, 1, 2, 6}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector003_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector003
        sevenNineExtensionVector003Selected0 =
      sevenNineExtensionVector003Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector003_blocker_rows]
  decide

theorem sevenNineExtensionVector003_final_card0 :
    (fastBlocker sevenNineExtensionVector003Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector003_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector003
      sevenNineExtensionVector003Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector003_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector003Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector003Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector003_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
