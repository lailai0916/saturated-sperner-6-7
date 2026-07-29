import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector072

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector074 : List Nat :=
  [1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0]

theorem sevenNineExtensionVector074_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 74 [] =
      sevenNineExtensionVector074 := by
  decide

def sevenNineExtensionVector074BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5}, {2, 4}, {1, 7}, {1, 6}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

def sevenNineExtensionVector074Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector074Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector074Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector074_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector074 =
      sevenNineExtensionVector074BlockerRows := by
  decide

theorem sevenNineExtensionVector074_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector074 =
      sevenNineExtensionVector074Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector074_blocker_rows]
  decide

def sevenNineExtensionVector074Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 5, 8}, {2, 4, 8}, {1, 7, 8}, {1, 6, 8}, {1, 2, 3}, {0, 5, 7}, {0, 5, 6}, {0, 4, 7}, {0, 4, 6}]

theorem sevenNineExtensionVector074_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector074
        sevenNineExtensionVector074Selected0 =
      sevenNineExtensionVector074Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector074_blocker_rows]
  decide

theorem sevenNineExtensionVector074_final_card0 :
    (fastBlocker sevenNineExtensionVector074Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector074_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector074
      sevenNineExtensionVector074Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector074_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector074Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector074Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector074_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
