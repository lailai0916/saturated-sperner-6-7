import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector014

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector016 : List Nat :=
  [1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector016_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 16 [] =
      sevenNineExtensionVector016 := by
  decide

def sevenNineExtensionVector016BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {3, 5}, {2, 7}, {2, 6}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

def sevenNineExtensionVector016Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector016Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector016Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector016_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector016 =
      sevenNineExtensionVector016BlockerRows := by
  decide

theorem sevenNineExtensionVector016_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector016 =
      sevenNineExtensionVector016Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector016_blocker_rows]
  decide

def sevenNineExtensionVector016Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 8}, {3, 5, 8}, {2, 7, 8}, {2, 6, 8}, {1, 2, 5}, {0, 4, 7}, {0, 4, 6}, {0, 3, 7}, {0, 3, 6}]

theorem sevenNineExtensionVector016_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector016
        sevenNineExtensionVector016Selected0 =
      sevenNineExtensionVector016Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector016_blocker_rows]
  decide

theorem sevenNineExtensionVector016_final_card0 :
    (fastBlocker sevenNineExtensionVector016Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector016_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector016
      sevenNineExtensionVector016Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector016_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector016Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector016Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector016_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
