import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector088

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector090 : List Nat :=
  [1, 1, 1, 2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector090_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 90 [] =
      sevenNineExtensionVector090 := by
  decide

def sevenNineExtensionVector090BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7}, {4, 6}, {3, 6}, {2, 7}, {2, 4, 5}, {2, 3, 5}, {0, 1, 7}, {0, 1, 4, 5}, {0, 1, 3, 5}]

def sevenNineExtensionVector090Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector090Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector090Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector090_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector090 =
      sevenNineExtensionVector090BlockerRows := by
  decide

theorem sevenNineExtensionVector090_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector090 =
      sevenNineExtensionVector090Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector090_blocker_rows]
  decide

def sevenNineExtensionVector090Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{6, 7, 8}, {4, 6, 8}, {3, 6, 8}, {2, 7, 8}, {2, 4, 5}, {2, 3, 5}, {0, 1, 7}, {0, 1, 4, 5}, {0, 1, 3, 5}]

theorem sevenNineExtensionVector090_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector090
        sevenNineExtensionVector090Selected0 =
      sevenNineExtensionVector090Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector090_blocker_rows]
  decide

theorem sevenNineExtensionVector090_final_card0 :
    (fastBlocker sevenNineExtensionVector090Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector090_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector090
      sevenNineExtensionVector090Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector090_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector090Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector090Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector090_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
