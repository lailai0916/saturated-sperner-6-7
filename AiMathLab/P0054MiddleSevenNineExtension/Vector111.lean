import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector109

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector111 : List Nat :=
  [0, 2, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0]

theorem sevenNineExtensionVector111_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 111 [] =
      sevenNineExtensionVector111 := by
  decide

def sevenNineExtensionVector111BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector111Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector111Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector111Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector111_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector111 =
      sevenNineExtensionVector111BlockerRows := by
  decide

theorem sevenNineExtensionVector111_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector111 =
      sevenNineExtensionVector111Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector111_blocker_rows]
  decide

def sevenNineExtensionVector111Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector111_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector111
        sevenNineExtensionVector111Selected0 =
      sevenNineExtensionVector111Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector111_blocker_rows]
  decide

theorem sevenNineExtensionVector111_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector111
      sevenNineExtensionVector111Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector111_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector111Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector111Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
