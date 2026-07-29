import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector049

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector051 : List Nat :=
  [1, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector051_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 51 [] =
      sevenNineExtensionVector051 := by
  decide

def sevenNineExtensionVector051BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {4, 5}, {2, 7}, {2, 3, 6}, {2, 3, 5}, {1, 7}, {1, 3, 6}, {1, 3, 5}, {0, 4, 7}]

def sevenNineExtensionVector051Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector051Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector051Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector051_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector051 =
      sevenNineExtensionVector051BlockerRows := by
  decide

theorem sevenNineExtensionVector051_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector051 =
      sevenNineExtensionVector051Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector051_blocker_rows]
  decide

def sevenNineExtensionVector051Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {4, 5, 8}, {2, 7, 8}, {2, 3, 6}, {2, 3, 5}, {1, 7, 8}, {1, 3, 6}, {1, 3, 5}, {0, 4, 7}]

theorem sevenNineExtensionVector051_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector051
        sevenNineExtensionVector051Selected0 =
      sevenNineExtensionVector051Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector051_blocker_rows]
  decide

theorem sevenNineExtensionVector051_final_card0 :
    (fastBlocker sevenNineExtensionVector051Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector051_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector051
      sevenNineExtensionVector051Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector051_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector051Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector051Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector051_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
