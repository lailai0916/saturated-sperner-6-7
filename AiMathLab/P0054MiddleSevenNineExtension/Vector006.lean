import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector004

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector006 : List Nat :=
  [1, 1, 0, 1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector006_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 6 [] =
      sevenNineExtensionVector006 := by
  decide

def sevenNineExtensionVector006BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {3, 7}, {3, 6}, {1, 4, 5}, {1, 3, 5}, {0, 2, 7}, {0, 2, 6}, {0, 1, 2, 5}]

def sevenNineExtensionVector006Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector006Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector006Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector006_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector006 =
      sevenNineExtensionVector006BlockerRows := by
  decide

theorem sevenNineExtensionVector006_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector006 =
      sevenNineExtensionVector006Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector006_blocker_rows]
  decide

def sevenNineExtensionVector006Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {3, 7, 8}, {3, 6, 8}, {1, 4, 5}, {1, 3, 5}, {0, 2, 7}, {0, 2, 6}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector006_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector006
        sevenNineExtensionVector006Selected0 =
      sevenNineExtensionVector006Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector006_blocker_rows]
  decide

theorem sevenNineExtensionVector006_final_card0 :
    (fastBlocker sevenNineExtensionVector006Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector006_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector006
      sevenNineExtensionVector006Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector006_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector006Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector006Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector006_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
