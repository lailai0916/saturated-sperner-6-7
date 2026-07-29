import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector073

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector075 : List Nat :=
  [1, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector075_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 75 [] =
      sevenNineExtensionVector075 := by
  decide

def sevenNineExtensionVector075BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 6}, {2, 7}, {2, 4, 5}, {2, 3, 5}, {1, 7}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

def sevenNineExtensionVector075Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector075Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector075Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector075_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector075 =
      sevenNineExtensionVector075BlockerRows := by
  decide

theorem sevenNineExtensionVector075_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector075 =
      sevenNineExtensionVector075Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector075_blocker_rows]
  decide

def sevenNineExtensionVector075Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 8}, {3, 6, 8}, {2, 7, 8}, {2, 4, 5}, {2, 3, 5}, {1, 7, 8}, {1, 4, 5}, {1, 3, 5}, {0, 6, 7}]

theorem sevenNineExtensionVector075_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector075
        sevenNineExtensionVector075Selected0 =
      sevenNineExtensionVector075Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector075_blocker_rows]
  decide

theorem sevenNineExtensionVector075_final_card0 :
    (fastBlocker sevenNineExtensionVector075Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector075_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector075
      sevenNineExtensionVector075Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector075_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector075Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector075Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector075_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
