import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector120

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector122 : List Nat :=
  [2, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector122_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 122 [] =
      sevenNineExtensionVector122 := by
  decide

def sevenNineExtensionVector122BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {2, 4, 5}, {1, 7}, {1, 3, 6}, {1, 2, 3, 5}, {0, 7}, {0, 3, 6}, {0, 2, 3, 5}]

def sevenNineExtensionVector122Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector122Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector122Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector122_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector122 =
      sevenNineExtensionVector122BlockerRows := by
  decide

theorem sevenNineExtensionVector122_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector122 =
      sevenNineExtensionVector122Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector122_blocker_rows]
  decide

def sevenNineExtensionVector122Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {2, 4, 5}, {1, 7, 8}, {1, 3, 6}, {1, 2, 3, 5}, {0, 7, 8}, {0, 3, 6}, {0, 2, 3, 5}]

theorem sevenNineExtensionVector122_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector122
        sevenNineExtensionVector122Selected0 =
      sevenNineExtensionVector122Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector122_blocker_rows]
  decide

theorem sevenNineExtensionVector122_final_card0 :
    (fastBlocker sevenNineExtensionVector122Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector122_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector122
      sevenNineExtensionVector122Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector122_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector122Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector122Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector122_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
