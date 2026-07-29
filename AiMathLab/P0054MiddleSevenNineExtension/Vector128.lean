import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector126

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector128 : List Nat :=
  [2, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]

theorem sevenNineExtensionVector128_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 128 [] =
      sevenNineExtensionVector128 := by
  decide

def sevenNineExtensionVector128BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7}, {3, 6}, {3, 4, 5}, {1, 7}, {1, 2, 6}, {1, 2, 4, 5}, {0, 7}, {0, 2, 6}, {0, 2, 4, 5}]

def sevenNineExtensionVector128Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector128Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector128Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector128_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector128 =
      sevenNineExtensionVector128BlockerRows := by
  decide

theorem sevenNineExtensionVector128_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector128 =
      sevenNineExtensionVector128Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector128_blocker_rows]
  decide

def sevenNineExtensionVector128Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7, 8}, {3, 6, 8}, {3, 4, 5}, {1, 7, 8}, {1, 2, 6}, {1, 2, 4, 5}, {0, 7, 8}, {0, 2, 6}, {0, 2, 4, 5}]

theorem sevenNineExtensionVector128_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector128
        sevenNineExtensionVector128Selected0 =
      sevenNineExtensionVector128Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector128_blocker_rows]
  decide

theorem sevenNineExtensionVector128_final_card0 :
    (fastBlocker sevenNineExtensionVector128Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector128_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector128
      sevenNineExtensionVector128Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector128_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector128Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector128Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector128_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
