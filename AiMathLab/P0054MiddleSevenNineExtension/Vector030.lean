import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector028

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector030 : List Nat :=
  [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0]

theorem sevenNineExtensionVector030_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 30 [] =
      sevenNineExtensionVector030 := by
  decide

def sevenNineExtensionVector030BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {3, 7}, {2, 7}, {1, 3, 6}, {1, 2, 6}, {0, 4, 5}, {0, 1, 3, 5}, {0, 1, 2, 5}]

def sevenNineExtensionVector030Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector030Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector030Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector030_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector030 =
      sevenNineExtensionVector030BlockerRows := by
  decide

theorem sevenNineExtensionVector030_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector030 =
      sevenNineExtensionVector030Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector030_blocker_rows]
  decide

def sevenNineExtensionVector030Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {3, 7, 8}, {2, 7, 8}, {1, 3, 6}, {1, 2, 6}, {0, 4, 5}, {0, 1, 3, 5}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector030_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector030
        sevenNineExtensionVector030Selected0 =
      sevenNineExtensionVector030Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector030_blocker_rows]
  decide

theorem sevenNineExtensionVector030_final_card0 :
    (fastBlocker sevenNineExtensionVector030Base0).card =
      11 := by
  decide

theorem sevenNineExtensionVector030_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector030
      sevenNineExtensionVector030Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector030_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector030Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector030Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector030_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
