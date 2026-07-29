import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector036

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector038 : List Nat :=
  [1, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector038_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 38 [] =
      sevenNineExtensionVector038 := by
  decide

def sevenNineExtensionVector038BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7}, {3, 6}, {3, 4, 5}, {2, 7}, {2, 6}, {2, 4, 5}, {0, 1, 7}, {0, 1, 6}, {0, 1, 4, 5}]

def sevenNineExtensionVector038Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector038Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector038Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector038_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector038 =
      sevenNineExtensionVector038BlockerRows := by
  decide

theorem sevenNineExtensionVector038_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector038 =
      sevenNineExtensionVector038Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector038_blocker_rows]
  decide

def sevenNineExtensionVector038Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 7, 8}, {3, 6, 8}, {3, 4, 5}, {2, 7, 8}, {2, 6, 8}, {2, 4, 5}, {0, 1, 7}, {0, 1, 6}, {0, 1, 4, 5}]

theorem sevenNineExtensionVector038_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector038
        sevenNineExtensionVector038Selected0 =
      sevenNineExtensionVector038Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector038_blocker_rows]
  decide

theorem sevenNineExtensionVector038_final_card0 :
    (fastBlocker sevenNineExtensionVector038Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector038_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector038
      sevenNineExtensionVector038Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector038_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector038Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector038Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector038_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
