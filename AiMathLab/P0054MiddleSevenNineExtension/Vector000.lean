import AiMathLab.P0054MiddleSevenNineExtensionFinite

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector000 : List Nat :=
  [1, 1, 0, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector000_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 0 [] =
      sevenNineExtensionVector000 := by
  decide

def sevenNineExtensionVector000BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7}, {4, 6}, {3, 7}, {3, 6}, {1, 2, 7}, {1, 2, 6}, {0, 4, 5}, {0, 3, 5}, {0, 1, 2, 5}]

def sevenNineExtensionVector000Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector000Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector000Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector000_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector000 =
      sevenNineExtensionVector000BlockerRows := by
  decide

theorem sevenNineExtensionVector000_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector000 =
      sevenNineExtensionVector000Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector000_blocker_rows]
  decide

def sevenNineExtensionVector000Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 7, 8}, {4, 6, 8}, {3, 7, 8}, {3, 6, 8}, {1, 2, 7}, {1, 2, 6}, {0, 4, 5}, {0, 3, 5}, {0, 1, 2, 5}]

theorem sevenNineExtensionVector000_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector000
        sevenNineExtensionVector000Selected0 =
      sevenNineExtensionVector000Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector000_blocker_rows]
  decide

theorem sevenNineExtensionVector000_final_card0 :
    (fastBlocker sevenNineExtensionVector000Base0).card =
      8 := by
  decide

theorem sevenNineExtensionVector000_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector000
      sevenNineExtensionVector000Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector000_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector000Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector000Base0 = true := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  simp only [Bool.not_true, Bool.false_or]
  rw [sevenNineExtensionVector000_final_card0]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
