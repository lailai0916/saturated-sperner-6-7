import AiMathLab.P0054MiddleSevenNineExtensionFinite

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector001 : List Nat :=
  [0, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0]

theorem sevenNineExtensionVector001_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 1 [] =
      sevenNineExtensionVector001 := by
  decide

def sevenNineExtensionVector001BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 5}, {0, 3, 4}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector001Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector001Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector001Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector001_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector001 =
      sevenNineExtensionVector001BlockerRows := by
  decide

theorem sevenNineExtensionVector001_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector001 =
      sevenNineExtensionVector001Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector001_blocker_rows]
  decide

def sevenNineExtensionVector001Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 5, 7}, {0, 3, 4}, {0, 2, 4}, {0, 1, 6}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector001_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector001
        sevenNineExtensionVector001Selected0 =
      sevenNineExtensionVector001Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector001_blocker_rows]
  decide

theorem sevenNineExtensionVector001_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector001
      sevenNineExtensionVector001Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector001_base0, if_pos (by decide)]
  unfold sevenNineModelCandidateCheck
  have hRows : sevenNineModelRowsCardBetweenThreeAndSeven
      sevenNineExtensionVector001Base0 = true := by decide
  have hMax : sevenNineModelMaxDegreeAtMostFour
      sevenNineExtensionVector001Base0 = false := by decide
  simp only [hRows, Bool.not_true, Bool.false_or]
  rw [if_pos (by decide), hMax]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
