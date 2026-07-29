import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector071

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector073 : List Nat :=
  [0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector073_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 73 [] =
      sevenNineExtensionVector073 := by
  decide

def sevenNineExtensionVector073BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def sevenNineExtensionVector073Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector073Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector073Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector073_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector073 =
      sevenNineExtensionVector073BlockerRows := by
  decide

theorem sevenNineExtensionVector073_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector073 =
      sevenNineExtensionVector073Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector073_blocker_rows]
  decide

def sevenNineExtensionVector073Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

theorem sevenNineExtensionVector073_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector073
        sevenNineExtensionVector073Selected0 =
      sevenNineExtensionVector073Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector073_blocker_rows]
  decide

def sevenNineExtensionVector073Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector073BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{4, 7}, {0, 1, 5}, {0, 1, 7}, {2, 3, 6}, {2, 3, 7}, {4, 5, 6}, {0, 1, 2, 3}]).toFinset

theorem sevenNineExtensionVector073_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector073
        sevenNineExtensionVector073Base0 =
      sevenNineExtensionVector073Eligible0 := by
  decide

theorem sevenNineExtensionVector073_base_blocker0 :
    fastBlocker sevenNineExtensionVector073Base0 =
      sevenNineExtensionVector073BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
