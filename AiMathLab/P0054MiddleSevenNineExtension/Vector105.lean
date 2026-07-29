import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector103

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector105 : List Nat :=
  [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector105_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 105 [] =
      sevenNineExtensionVector105 := by
  decide

def sevenNineExtensionVector105BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 2, 4}, {0, 3, 5}, {0, 3, 4}]

def sevenNineExtensionVector105Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector105Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector105Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector105_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector105 =
      sevenNineExtensionVector105BlockerRows := by
  decide

theorem sevenNineExtensionVector105_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector105 =
      sevenNineExtensionVector105Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector105_blocker_rows]
  decide

def sevenNineExtensionVector105Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 2, 4}, {0, 3, 5}, {0, 3, 4}]

theorem sevenNineExtensionVector105_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector105
        sevenNineExtensionVector105Selected0 =
      sevenNineExtensionVector105Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector105_blocker_rows]
  decide

def sevenNineExtensionVector105Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector105BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 6}, {0, 2, 7}, {0, 4, 7}, {1, 3, 5}, {1, 3, 7}, {2, 3, 6}, {2, 3, 7}, {3, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector105_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector105
        sevenNineExtensionVector105Base0 =
      sevenNineExtensionVector105Eligible0 := by
  decide

theorem sevenNineExtensionVector105_base_blocker0 :
    fastBlocker sevenNineExtensionVector105Base0 =
      sevenNineExtensionVector105BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
