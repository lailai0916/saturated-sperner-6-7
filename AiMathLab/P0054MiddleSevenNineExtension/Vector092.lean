import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector090

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector092 : List Nat :=
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector092_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 92 [] =
      sevenNineExtensionVector092 := by
  decide

def sevenNineExtensionVector092BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

def sevenNineExtensionVector092Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector092Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector092Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector092_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector092 =
      sevenNineExtensionVector092BlockerRows := by
  decide

theorem sevenNineExtensionVector092_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector092 =
      sevenNineExtensionVector092Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector092_blocker_rows]
  decide

def sevenNineExtensionVector092Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

theorem sevenNineExtensionVector092_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector092
        sevenNineExtensionVector092Selected0 =
      sevenNineExtensionVector092Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector092_blocker_rows]
  decide

def sevenNineExtensionVector092Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector092BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 7}, {0, 4, 7}, {1, 3, 5}, {1, 3, 7}, {2, 3, 6}, {2, 3, 7}, {3, 4, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector092_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector092
        sevenNineExtensionVector092Base0 =
      sevenNineExtensionVector092Eligible0 := by
  decide

theorem sevenNineExtensionVector092_base_blocker0 :
    fastBlocker sevenNineExtensionVector092Base0 =
      sevenNineExtensionVector092BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
