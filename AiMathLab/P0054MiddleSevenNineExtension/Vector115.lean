import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector113

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector115 : List Nat :=
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0]

theorem sevenNineExtensionVector115_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 115 [] =
      sevenNineExtensionVector115 := by
  decide

def sevenNineExtensionVector115BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 4, 5}, {0, 3, 4}, {0, 1, 5}]

def sevenNineExtensionVector115Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector115Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector115Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector115_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector115 =
      sevenNineExtensionVector115BlockerRows := by
  decide

theorem sevenNineExtensionVector115_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector115 =
      sevenNineExtensionVector115Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector115_blocker_rows]
  decide

def sevenNineExtensionVector115Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 4, 5}, {0, 3, 4}, {0, 1, 5}]

theorem sevenNineExtensionVector115_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector115
        sevenNineExtensionVector115Selected0 =
      sevenNineExtensionVector115Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector115_blocker_rows]
  decide

def sevenNineExtensionVector115Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector115BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 6}, {0, 2, 7}, {0, 3, 7}, {0, 4, 7}, {1, 2, 4}, {1, 4, 7}, {3, 5, 6}, {3, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector115_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector115
        sevenNineExtensionVector115Base0 =
      sevenNineExtensionVector115Eligible0 := by
  decide

theorem sevenNineExtensionVector115_base_blocker0 :
    fastBlocker sevenNineExtensionVector115Base0 =
      sevenNineExtensionVector115BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
