import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector093

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector095 : List Nat :=
  [1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector095_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 95 [] =
      sevenNineExtensionVector095 := by
  decide

def sevenNineExtensionVector095BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 4, 6}, {1, 2, 4}, {0, 3, 6}, {0, 1, 6}]

def sevenNineExtensionVector095Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector095Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector095Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector095_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector095 =
      sevenNineExtensionVector095BlockerRows := by
  decide

theorem sevenNineExtensionVector095_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector095 =
      sevenNineExtensionVector095Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector095_blocker_rows]
  decide

def sevenNineExtensionVector095Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 4, 6}, {1, 2, 4}, {0, 3, 6}, {0, 1, 6}]

theorem sevenNineExtensionVector095_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector095
        sevenNineExtensionVector095Selected0 =
      sevenNineExtensionVector095Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector095_blocker_rows]
  decide

def sevenNineExtensionVector095Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

def sevenNineExtensionVector095BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 4, 5}, {0, 4, 7}, {1, 3, 5}, {1, 3, 7}, {1, 6, 7}, {2, 3, 6}, {2, 6, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector095_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector095
        sevenNineExtensionVector095Base0 =
      sevenNineExtensionVector095Eligible0 := by
  decide

theorem sevenNineExtensionVector095_base_blocker0 :
    fastBlocker sevenNineExtensionVector095Base0 =
      sevenNineExtensionVector095BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
