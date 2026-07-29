import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector076

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector078 : List Nat :=
  [1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector078_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 78 [] =
      sevenNineExtensionVector078 := by
  decide

def sevenNineExtensionVector078BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

def sevenNineExtensionVector078Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector078Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector078Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector078_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector078 =
      sevenNineExtensionVector078BlockerRows := by
  decide

theorem sevenNineExtensionVector078_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector078 =
      sevenNineExtensionVector078Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector078_blocker_rows]
  decide

def sevenNineExtensionVector078Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

theorem sevenNineExtensionVector078_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector078
        sevenNineExtensionVector078Selected0 =
      sevenNineExtensionVector078Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector078_blocker_rows]
  decide

def sevenNineExtensionVector078Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 6]

def sevenNineExtensionVector078BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 3}, {0, 1, 7}, {0, 2, 7}, {1, 3, 5}, {1, 5, 7}, {2, 3, 6}, {2, 5, 7}, {2, 6, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector078_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector078
        sevenNineExtensionVector078Base0 =
      sevenNineExtensionVector078Eligible0 := by
  decide

theorem sevenNineExtensionVector078_base_blocker0 :
    fastBlocker sevenNineExtensionVector078Base0 =
      sevenNineExtensionVector078BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
