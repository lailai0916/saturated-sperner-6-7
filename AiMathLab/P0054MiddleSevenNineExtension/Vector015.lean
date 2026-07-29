import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector013

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector015 : List Nat :=
  [0, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector015_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 15 [] =
      sevenNineExtensionVector015 := by
  decide

def sevenNineExtensionVector015BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 6}, {1, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector015Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector015Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector015Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector015_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector015 =
      sevenNineExtensionVector015BlockerRows := by
  decide

theorem sevenNineExtensionVector015_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector015 =
      sevenNineExtensionVector015Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector015_blocker_rows]
  decide

def sevenNineExtensionVector015Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector015_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector015
        sevenNineExtensionVector015Selected0 =
      sevenNineExtensionVector015Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector015_blocker_rows]
  decide

def sevenNineExtensionVector015Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector015BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 3, 6}, {1, 2, 3}, {1, 2, 7}, {4, 5, 6}, {4, 5, 7}, {1, 2, 4, 5}]).toFinset

theorem sevenNineExtensionVector015_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector015
        sevenNineExtensionVector015Base0 =
      sevenNineExtensionVector015Eligible0 := by
  decide

theorem sevenNineExtensionVector015_base_blocker0 :
    fastBlocker sevenNineExtensionVector015Base0 =
      sevenNineExtensionVector015BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
