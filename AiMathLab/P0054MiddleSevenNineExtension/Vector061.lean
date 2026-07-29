import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector059

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector061 : List Nat :=
  [1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector061_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 61 [] =
      sevenNineExtensionVector061 := by
  decide

def sevenNineExtensionVector061BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

def sevenNineExtensionVector061Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector061Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector061Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector061_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector061 =
      sevenNineExtensionVector061BlockerRows := by
  decide

theorem sevenNineExtensionVector061_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector061 =
      sevenNineExtensionVector061Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector061_blocker_rows]
  decide

def sevenNineExtensionVector061Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

theorem sevenNineExtensionVector061_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector061
        sevenNineExtensionVector061Selected0 =
      sevenNineExtensionVector061Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector061_blocker_rows]
  decide

def sevenNineExtensionVector061Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

def sevenNineExtensionVector061BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 3, 5}, {0, 5, 7}, {0, 6, 7}, {1, 2, 3}, {1, 2, 7}, {2, 3, 6}, {2, 6, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector061_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector061
        sevenNineExtensionVector061Base0 =
      sevenNineExtensionVector061Eligible0 := by
  decide

theorem sevenNineExtensionVector061_base_blocker0 :
    fastBlocker sevenNineExtensionVector061Base0 =
      sevenNineExtensionVector061BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
