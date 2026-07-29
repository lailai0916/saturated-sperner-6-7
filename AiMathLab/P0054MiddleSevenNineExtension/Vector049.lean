import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector047

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector049 : List Nat :=
  [0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector049_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 49 [] =
      sevenNineExtensionVector049 := by
  decide

def sevenNineExtensionVector049BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector049Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector049Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector049Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector049_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector049 =
      sevenNineExtensionVector049BlockerRows := by
  decide

theorem sevenNineExtensionVector049_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector049 =
      sevenNineExtensionVector049Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector049_blocker_rows]
  decide

def sevenNineExtensionVector049Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector049_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector049
        sevenNineExtensionVector049Selected0 =
      sevenNineExtensionVector049Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector049_blocker_rows]
  decide

def sevenNineExtensionVector049Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 3, 4, 5, 6]

def sevenNineExtensionVector049BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{2, 7}, {0, 1, 3}, {0, 1, 7}, {2, 3, 6}, {4, 5, 6}, {4, 5, 7}, {0, 1, 4, 5}]).toFinset

theorem sevenNineExtensionVector049_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector049
        sevenNineExtensionVector049Base0 =
      sevenNineExtensionVector049Eligible0 := by
  decide

theorem sevenNineExtensionVector049_base_blocker0 :
    fastBlocker sevenNineExtensionVector049Base0 =
      sevenNineExtensionVector049BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
