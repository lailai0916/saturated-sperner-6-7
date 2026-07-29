import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector058

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector060 : List Nat :=
  [0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0]

theorem sevenNineExtensionVector060_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 60 [] =
      sevenNineExtensionVector060 := by
  decide

def sevenNineExtensionVector060BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

def sevenNineExtensionVector060Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector060Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector060Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector060_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector060 =
      sevenNineExtensionVector060BlockerRows := by
  decide

theorem sevenNineExtensionVector060_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector060 =
      sevenNineExtensionVector060Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector060_blocker_rows]
  decide

def sevenNineExtensionVector060Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

theorem sevenNineExtensionVector060_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector060
        sevenNineExtensionVector060Selected0 =
      sevenNineExtensionVector060Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector060_blocker_rows]
  decide

def sevenNineExtensionVector060Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 6]

def sevenNineExtensionVector060BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 3}, {0, 1, 7}, {0, 2, 7}, {1, 3, 5}, {1, 5, 7}, {2, 3, 6}, {2, 5, 7}, {2, 6, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector060_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector060
        sevenNineExtensionVector060Base0 =
      sevenNineExtensionVector060Eligible0 := by
  decide

theorem sevenNineExtensionVector060_base_blocker0 :
    fastBlocker sevenNineExtensionVector060Base0 =
      sevenNineExtensionVector060BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
