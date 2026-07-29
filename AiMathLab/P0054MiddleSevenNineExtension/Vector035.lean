import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector033

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector035 : List Nat :=
  [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0]

theorem sevenNineExtensionVector035_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 35 [] =
      sevenNineExtensionVector035 := by
  decide

def sevenNineExtensionVector035BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

def sevenNineExtensionVector035Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector035Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector035Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector035_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector035 =
      sevenNineExtensionVector035BlockerRows := by
  decide

theorem sevenNineExtensionVector035_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector035 =
      sevenNineExtensionVector035Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector035_blocker_rows]
  decide

def sevenNineExtensionVector035Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

theorem sevenNineExtensionVector035_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector035
        sevenNineExtensionVector035Selected0 =
      sevenNineExtensionVector035Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector035_blocker_rows]
  decide

def sevenNineExtensionVector035Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector035BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 6}, {0, 2, 7}, {0, 3, 7}, {0, 4, 7}, {1, 2, 3}, {1, 3, 7}, {3, 5, 6}, {3, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector035_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector035
        sevenNineExtensionVector035Base0 =
      sevenNineExtensionVector035Eligible0 := by
  decide

theorem sevenNineExtensionVector035_base_blocker0 :
    fastBlocker sevenNineExtensionVector035Base0 =
      sevenNineExtensionVector035BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
