import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector123

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector125 : List Nat :=
  [1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]

theorem sevenNineExtensionVector125_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 125 [] =
      sevenNineExtensionVector125 := by
  decide

def sevenNineExtensionVector125BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 6}, {3, 5}, {2, 4, 5}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def sevenNineExtensionVector125Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector125Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector125Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector125_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector125 =
      sevenNineExtensionVector125BlockerRows := by
  decide

theorem sevenNineExtensionVector125_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector125 =
      sevenNineExtensionVector125Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector125_blocker_rows]
  decide

def sevenNineExtensionVector125Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {3, 6, 7}, {3, 5, 7}, {2, 4, 5}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

theorem sevenNineExtensionVector125_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector125
        sevenNineExtensionVector125Selected0 =
      sevenNineExtensionVector125Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector125_blocker_rows]
  decide

def sevenNineExtensionVector125Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 5, 6]

def sevenNineExtensionVector125BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 3, 4}, {0, 4, 7}, {1, 2, 7}, {1, 5, 6}, {1, 5, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector125_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector125
        sevenNineExtensionVector125Base0 =
      sevenNineExtensionVector125Eligible0 := by
  decide

theorem sevenNineExtensionVector125_base_blocker0 :
    fastBlocker sevenNineExtensionVector125Base0 =
      sevenNineExtensionVector125BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
