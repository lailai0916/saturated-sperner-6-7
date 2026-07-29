import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector045

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector047 : List Nat :=
  [0, 1, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0]

theorem sevenNineExtensionVector047_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 47 [] =
      sevenNineExtensionVector047 := by
  decide

def sevenNineExtensionVector047BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def sevenNineExtensionVector047Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector047Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector047Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector047_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector047 =
      sevenNineExtensionVector047BlockerRows := by
  decide

theorem sevenNineExtensionVector047_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector047 =
      sevenNineExtensionVector047Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector047_blocker_rows]
  decide

def sevenNineExtensionVector047Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

theorem sevenNineExtensionVector047_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector047
        sevenNineExtensionVector047Selected0 =
      sevenNineExtensionVector047Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector047_blocker_rows]
  decide

def sevenNineExtensionVector047Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector047BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 2}, {1, 3, 4}, {2, 5, 6}, {3, 4, 7}, {5, 6, 7}, {3, 4, 5, 6}]).toFinset

theorem sevenNineExtensionVector047_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector047
        sevenNineExtensionVector047Base0 =
      sevenNineExtensionVector047Eligible0 := by
  decide

theorem sevenNineExtensionVector047_base_blocker0 :
    fastBlocker sevenNineExtensionVector047Base0 =
      sevenNineExtensionVector047BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
