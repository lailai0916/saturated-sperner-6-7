import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector087

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector089 : List Nat :=
  [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector089_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 89 [] =
      sevenNineExtensionVector089 := by
  decide

def sevenNineExtensionVector089BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 3}, {0, 4, 5}, {0, 1, 5}, {0, 1, 4}]

def sevenNineExtensionVector089Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector089Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector089Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector089_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector089 =
      sevenNineExtensionVector089BlockerRows := by
  decide

theorem sevenNineExtensionVector089_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector089 =
      sevenNineExtensionVector089Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector089_blocker_rows]
  decide

def sevenNineExtensionVector089Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 3, 6}, {0, 4, 5}, {0, 1, 5}, {0, 1, 4}]

theorem sevenNineExtensionVector089_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector089
        sevenNineExtensionVector089Selected0 =
      sevenNineExtensionVector089Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector089_blocker_rows]
  decide

def sevenNineExtensionVector089Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3]

def sevenNineExtensionVector089BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 3}, {0, 3, 6}, {0, 4, 6}, {0, 5, 6}, {1, 2, 4}, {1, 2, 5}, {1, 4, 6}, {1, 5, 6}, {3, 4, 5}, {4, 5, 6}]).toFinset

theorem sevenNineExtensionVector089_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector089
        sevenNineExtensionVector089Base0 =
      sevenNineExtensionVector089Eligible0 := by
  decide

theorem sevenNineExtensionVector089_base_blocker0 :
    fastBlocker sevenNineExtensionVector089Base0 =
      sevenNineExtensionVector089BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
