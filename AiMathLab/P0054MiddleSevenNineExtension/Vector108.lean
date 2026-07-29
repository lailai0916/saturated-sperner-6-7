import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector106

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector108 : List Nat :=
  [1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]

theorem sevenNineExtensionVector108_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 108 [] =
      sevenNineExtensionVector108 := by
  decide

def sevenNineExtensionVector108BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 6}, {3, 4}, {2, 4, 5}, {1, 6}, {1, 2, 4}, {0, 3, 5}, {0, 2, 5}]

def sevenNineExtensionVector108Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector108Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector108Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector108_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector108 =
      sevenNineExtensionVector108BlockerRows := by
  decide

theorem sevenNineExtensionVector108_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector108 =
      sevenNineExtensionVector108Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector108_blocker_rows]
  decide

def sevenNineExtensionVector108Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 6, 7}, {3, 4, 7}, {2, 4, 5}, {1, 6, 7}, {1, 2, 4}, {0, 3, 5}, {0, 2, 5}]

theorem sevenNineExtensionVector108_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector108
        sevenNineExtensionVector108Selected0 =
      sevenNineExtensionVector108Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector108_blocker_rows]
  decide

def sevenNineExtensionVector108Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 6]

def sevenNineExtensionVector108BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 7}, {0, 4, 6}, {0, 4, 7}, {1, 3, 5}, {1, 5, 7}, {2, 3, 6}, {2, 3, 7}, {2, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector108_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector108
        sevenNineExtensionVector108Base0 =
      sevenNineExtensionVector108Eligible0 := by
  decide

theorem sevenNineExtensionVector108_base_blocker0 :
    fastBlocker sevenNineExtensionVector108Base0 =
      sevenNineExtensionVector108BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
