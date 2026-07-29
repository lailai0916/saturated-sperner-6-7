import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector018

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector020 : List Nat :=
  [0, 0, 0, 1, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0]

theorem sevenNineExtensionVector020_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 20 [] =
      sevenNineExtensionVector020 := by
  decide

def sevenNineExtensionVector020BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def sevenNineExtensionVector020Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector020Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector020Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector020_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector020 =
      sevenNineExtensionVector020BlockerRows := by
  decide

theorem sevenNineExtensionVector020_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector020 =
      sevenNineExtensionVector020Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector020_blocker_rows]
  decide

def sevenNineExtensionVector020Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

theorem sevenNineExtensionVector020_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector020
        sevenNineExtensionVector020Selected0 =
      sevenNineExtensionVector020Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector020_blocker_rows]
  decide

def sevenNineExtensionVector020Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector020BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 2}, {1, 3, 4}, {2, 5, 6}, {3, 4, 7}, {5, 6, 7}, {3, 4, 5, 6}]).toFinset

theorem sevenNineExtensionVector020_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector020
        sevenNineExtensionVector020Base0 =
      sevenNineExtensionVector020Eligible0 := by
  decide

theorem sevenNineExtensionVector020_base_blocker0 :
    fastBlocker sevenNineExtensionVector020Base0 =
      sevenNineExtensionVector020BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
