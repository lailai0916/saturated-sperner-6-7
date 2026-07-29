import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector099

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector101 : List Nat :=
  [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0]

theorem sevenNineExtensionVector101_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 101 [] =
      sevenNineExtensionVector101 := by
  decide

def sevenNineExtensionVector101BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def sevenNineExtensionVector101Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector101Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector101Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector101_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector101 =
      sevenNineExtensionVector101BlockerRows := by
  decide

theorem sevenNineExtensionVector101_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector101 =
      sevenNineExtensionVector101Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector101_blocker_rows]
  decide

def sevenNineExtensionVector101Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

theorem sevenNineExtensionVector101_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector101
        sevenNineExtensionVector101Selected0 =
      sevenNineExtensionVector101Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector101_blocker_rows]
  decide

def sevenNineExtensionVector101Eligible0 :
    List MiddleFourModelPoint :=
  [0, 2, 3, 4, 5, 6]

def sevenNineExtensionVector101BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 3}, {0, 1, 7}, {1, 2, 7}, {1, 5, 6}, {1, 5, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector101_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector101
        sevenNineExtensionVector101Base0 =
      sevenNineExtensionVector101Eligible0 := by
  decide

theorem sevenNineExtensionVector101_base_blocker0 :
    fastBlocker sevenNineExtensionVector101Base0 =
      sevenNineExtensionVector101BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
