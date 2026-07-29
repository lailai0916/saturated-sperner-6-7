import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector030

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector032 : List Nat :=
  [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0]

theorem sevenNineExtensionVector032_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 32 [] =
      sevenNineExtensionVector032 := by
  decide

def sevenNineExtensionVector032BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 3, 4}, {1, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

def sevenNineExtensionVector032Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector032Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector032Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector032_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector032 =
      sevenNineExtensionVector032BlockerRows := by
  decide

theorem sevenNineExtensionVector032_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector032 =
      sevenNineExtensionVector032Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector032_blocker_rows]
  decide

def sevenNineExtensionVector032Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

theorem sevenNineExtensionVector032_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector032
        sevenNineExtensionVector032Selected0 =
      sevenNineExtensionVector032Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector032_blocker_rows]
  decide

def sevenNineExtensionVector032Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 3, 4, 5, 6]

def sevenNineExtensionVector032BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 2, 7}, {0, 3, 6}, {0, 3, 7}, {0, 4, 7}, {1, 2, 3}, {1, 2, 7}, {2, 5, 6}, {2, 5, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector032_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector032
        sevenNineExtensionVector032Base0 =
      sevenNineExtensionVector032Eligible0 := by
  decide

theorem sevenNineExtensionVector032_base_blocker0 :
    fastBlocker sevenNineExtensionVector032Base0 =
      sevenNineExtensionVector032BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
