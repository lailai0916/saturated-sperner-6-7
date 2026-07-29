import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector065

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector067 : List Nat :=
  [0, 0, 2, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0]

theorem sevenNineExtensionVector067_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 67 [] =
      sevenNineExtensionVector067 := by
  decide

def sevenNineExtensionVector067BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}, {0, 2, 4}]

def sevenNineExtensionVector067Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector067Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector067Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector067_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector067 =
      sevenNineExtensionVector067BlockerRows := by
  decide

theorem sevenNineExtensionVector067_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector067 =
      sevenNineExtensionVector067Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector067_blocker_rows]
  decide

def sevenNineExtensionVector067Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}, {0, 2, 4}]

theorem sevenNineExtensionVector067_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector067
        sevenNineExtensionVector067Selected0 =
      sevenNineExtensionVector067Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector067_blocker_rows]
  decide

def sevenNineExtensionVector067Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 3, 4, 5, 6]

def sevenNineExtensionVector067BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{2, 7}, {0, 1, 3}, {0, 1, 7}, {2, 3, 6}, {4, 5, 6}, {4, 5, 7}, {0, 1, 4, 5}]).toFinset

theorem sevenNineExtensionVector067_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector067
        sevenNineExtensionVector067Base0 =
      sevenNineExtensionVector067Eligible0 := by
  decide

theorem sevenNineExtensionVector067_base_blocker0 :
    fastBlocker sevenNineExtensionVector067Base0 =
      sevenNineExtensionVector067BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
