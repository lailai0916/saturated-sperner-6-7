import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector063

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector065 : List Nat :=
  [0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0]

theorem sevenNineExtensionVector065_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 65 [] =
      sevenNineExtensionVector065 := by
  decide

def sevenNineExtensionVector065BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def sevenNineExtensionVector065Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector065Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector065Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector065_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector065 =
      sevenNineExtensionVector065BlockerRows := by
  decide

theorem sevenNineExtensionVector065_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector065 =
      sevenNineExtensionVector065Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector065_blocker_rows]
  decide

def sevenNineExtensionVector065Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

theorem sevenNineExtensionVector065_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector065
        sevenNineExtensionVector065Selected0 =
      sevenNineExtensionVector065Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector065_blocker_rows]
  decide

def sevenNineExtensionVector065Eligible0 :
    List MiddleFourModelPoint :=
  [1, 2, 3, 4, 5, 6]

def sevenNineExtensionVector065BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 7}, {0, 1, 4}, {1, 2, 3}, {2, 3, 7}, {4, 5, 6}, {5, 6, 7}, {2, 3, 5, 6}]).toFinset

theorem sevenNineExtensionVector065_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector065
        sevenNineExtensionVector065Base0 =
      sevenNineExtensionVector065Eligible0 := by
  decide

theorem sevenNineExtensionVector065_base_blocker0 :
    fastBlocker sevenNineExtensionVector065Base0 =
      sevenNineExtensionVector065BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
