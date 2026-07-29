import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector117

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector119 : List Nat :=
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem sevenNineExtensionVector119_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 119 [] =
      sevenNineExtensionVector119 := by
  decide

def sevenNineExtensionVector119BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def sevenNineExtensionVector119Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector119Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector119Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector119_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector119 =
      sevenNineExtensionVector119BlockerRows := by
  decide

theorem sevenNineExtensionVector119_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector119 =
      sevenNineExtensionVector119Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector119_blocker_rows]
  decide

def sevenNineExtensionVector119Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

theorem sevenNineExtensionVector119_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector119
        sevenNineExtensionVector119Selected0 =
      sevenNineExtensionVector119Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector119_blocker_rows]
  decide

def sevenNineExtensionVector119Eligible0 :
    List MiddleFourModelPoint :=
  [0, 2, 3, 4, 5, 6]

def sevenNineExtensionVector119BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 7}, {1, 3, 6}, {1, 3, 7}, {1, 4, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {4, 5, 6}, {4, 5, 7}]).toFinset

theorem sevenNineExtensionVector119_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector119
        sevenNineExtensionVector119Base0 =
      sevenNineExtensionVector119Eligible0 := by
  decide

theorem sevenNineExtensionVector119_base_blocker0 :
    fastBlocker sevenNineExtensionVector119Base0 =
      sevenNineExtensionVector119BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
