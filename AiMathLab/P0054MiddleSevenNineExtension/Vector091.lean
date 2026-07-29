import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector089

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector091 : List Nat :=
  [0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0]

theorem sevenNineExtensionVector091_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 91 [] =
      sevenNineExtensionVector091 := by
  decide

def sevenNineExtensionVector091BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

def sevenNineExtensionVector091Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector091Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector091Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector091_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector091 =
      sevenNineExtensionVector091BlockerRows := by
  decide

theorem sevenNineExtensionVector091_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector091 =
      sevenNineExtensionVector091Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector091_blocker_rows]
  decide

def sevenNineExtensionVector091Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

theorem sevenNineExtensionVector091_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector091
        sevenNineExtensionVector091Selected0 =
      sevenNineExtensionVector091Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector091_blocker_rows]
  decide

def sevenNineExtensionVector091Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 4, 5, 6]

def sevenNineExtensionVector091BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 5}, {0, 1, 7}, {0, 4, 7}, {1, 3, 5}, {1, 3, 7}, {2, 3, 6}, {2, 3, 7}, {3, 4, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector091_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector091
        sevenNineExtensionVector091Base0 =
      sevenNineExtensionVector091Eligible0 := by
  decide

theorem sevenNineExtensionVector091_base_blocker0 :
    fastBlocker sevenNineExtensionVector091Base0 =
      sevenNineExtensionVector091BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
