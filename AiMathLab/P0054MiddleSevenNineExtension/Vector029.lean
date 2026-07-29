import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector027

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector029 : List Nat :=
  [1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0]

theorem sevenNineExtensionVector029_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 29 [] =
      sevenNineExtensionVector029 := by
  decide

def sevenNineExtensionVector029BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

def sevenNineExtensionVector029Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector029Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector029Selected0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector029_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector029 =
      sevenNineExtensionVector029BlockerRows := by
  decide

theorem sevenNineExtensionVector029_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector029 =
      sevenNineExtensionVector029Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector029_blocker_rows]
  decide

def sevenNineExtensionVector029Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

theorem sevenNineExtensionVector029_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector029
        sevenNineExtensionVector029Selected0 =
      sevenNineExtensionVector029Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector029_blocker_rows]
  decide

def sevenNineExtensionVector029Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

def sevenNineExtensionVector029BaseBlocker0 :
    G413.Hypergraph MiddleFourModelPoint :=
  ([{0, 1, 7}, {0, 3, 5}, {0, 5, 7}, {0, 6, 7}, {1, 2, 3}, {1, 2, 7}, {2, 3, 6}, {2, 6, 7}, {4, 5, 6}, {4, 6, 7}]).toFinset

theorem sevenNineExtensionVector029_eligible0 :
    middleFourModelEligibleOldPointList sevenNineExtensionVector029
        sevenNineExtensionVector029Base0 =
      sevenNineExtensionVector029Eligible0 := by
  decide

theorem sevenNineExtensionVector029_base_blocker0 :
    fastBlocker sevenNineExtensionVector029Base0 =
      sevenNineExtensionVector029BaseBlocker0 := by
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
