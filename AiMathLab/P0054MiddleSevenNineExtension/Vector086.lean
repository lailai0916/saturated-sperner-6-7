import AiMathLab.P0054MiddleSevenNineExtensionFinite
import AiMathLab.P0054MiddleSevenNineExtension.Vector084

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

def sevenNineExtensionVector086 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0]

theorem sevenNineExtensionVector086_certificate :
    MiddleSevenNineFinite.middleFourMultiplicityCertificate.getD 86 [] =
      sevenNineExtensionVector086 := by
  decide

def sevenNineExtensionVector086BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3}, {1, 4}, {1, 2, 5}, {0, 5}, {0, 2, 4}, {0, 1, 3}]

def sevenNineExtensionVector086Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def sevenNineExtensionVector086Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 3}]

def sevenNineExtensionVector086Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def sevenNineExtensionVector086Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def sevenNineExtensionVector086Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}]

def sevenNineExtensionVector086Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [sevenNineExtensionVector086Selected0, sevenNineExtensionVector086Selected1, sevenNineExtensionVector086Selected2, sevenNineExtensionVector086Selected3, sevenNineExtensionVector086Selected4]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem sevenNineExtensionVector086_blocker_rows :
    middleFourModelBlockerRows sevenNineExtensionVector086 =
      sevenNineExtensionVector086BlockerRows := by
  decide

theorem sevenNineExtensionVector086_selections :
    middleFourModelLiftSelectionRows sevenNineExtensionVector086 =
      sevenNineExtensionVector086Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

def sevenNineExtensionVector086Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector086_base0 :
    middleFourModelLiftBaseRows sevenNineExtensionVector086
        sevenNineExtensionVector086Selected0 =
      sevenNineExtensionVector086Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

theorem sevenNineExtensionVector086_selection0_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector086
      sevenNineExtensionVector086Selected0 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector086_base0,
    if_neg (by decide), if_neg (by decide)]
def sevenNineExtensionVector086Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3, 6}]

theorem sevenNineExtensionVector086_base1 :
    middleFourModelLiftBaseRows sevenNineExtensionVector086
        sevenNineExtensionVector086Selected1 =
      sevenNineExtensionVector086Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

theorem sevenNineExtensionVector086_selection1_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector086
      sevenNineExtensionVector086Selected1 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector086_base1,
    if_neg (by decide), if_neg (by decide)]
def sevenNineExtensionVector086Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4, 6}, {0, 1, 3}]

theorem sevenNineExtensionVector086_base2 :
    middleFourModelLiftBaseRows sevenNineExtensionVector086
        sevenNineExtensionVector086Selected2 =
      sevenNineExtensionVector086Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

theorem sevenNineExtensionVector086_selection2_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector086
      sevenNineExtensionVector086Selected2 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector086_base2,
    if_neg (by decide), if_neg (by decide)]
def sevenNineExtensionVector086Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5, 6}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector086_base3 :
    middleFourModelLiftBaseRows sevenNineExtensionVector086
        sevenNineExtensionVector086Selected3 =
      sevenNineExtensionVector086Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

theorem sevenNineExtensionVector086_selection3_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector086
      sevenNineExtensionVector086Selected3 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector086_base3,
    if_neg (by decide), if_neg (by decide)]
def sevenNineExtensionVector086Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5, 6}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

theorem sevenNineExtensionVector086_base4 :
    middleFourModelLiftBaseRows sevenNineExtensionVector086
        sevenNineExtensionVector086Selected4 =
      sevenNineExtensionVector086Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [sevenNineExtensionVector086_blocker_rows]
  decide

theorem sevenNineExtensionVector086_selection4_check :
    sevenNineModelSelectionCheck sevenNineExtensionVector086
      sevenNineExtensionVector086Selected4 = true := by
  unfold sevenNineModelSelectionCheck
  rw [sevenNineExtensionVector086_base4,
    if_neg (by decide), if_neg (by decide)]

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
