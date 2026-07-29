import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector20 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector20_certificate :
    middleFourMultiplicityCertificate.getD 20 [] =
      middleFourDegreeFourVector20 := by
  decide

def middleFourDegreeFourVector20BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3}, {1, 4}, {1, 2, 5}, {0, 5}, {0, 2, 4}, {0, 1, 3}]

def middleFourDegreeFourVector20Selections :
    List (List (G413.Row MiddleFourModelPoint)) :=
  [[], [{0, 1, 3}], [{0, 2, 4}], [{1, 2, 5}], [{3, 4, 5}]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector20_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector20 =
      middleFourDegreeFourVector20BlockerRows := by
  decide

theorem middleFourDegreeFourVector20_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector20 =
      middleFourDegreeFourVector20Selections := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

def middleFourDegreeFourVector20Selected0 :
    List (G413.Row MiddleFourModelPoint) :=
  []

def middleFourDegreeFourVector20Base0 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

def middleFourDegreeFourVector20Eligible0 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5, 6]

theorem middleFourDegreeFourVector20_base0 :
    middleFourModelLiftBaseRows middleFourDegreeFourVector20
        middleFourDegreeFourVector20Selected0 =
      middleFourDegreeFourVector20Base0 := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

theorem middleFourDegreeFourVector20_eligible0 :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base0 =
      middleFourDegreeFourVector20Eligible0 := by
  decide

def middleFourDegreeFourVector20Selected1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 1, 3}]

def middleFourDegreeFourVector20Base1 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3, 6}]

def middleFourDegreeFourVector20Eligible1 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

theorem middleFourDegreeFourVector20_base1 :
    middleFourModelLiftBaseRows middleFourDegreeFourVector20
        middleFourDegreeFourVector20Selected1 =
      middleFourDegreeFourVector20Base1 := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

theorem middleFourDegreeFourVector20_eligible1 :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base1 =
      middleFourDegreeFourVector20Eligible1 := by
  decide

def middleFourDegreeFourVector20Selected2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 4}]

def middleFourDegreeFourVector20Base2 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4, 6}, {0, 1, 3}]

def middleFourDegreeFourVector20Eligible2 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

theorem middleFourDegreeFourVector20_base2 :
    middleFourModelLiftBaseRows middleFourDegreeFourVector20
        middleFourDegreeFourVector20Selected2 =
      middleFourDegreeFourVector20Base2 := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

theorem middleFourDegreeFourVector20_eligible2 :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base2 =
      middleFourDegreeFourVector20Eligible2 := by
  decide

def middleFourDegreeFourVector20Selected3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{1, 2, 5}]

def middleFourDegreeFourVector20Base3 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5, 6}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

def middleFourDegreeFourVector20Eligible3 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

theorem middleFourDegreeFourVector20_base3 :
    middleFourModelLiftBaseRows middleFourDegreeFourVector20
        middleFourDegreeFourVector20Selected3 =
      middleFourDegreeFourVector20Base3 := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

theorem middleFourDegreeFourVector20_eligible3 :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base3 =
      middleFourDegreeFourVector20Eligible3 := by
  decide

def middleFourDegreeFourVector20Selected4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}]

def middleFourDegreeFourVector20Base4 :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5, 6}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 5, 6}, {0, 2, 4}, {0, 1, 3}]

def middleFourDegreeFourVector20Eligible4 :
    List MiddleFourModelPoint :=
  [0, 1, 2, 3, 4, 5]

theorem middleFourDegreeFourVector20_base4 :
    middleFourModelLiftBaseRows middleFourDegreeFourVector20
        middleFourDegreeFourVector20Selected4 =
      middleFourDegreeFourVector20Base4 := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector20_blocker_rows]
  decide

theorem middleFourDegreeFourVector20_eligible4 :
    middleFourModelEligibleOldPointList middleFourDegreeFourVector20
        middleFourDegreeFourVector20Base4 =
      middleFourDegreeFourVector20Eligible4 := by
  decide


end AiMathLab.P0054.G420
