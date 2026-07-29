import AiMathLab.P0054MiddleSevenNineK4Data
import AiMathLab.P0054MiddleSevenNineK4WitnessData

/-!
# Finite model for the two-extra-row `K₄` branch of the 7+9 split

The ordinary 7+9 extension checker deliberately starts at kernel-blocker
cardinality eight.  The `K₄` vector has kernel-blocker cardinality seven, so
it needs two extra rows.  This file gives that branch its own finite model.

The four fresh-point classes use fixed, disjoint intervals.  Keeping the
intervals fixed makes the later arbitrary-finite soundness map substantially
simpler than a packed representation, while `fastBlocker` still visits only
the points that occur in a row.
-/

namespace AiMathLab.P0054.MiddleSevenNineK4Finite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420

abbrev SevenNineK4Point := Fin 28

def sevenNineK4WidenPoint
    (point : MiddleFourModelPoint) : SevenNineK4Point :=
  ⟨point.val, by omega⟩

def sevenNineK4WidenRow
    (row : G413.Row MiddleFourModelPoint) :
    G413.Row SevenNineK4Point :=
  row.image sevenNineK4WidenPoint

def sevenNineK4WidenRows
    (rows : List (G413.Row MiddleFourModelPoint)) :
    List (G413.Row SevenNineK4Point) :=
  rows.map sevenNineK4WidenRow

def sevenNineK4Bases :
    List (List (G413.Row SevenNineK4Point)) :=
  [sevenNineK4WidenRows middleFourDegreeFourVector20Base0,
    sevenNineK4WidenRows middleFourDegreeFourVector20Base1,
    sevenNineK4WidenRows middleFourDegreeFourVector20Base2,
    sevenNineK4WidenRows middleFourDegreeFourVector20Base3,
    sevenNineK4WidenRows middleFourDegreeFourVector20Base4]

def sevenNineK4BaseIndex
    (base : List (G413.Row SevenNineK4Point)) : Nat :=
  if base = sevenNineK4Bases.getD 0 [] then 0
  else if base = sevenNineK4Bases.getD 1 [] then 1
  else if base = sevenNineK4Bases.getD 2 [] then 2
  else if base = sevenNineK4Bases.getD 3 [] then 3
  else if base = sevenNineK4Bases.getD 4 [] then 4
  else 5

def sevenNineK4KernelRows :
    List (G413.Row SevenNineK4Point) :=
  sevenNineK4WidenRows
    (middleFourModelKernelRows middleFourDegreeFourVector20)

def sevenNineK4Center : SevenNineK4Point := ⟨6, by omega⟩

def sevenNineK4OldPoints : List SevenNineK4Point :=
  (List.finRange 28).filter fun point => decide (point.val < 7)

def sevenNineK4OldPairAdmissible
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point) : Bool :=
  sevenNineK4OldPoints.all fun point =>
    decide (degree base.toFinset point +
      (if point ∈ oldFirst then 1 else 0) +
      (if point ∈ oldSecond then 1 else 0) ≤ 4)

def sevenNineK4OldPairs
    (base : List (G413.Row SevenNineK4Point)) :
    List (G413.Row SevenNineK4Point × G413.Row SevenNineK4Point) :=
  ((middleFourListPowerset sevenNineK4OldPoints).flatMap fun first =>
    (middleFourListPowerset sevenNineK4OldPoints).map fun second =>
      (first.toFinset, second.toFinset)).filter fun pair =>
        sevenNineK4OldPairAdmissible base pair.1 pair.2

theorem sevenNineK4Degree_insert_eq_add_indicator {alpha : Type*}
    [DecidableEq alpha] {H : G413.Hypergraph alpha} {E : G413.Row alpha}
    (hEH : E ∉ H) (point : alpha) :
    degree (insert E H) point = degree H point +
      (if point ∈ E then 1 else 0) := by
  by_cases hPoint : point ∈ E
  · rw [degree_insert_of_notMem hEH hPoint]
    simp [hPoint]
  · have hFilter : (insert E H).filter (fun row ↦ point ∈ row) =
        H.filter (fun row ↦ point ∈ row) := by
      ext row
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hRow, hPointRow⟩
        · exact (hPoint hPointRow).elim
        · exact ⟨hRow, hPointRow⟩
      · rintro ⟨hRow, hPointRow⟩
        exact ⟨Or.inr hRow, hPointRow⟩
    simp only [degree, hFilter, if_neg hPoint, Nat.add_zero]

def sevenNineK4FreshBlock (start count : Nat) :
    G413.Row SevenNineK4Point :=
  Finset.univ.filter fun point =>
    start ≤ point.val ∧ point.val < start + count

def sevenNineK4PrivateFirst (count : Nat) :
    G413.Row SevenNineK4Point :=
  sevenNineK4FreshBlock 7 count

def sevenNineK4PrivateSecond (count : Nat) :
    G413.Row SevenNineK4Point :=
  sevenNineK4FreshBlock 14 count

def sevenNineK4Shared (count : Nat) :
    G413.Row SevenNineK4Point :=
  sevenNineK4FreshBlock 21 count

def sevenNineK4FirstExtra
    (old : G413.Row SevenNineK4Point) (privateCount shared : Nat) :
    G413.Row SevenNineK4Point :=
  old ∪
    sevenNineK4PrivateFirst privateCount ∪
      sevenNineK4Shared shared

def sevenNineK4SecondExtra
    (old : G413.Row SevenNineK4Point) (privateCount shared : Nat) :
    G413.Row SevenNineK4Point :=
  old ∪
    sevenNineK4PrivateSecond privateCount ∪
      sevenNineK4Shared shared

theorem sevenNineK4FirstExtra_mem_old_iff
    (old : G413.Row SevenNineK4Point) (privateCount shared : Nat)
    {point : SevenNineK4Point} (hPoint : point ∈ sevenNineK4OldPoints) :
    point ∈ sevenNineK4FirstExtra old privateCount shared ↔ point ∈ old := by
  have hVal : point.val < 7 :=
    of_decide_eq_true (List.mem_filter.mp hPoint).2
  simp [sevenNineK4FirstExtra, sevenNineK4PrivateFirst,
    sevenNineK4Shared, sevenNineK4FreshBlock]
  omega

theorem sevenNineK4SecondExtra_mem_old_iff
    (old : G413.Row SevenNineK4Point) (privateCount shared : Nat)
    {point : SevenNineK4Point} (hPoint : point ∈ sevenNineK4OldPoints) :
    point ∈ sevenNineK4SecondExtra old privateCount shared ↔ point ∈ old := by
  have hVal : point.val < 7 :=
    of_decide_eq_true (List.mem_filter.mp hPoint).2
  simp [sevenNineK4SecondExtra, sevenNineK4PrivateSecond,
    sevenNineK4Shared, sevenNineK4FreshBlock]
  omega

def sevenNineK4OldCode (row : G413.Row SevenNineK4Point) : Nat :=
  row.sum fun point => 2 ^ point.val

def sevenNineK4ExtraKey
    (old : G413.Row SevenNineK4Point) (privateCount : Nat) : Nat :=
  sevenNineK4OldCode old * 8 + privateCount

def sevenNineK4RowsClutter
    (rows : List (G413.Row SevenNineK4Point)) : Bool :=
  rows.all fun left =>
    rows.all fun right =>
      !decide (left ⊆ right) || decide (left = right)

def sevenNineK4RowsMaxDegreeAtMost
    (rows : List (G413.Row SevenNineK4Point)) (bound : Nat) : Bool :=
  (List.finRange 28).all fun point =>
    decide (degree rows.toFinset point ≤ bound)

def sevenNineK4TwoExtraRows
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat) :
    List (G413.Row SevenNineK4Point) :=
  sevenNineK4SecondExtra oldSecond privateSecond shared ::
    sevenNineK4FirstExtra oldFirst privateFirst shared :: base

theorem sevenNineK4OldPairAdmissible_of_candidate_max
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hFirstNotBase :
      sevenNineK4FirstExtra oldFirst privateFirst shared ∉ base.toFinset)
    (hSecondNotRest :
      sevenNineK4SecondExtra oldSecond privateSecond shared ∉
        insert (sevenNineK4FirstExtra oldFirst privateFirst shared)
          base.toFinset)
    (hMax : sevenNineK4RowsMaxDegreeAtMost
      (sevenNineK4TwoExtraRows base oldFirst oldSecond
        privateFirst privateSecond shared) 4 = true) :
    sevenNineK4OldPairAdmissible base oldFirst oldSecond = true := by
  rw [sevenNineK4OldPairAdmissible, List.all_eq_true]
  intro point hPoint
  apply decide_eq_true
  have hPointMaxBool := (List.all_eq_true.mp hMax) point
    (List.mem_finRange point)
  have hPointMax := of_decide_eq_true hPointMaxBool
  rw [sevenNineK4TwoExtraRows, List.toFinset_cons,
    List.toFinset_cons,
    sevenNineK4Degree_insert_eq_add_indicator hSecondNotRest,
    sevenNineK4Degree_insert_eq_add_indicator hFirstNotBase] at hPointMax
  simp only [sevenNineK4FirstExtra_mem_old_iff oldFirst privateFirst shared hPoint,
    sevenNineK4SecondExtra_mem_old_iff oldSecond privateSecond shared hPoint]
    at hPointMax
  exact hPointMax

def sevenNineK4CandidateStructure
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat) : Bool :=
  let first := sevenNineK4FirstExtra oldFirst privateFirst shared
  let second := sevenNineK4SecondExtra oldSecond privateSecond shared
  let rows := second :: first :: base
  decide (sevenNineK4ExtraKey oldFirst privateFirst ≤
      sevenNineK4ExtraKey oldSecond privateSecond) &&
    decide (3 ≤ first.card ∧ first.card ≤ 7) &&
    decide (3 ≤ second.card ∧ second.card ≤ 7) &&
    decide (rows.toFinset.card = 9) &&
    sevenNineK4RowsClutter rows

theorem sevenNineK4RowsClutter_of_isClutter
    (rows : List (G413.Row SevenNineK4Point))
    (hClutter : IsClutter rows.toFinset) :
    sevenNineK4RowsClutter rows = true := by
  rw [sevenNineK4RowsClutter, List.all_eq_true]
  intro left hLeft
  rw [List.all_eq_true]
  intro right hRight
  by_cases hSubset : left ⊆ right
  · have hEq := hClutter (List.mem_toFinset.mpr hLeft)
      (List.mem_toFinset.mpr hRight) hSubset
    simp [hSubset, hEq]
  · simp [hSubset]

theorem sevenNineK4CandidateStructure_of
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hKey : sevenNineK4ExtraKey oldFirst privateFirst ≤
      sevenNineK4ExtraKey oldSecond privateSecond)
    (hFirstLower : 3 ≤
      (sevenNineK4FirstExtra oldFirst privateFirst shared).card)
    (hFirstUpper :
      (sevenNineK4FirstExtra oldFirst privateFirst shared).card ≤ 7)
    (hSecondLower : 3 ≤
      (sevenNineK4SecondExtra oldSecond privateSecond shared).card)
    (hSecondUpper :
      (sevenNineK4SecondExtra oldSecond privateSecond shared).card ≤ 7)
    (hCard : (sevenNineK4TwoExtraRows base oldFirst oldSecond
      privateFirst privateSecond shared).toFinset.card = 9)
    (hClutter : IsClutter
      (sevenNineK4TwoExtraRows base oldFirst oldSecond
        privateFirst privateSecond shared).toFinset) :
    sevenNineK4CandidateStructure base oldFirst oldSecond
      privateFirst privateSecond shared = true := by
  have hCard' : (sevenNineK4SecondExtra oldSecond privateSecond shared ::
      sevenNineK4FirstExtra oldFirst privateFirst shared :: base).toFinset.card =
      9 := by
    simpa [sevenNineK4TwoExtraRows] using hCard
  unfold sevenNineK4CandidateStructure
  rw [decide_eq_true hKey]
  simp only [Bool.true_and]
  rw [decide_eq_true ⟨hFirstLower, hFirstUpper⟩]
  simp only [Bool.true_and]
  rw [decide_eq_true ⟨hSecondLower, hSecondUpper⟩]
  simp only [Bool.true_and]
  rw [decide_eq_true hCard']
  apply sevenNineK4RowsClutter_of_isClutter
  simpa [sevenNineK4TwoExtraRows] using hClutter

def sevenNineK4DualRowsValid
    (dual : G413.Hypergraph SevenNineK4Point) : Bool :=
  decide (dual.card = 7) &&
    (sevenNineK4KernelRows.all fun row => decide (row ∈ dual)) &&
    decide ((dual.filter fun row =>
      3 ≤ row.card ∧ row.card ≤ 9).card = dual.card) &&
    (List.finRange 28).all (fun point =>
      decide (degree dual point ≤ 3)) &&
    decide (degree dual sevenNineK4Center = 3)

theorem sevenNineK4DualRowsValid_of
    (dual : G413.Hypergraph SevenNineK4Point)
    (hCard : dual.card = 7)
    (hKernel : ∀ row ∈ sevenNineK4KernelRows, row ∈ dual)
    (hRows : ∀ row ∈ dual, 3 ≤ row.card ∧ row.card ≤ 9)
    (hMaxDegree : ∀ point, degree dual point ≤ 3)
    (hCenter : degree dual sevenNineK4Center = 3) :
    sevenNineK4DualRowsValid dual = true := by
  unfold sevenNineK4DualRowsValid
  rw [decide_eq_true hCard]
  simp only [Bool.true_and]
  have hKernelCheck :
      sevenNineK4KernelRows.all (fun row => decide (row ∈ dual)) = true := by
    rw [List.all_eq_true]
    intro row hRow
    exact decide_eq_true (hKernel row hRow)
  rw [hKernelCheck]
  simp only [Bool.true_and]
  have hFilter : (dual.filter fun row =>
      3 ≤ row.card ∧ row.card ≤ 9) = dual := by
    apply Finset.filter_eq_self.mpr
    intro row hRow
    exact hRows row hRow
  rw [hFilter, decide_eq_true rfl]
  simp only [Bool.true_and]
  have hMaxCheck : (List.finRange 28).all (fun point =>
      decide (degree dual point ≤ 3)) = true := by
    rw [List.all_eq_true]
    intro point _hPoint
    exact decide_eq_true (hMaxDegree point)
  rw [hMaxCheck]
  exact decide_eq_true hCenter

def sevenNineK4CandidateValid
    (rows : List (G413.Row SevenNineK4Point)) : Bool :=
  decide (rows.toFinset.card = 9) &&
    sevenNineK4RowsClutter rows &&
    (rows.all fun row => decide (3 ≤ row.card ∧ row.card ≤ 7)) &&
    sevenNineK4RowsMaxDegreeAtMost rows 4 &&
    sevenNineK4DualRowsValid (fastBlocker rows)

def sevenNineK4ParameterCheck
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat) : Bool :=
  if sevenNineK4OldPairAdmissible base oldFirst oldSecond &&
      sevenNineK4CandidateStructure base oldFirst oldSecond
        privateFirst privateSecond shared then
    let first := sevenNineK4FirstExtra oldFirst privateFirst shared
    let second := sevenNineK4SecondExtra oldSecond privateSecond shared
    let afterBase := fastBlocker base
    let afterFirst := fastBlockerStep afterBase first
    let dual := fastBlockerStep afterFirst second
    !sevenNineK4DualRowsValid dual
  else
    true

def sevenNineK4FirstSizeValid
    (oldFirst : G413.Row SevenNineK4Point)
    (privateFirst shared : Nat) : Bool :=
  let first := sevenNineK4FirstExtra oldFirst privateFirst shared
  decide (3 ≤ first.card ∧ first.card ≤ 7)

def sevenNineK4KernelHitCheck
    (first second : G413.Row SevenNineK4Point) : Bool :=
  sevenNineK4KernelRows.all fun row =>
    decide (¬Disjoint row first) && decide (¬Disjoint row second)

def sevenNineK4OldPairKernelHit
    (oldFirst oldSecond : G413.Row SevenNineK4Point) : Bool :=
  sevenNineK4KernelRows.all fun row =>
    decide (¬Disjoint row oldFirst) && decide (¬Disjoint row oldSecond)

theorem sevenNineK4KernelRows_mem_oldPoints
    (row : G413.Row SevenNineK4Point) (hRow : row ∈ sevenNineK4KernelRows)
    (point : SevenNineK4Point) (hPoint : point ∈ row) :
    point ∈ sevenNineK4OldPoints := by
  rw [sevenNineK4KernelRows, sevenNineK4WidenRows, List.mem_map] at hRow
  obtain ⟨sourceRow, hSourceRow, rfl⟩ := hRow
  rw [sevenNineK4WidenRow, Finset.mem_image] at hPoint
  obtain ⟨sourcePoint, hSourcePoint, rfl⟩ := hPoint
  rw [middleFourModelKernelRows, List.mem_map] at hSourceRow
  obtain ⟨sourceIndex, _hSourceIndex, rfl⟩ := hSourceRow
  have hSourceBool := (Finset.mem_filter.mp hSourcePoint).2
  have hVal := of_decide_eq_true
    (Bool.and_eq_true_iff.mp hSourceBool).1
  have hLength :
      (middleFourModelSupports middleFourDegreeFourVector20).length = 6 := by
    decide
  rw [hLength] at hVal
  apply List.mem_filter.mpr
  refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
  change sourcePoint.val < 7
  omega

theorem sevenNineK4OldPairKernelHit_of_kernelHitCheck
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hHit : sevenNineK4KernelHitCheck
      (sevenNineK4FirstExtra oldFirst privateFirst shared)
      (sevenNineK4SecondExtra oldSecond privateSecond shared) = true) :
    sevenNineK4OldPairKernelHit oldFirst oldSecond = true := by
  unfold sevenNineK4OldPairKernelHit
  rw [List.all_eq_true]
  intro row hRow
  rw [Bool.and_eq_true_iff]
  have hRowHit := Bool.and_eq_true_iff.mp
    ((List.all_eq_true.mp hHit) row hRow)
  constructor
  · apply decide_eq_true
    obtain ⟨point, hPointRow, hPointFirst⟩ := Finset.not_disjoint_iff.mp
      (of_decide_eq_true hRowHit.1)
    exact Finset.not_disjoint_iff.mpr ⟨point, hPointRow,
      (sevenNineK4FirstExtra_mem_old_iff oldFirst privateFirst shared
        (sevenNineK4KernelRows_mem_oldPoints row hRow point hPointRow)).mp
          hPointFirst⟩
  · apply decide_eq_true
    obtain ⟨point, hPointRow, hPointSecond⟩ := Finset.not_disjoint_iff.mp
      (of_decide_eq_true hRowHit.2)
    exact Finset.not_disjoint_iff.mpr ⟨point, hPointRow,
      (sevenNineK4SecondExtra_mem_old_iff oldSecond privateSecond shared
        (sevenNineK4KernelRows_mem_oldPoints row hRow point hPointRow)).mp
          hPointSecond⟩

theorem sevenNineK4KernelHitCheck_of_dualRowsValid
    (base : List (G413.Row SevenNineK4Point))
    (first second : G413.Row SevenNineK4Point)
    (hValid : sevenNineK4DualRowsValid
      (fastBlocker (second :: first :: base)) = true) :
    sevenNineK4KernelHitCheck first second = true := by
  have hValid' := hValid
  unfold sevenNineK4DualRowsValid at hValid'
  have hWithoutCenter := (Bool.and_eq_true_iff.mp hValid').1
  have hWithoutMaxDegree := (Bool.and_eq_true_iff.mp hWithoutCenter).1
  have hCardAndKernel := (Bool.and_eq_true_iff.mp hWithoutMaxDegree).1
  have hKernelAll := (Bool.and_eq_true_iff.mp hCardAndKernel).2
  unfold sevenNineK4KernelHitCheck
  rw [List.all_eq_true]
  intro row hRow
  rw [Bool.and_eq_true_iff]
  have hRowBool := (List.all_eq_true.mp hKernelAll) row hRow
  have hRowBlocker : row ∈
      fastBlocker (second :: first :: base) := of_decide_eq_true hRowBool
  rw [fastBlocker_eq_blocker] at hRowBlocker
  constructor
  · apply decide_eq_true
    exact Finset.not_disjoint_iff.mpr
      ((mem_blocker.mp hRowBlocker).prop first (by simp))
  · apply decide_eq_true
    exact Finset.not_disjoint_iff.mpr
      ((mem_blocker.mp hRowBlocker).prop second (by simp))

theorem sevenNineK4DualRows_invalid_of_kernelHitCheck
    (base : List (G413.Row SevenNineK4Point))
    (first second : G413.Row SevenNineK4Point)
    (hHit : sevenNineK4KernelHitCheck first second = false) :
    sevenNineK4DualRowsValid
      (fastBlocker (second :: first :: base)) = false := by
  cases hValue : sevenNineK4DualRowsValid
      (fastBlocker (second :: first :: base)) with
  | false => rfl
  | true =>
      have hHitTrue := sevenNineK4KernelHitCheck_of_dualRowsValid
        base first second hValue
      rw [hHit] at hHitTrue
      contradiction

theorem sevenNineK4DualRows_invalid_of_oldPairKernelHit
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hHit : sevenNineK4OldPairKernelHit oldFirst oldSecond = false) :
    sevenNineK4DualRowsValid (fastBlocker
      (sevenNineK4SecondExtra oldSecond privateSecond shared ::
        sevenNineK4FirstExtra oldFirst privateFirst shared :: base)) = false := by
  cases hValue : sevenNineK4DualRowsValid (fastBlocker
      (sevenNineK4SecondExtra oldSecond privateSecond shared ::
        sevenNineK4FirstExtra oldFirst privateFirst shared :: base)) with
  | false => rfl
  | true =>
      have hInner := sevenNineK4KernelHitCheck_of_dualRowsValid base
        (sevenNineK4FirstExtra oldFirst privateFirst shared)
        (sevenNineK4SecondExtra oldSecond privateSecond shared) hValue
      have hOld := sevenNineK4OldPairKernelHit_of_kernelHitCheck
        oldFirst oldSecond privateFirst privateSecond shared hInner
      rw [hHit] at hOld
      contradiction

theorem sevenNineK4FirstSizeValid_of_candidateStructure
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hStructure : sevenNineK4CandidateStructure base oldFirst oldSecond
      privateFirst privateSecond shared = true) :
    sevenNineK4FirstSizeValid oldFirst privateFirst shared = true := by
  unfold sevenNineK4CandidateStructure at hStructure
  have hWithoutClutter := (Bool.and_eq_true_iff.mp hStructure).1
  have hWithoutRowsCard := (Bool.and_eq_true_iff.mp hWithoutClutter).1
  have hKeyFirstSecond := (Bool.and_eq_true_iff.mp hWithoutRowsCard).1
  have hFirst := (Bool.and_eq_true_iff.mp hKeyFirstSecond).2
  simpa [sevenNineK4FirstSizeValid] using hFirst

def sevenNineK4BlockerWitnessCheck
    (rows witnesses : List (G413.Row SevenNineK4Point)) : Bool :=
  decide (witnesses.toFinset.card = 8) &&
    witnesses.all fun witness =>
      supportPrivateBlockerCertificate rows.toFinset witness

def sevenNineK4WitnessRowsFromCommon
    (common : List Nat)
    (baseIndex oldFirstCode oldSecondCode privateFirst privateSecond shared : Nat) :
    List (G413.Row SevenNineK4Point) :=
  let codes :=
    if common.length = 8 then
      common
    else
      match sevenNineK4ExceptionalWitnessCode?
          baseIndex oldFirstCode oldSecondCode
          privateFirst privateSecond shared with
      | some code => common ++ [code]
      | none => common
  codes.map sevenNineK4DecodeWitnessRow

theorem sevenNineK4DualRows_invalid_of_blockerWitnessCheck
    (rows witnesses : List (G413.Row SevenNineK4Point))
    (hCheck : sevenNineK4BlockerWitnessCheck rows witnesses = true) :
    sevenNineK4DualRowsValid (fastBlocker rows) = false := by
  cases hValue : sevenNineK4DualRowsValid (fastBlocker rows) with
  | false => rfl
  | true =>
      have hCheckPair := Bool.and_eq_true_iff.mp hCheck
      have hWitnessCard : witnesses.toFinset.card = 8 :=
        of_decide_eq_true hCheckPair.1
      have hWitnessSubset : witnesses.toFinset ⊆ blocker rows.toFinset := by
        intro witness hWitness
        apply supportPrivateBlockerCertificate_eq_true_iff.mp
        exact (List.all_eq_true.mp hCheckPair.2) witness
          (List.mem_toFinset.mp hWitness)
      have hCardLe := Finset.card_le_card hWitnessSubset
      have hValue' := hValue
      unfold sevenNineK4DualRowsValid at hValue'
      have hWithoutCenter := (Bool.and_eq_true_iff.mp hValue').1
      have hWithoutMaxDegree := (Bool.and_eq_true_iff.mp hWithoutCenter).1
      have hCardAndKernel := (Bool.and_eq_true_iff.mp hWithoutMaxDegree).1
      have hDualCard : (fastBlocker rows).card = 7 :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hCardAndKernel).1
      rw [fastBlocker_eq_blocker] at hDualCard
      rw [hWitnessCard, hDualCard] at hCardLe
      omega

def sevenNineK4OldPairCheck
    (base : List (G413.Row SevenNineK4Point))
    (oldPair : G413.Row SevenNineK4Point ×
      G413.Row SevenNineK4Point) : Bool :=
  let baseIndex := sevenNineK4BaseIndex base
  let oldFirstCode := sevenNineK4OldCode oldPair.1
  let oldSecondCode := sevenNineK4OldCode oldPair.2
  let commonWitnessCodes := sevenNineK4UniversalWitnessCodes
    baseIndex oldFirstCode oldSecondCode
  if sevenNineK4OldPairKernelHit oldPair.1 oldPair.2 then
    let afterBase := fastBlocker base
    (List.range 8).all fun privateFirst =>
      (List.range 8).all fun shared =>
        if sevenNineK4FirstSizeValid oldPair.1 privateFirst shared then
          let first := sevenNineK4FirstExtra oldPair.1 privateFirst shared
          let afterFirst := fastBlockerStep afterBase first
          (List.range 8).all fun privateSecond =>
            if sevenNineK4CandidateStructure base oldPair.1 oldPair.2
                  privateFirst privateSecond shared then
              let second := sevenNineK4SecondExtra oldPair.2 privateSecond shared
              if sevenNineK4KernelHitCheck first second then
                let rows := second :: first :: base
                let witnesses := sevenNineK4WitnessRowsFromCommon
                  commonWitnessCodes baseIndex oldFirstCode oldSecondCode
                  privateFirst privateSecond shared
                if sevenNineK4BlockerWitnessCheck rows witnesses then
                  true
                else
                  !sevenNineK4DualRowsValid
                    (fastBlockerStep afterFirst second)
              else
                true
            else
              true
        else
          true
  else
    true

def sevenNineK4ChunkOldPairs
    (base : List (G413.Row SevenNineK4Point))
    (chunkIndex : Nat) :
    List (G413.Row SevenNineK4Point × G413.Row SevenNineK4Point) :=
  sevenNineK4OldPairDataChunk (sevenNineK4BaseIndex base) chunkIndex

def sevenNineK4ChunkCheck
    (baseIndex chunkIndex : Nat) : Bool :=
  let base := sevenNineK4Bases.getD baseIndex []
  (sevenNineK4ChunkOldPairs base chunkIndex).all
    (sevenNineK4OldPairCheck base)

def sevenNineK4PartWidth : Nat := 27

def sevenNineK4ChunkPartOldPairs
    (base : List (G413.Row SevenNineK4Point))
    (chunkIndex partIndex : Nat) :
    List (G413.Row SevenNineK4Point × G413.Row SevenNineK4Point) :=
  (sevenNineK4ChunkOldPairs base chunkIndex).drop
    (partIndex * sevenNineK4PartWidth) |>.take sevenNineK4PartWidth

def sevenNineK4ChunkPartCheck
    (baseIndex chunkIndex partIndex : Nat) : Bool :=
  let base := sevenNineK4Bases.getD baseIndex []
  (sevenNineK4ChunkPartOldPairs base chunkIndex partIndex).all
    (sevenNineK4OldPairCheck base)

theorem all_eq_true_of_three_parts {α : Type*}
    {xs : List α} {p : α → Bool}
    (hLength : xs.length ≤ 81)
    (hFirst : (xs.take 27).all p = true)
    (hSecond : ((xs.drop 27).take 27).all p = true)
    (hThird : ((xs.drop 54).take 27).all p = true) :
    xs.all p = true := by
  have hRest : ((xs.drop 27).take 54).all p = true := by
    rw [show 54 = 27 + 27 by omega, List.take_add,
      List.all_append, Bool.and_eq_true]
    refine ⟨hSecond, ?_⟩
    simpa only [List.drop_drop] using hThird
  have hTake : (xs.take 81).all p = true := by
    rw [show 81 = 27 + 54 by omega, List.take_add,
      List.all_append, Bool.and_eq_true]
    exact ⟨hFirst, hRest⟩
  simpa only [List.take_of_length_le hLength] using hTake

theorem sevenNineK4ChunkCheck_of_parts
    (baseIndex chunkIndex : Nat)
    (hLength : (sevenNineK4ChunkOldPairs
      (sevenNineK4Bases.getD baseIndex []) chunkIndex).length ≤ 81)
    (hFirst : sevenNineK4ChunkPartCheck baseIndex chunkIndex 0 = true)
    (hSecond : sevenNineK4ChunkPartCheck baseIndex chunkIndex 1 = true)
    (hThird : sevenNineK4ChunkPartCheck baseIndex chunkIndex 2 = true) :
    sevenNineK4ChunkCheck baseIndex chunkIndex = true := by
  let base := sevenNineK4Bases.getD baseIndex []
  have hFirst' :
      (sevenNineK4ChunkPartOldPairs base chunkIndex 0).all
        (sevenNineK4OldPairCheck base) = true := by
    simpa [sevenNineK4ChunkPartCheck, base] using hFirst
  have hSecond' :
      (sevenNineK4ChunkPartOldPairs base chunkIndex 1).all
        (sevenNineK4OldPairCheck base) = true := by
    simpa [sevenNineK4ChunkPartCheck, base] using hSecond
  have hThird' :
      (sevenNineK4ChunkPartOldPairs base chunkIndex 2).all
        (sevenNineK4OldPairCheck base) = true := by
    simpa [sevenNineK4ChunkPartCheck, base] using hThird
  change (sevenNineK4ChunkOldPairs base chunkIndex).all
    (sevenNineK4OldPairCheck base) = true
  apply all_eq_true_of_three_parts
  · simpa [base] using hLength
  · simpa [sevenNineK4ChunkPartOldPairs, sevenNineK4PartWidth] using hFirst'
  · simpa [sevenNineK4ChunkPartOldPairs, sevenNineK4PartWidth] using hSecond'
  · simpa [sevenNineK4ChunkPartOldPairs, sevenNineK4PartWidth] using hThird'

def sevenNineK4BaseChunkCount (baseIndex : Nat) : Nat :=
  if baseIndex = 0 then 27 else 9

def sevenNineK4AllChunkIndices : List (Nat × Nat) :=
  (List.range 5).flatMap fun baseIndex =>
    (List.range (sevenNineK4BaseChunkCount baseIndex)).map fun chunkIndex =>
      (baseIndex, chunkIndex)

def sevenNineK4BaseChunks (baseIndex : Nat) :
    List (List (G413.Row SevenNineK4Point ×
      G413.Row SevenNineK4Point)) :=
  let base := sevenNineK4Bases.getD baseIndex []
  (List.range (sevenNineK4BaseChunkCount baseIndex)).map fun chunkIndex =>
    sevenNineK4ChunkOldPairs base chunkIndex

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This finite list equality is closed by kernel reduction over 2,187 old pairs.
theorem sevenNineK4BaseChunks_flatten_0 :
    (sevenNineK4BaseChunks 0).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD 0 []) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This finite list equality is closed by kernel reduction over the second base.
theorem sevenNineK4BaseChunks_flatten_1 :
    (sevenNineK4BaseChunks 1).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD 1 []) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This finite list equality is closed by kernel reduction over the third base.
theorem sevenNineK4BaseChunks_flatten_2 :
    (sevenNineK4BaseChunks 2).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD 2 []) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This finite list equality is closed by kernel reduction over the fourth base.
theorem sevenNineK4BaseChunks_flatten_3 :
    (sevenNineK4BaseChunks 3).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD 3 []) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This finite list equality is closed by kernel reduction over the fifth base.
theorem sevenNineK4BaseChunks_flatten_4 :
    (sevenNineK4BaseChunks 4).flatMap id =
      sevenNineK4OldPairs (sevenNineK4Bases.getD 4 []) := by
  decide

def sevenNineK4BaseCheck
    (base : List (G413.Row SevenNineK4Point)) : Bool :=
  (sevenNineK4OldPairs base).all (sevenNineK4OldPairCheck base)

theorem sevenNineK4BaseCheck_of_chunks
    (base : List (G413.Row SevenNineK4Point))
    (chunks : List (List (G413.Row SevenNineK4Point ×
      G413.Row SevenNineK4Point)))
    (hFlatten : chunks.flatMap id = sevenNineK4OldPairs base)
    (hChunks : chunks.all (fun chunk =>
      chunk.all (sevenNineK4OldPairCheck base)) = true) :
    sevenNineK4BaseCheck base = true := by
  unfold sevenNineK4BaseCheck
  rw [← hFlatten]
  clear hFlatten
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      change (chunk.all (sevenNineK4OldPairCheck base) &&
        chunks.all (fun rest =>
          rest.all (sevenNineK4OldPairCheck base))) = true at hChunks
      have hBoth := Bool.and_eq_true_iff.mp hChunks
      rw [List.flatMap_cons, List.all_append]
      exact Bool.and_eq_true_iff.mpr ⟨hBoth.1, ih hBoth.2⟩

def sevenNineK4ExtensionCheck : Bool :=
  sevenNineK4Bases.all sevenNineK4BaseCheck

theorem sevenNineK4OldPairCheck_of_extensionCheck
    (base : List (G413.Row SevenNineK4Point))
    (oldPair : G413.Row SevenNineK4Point ×
      G413.Row SevenNineK4Point)
    (hCheck : sevenNineK4ExtensionCheck = true)
    (hBase : base ∈ sevenNineK4Bases)
    (hOldPair : oldPair ∈ sevenNineK4OldPairs base) :
    sevenNineK4OldPairCheck base oldPair = true := by
  have hBaseCheck := (List.all_eq_true.mp hCheck) base hBase
  exact (List.all_eq_true.mp hBaseCheck) oldPair hOldPair

theorem sevenNineK4DualRows_invalid_of_oldPairCheck
    (base : List (G413.Row SevenNineK4Point))
    (oldFirst oldSecond : G413.Row SevenNineK4Point)
    (privateFirst privateSecond shared : Nat)
    (hCheck : sevenNineK4OldPairCheck base
      (oldFirst, oldSecond) = true)
    (hPrivateFirst : privateFirst < 8)
    (hPrivateSecond : privateSecond < 8)
    (hShared : shared < 8)
    (hStructure : sevenNineK4CandidateStructure base oldFirst oldSecond
      privateFirst privateSecond shared = true) :
    sevenNineK4DualRowsValid (fastBlocker
      (sevenNineK4SecondExtra oldSecond privateSecond shared ::
        sevenNineK4FirstExtra oldFirst privateFirst shared :: base)) = false := by
  unfold sevenNineK4OldPairCheck at hCheck
  by_cases hOldHit : sevenNineK4OldPairKernelHit oldFirst oldSecond = true
  · rw [if_pos hOldHit] at hCheck
    have hFirst := (List.all_eq_true.mp hCheck) privateFirst
      (List.mem_range.mpr hPrivateFirst)
    have hCommon := (List.all_eq_true.mp hFirst) shared
      (List.mem_range.mpr hShared)
    have hFirstSize := sevenNineK4FirstSizeValid_of_candidateStructure
      base oldFirst oldSecond privateFirst privateSecond shared hStructure
    rw [if_pos hFirstSize] at hCommon
    have hSecond := (List.all_eq_true.mp hCommon) privateSecond
      (List.mem_range.mpr hPrivateSecond)
    rw [if_pos hStructure] at hSecond
    let first := sevenNineK4FirstExtra oldFirst privateFirst shared
    let second := sevenNineK4SecondExtra oldSecond privateSecond shared
    by_cases hHit : sevenNineK4KernelHitCheck first second = true
    · rw [if_pos hHit] at hSecond
      let rows := second :: first :: base
      let witnesses := sevenNineK4WitnessRowsFromCommon
        (sevenNineK4UniversalWitnessCodes
          (sevenNineK4BaseIndex base)
          (sevenNineK4OldCode oldFirst)
          (sevenNineK4OldCode oldSecond))
        (sevenNineK4BaseIndex base)
        (sevenNineK4OldCode oldFirst)
        (sevenNineK4OldCode oldSecond)
        privateFirst privateSecond shared
      by_cases hWitness :
          sevenNineK4BlockerWitnessCheck rows witnesses = true
      · exact sevenNineK4DualRows_invalid_of_blockerWitnessCheck
          rows witnesses hWitness
      · rw [if_neg hWitness] at hSecond
        simpa [rows, first, second, fastBlocker] using hSecond
    · have hHitFalse : sevenNineK4KernelHitCheck first second = false :=
        Bool.eq_false_of_not_eq_true hHit
      exact sevenNineK4DualRows_invalid_of_kernelHitCheck
        base first second hHitFalse
  · exact sevenNineK4DualRows_invalid_of_oldPairKernelHit base
      oldFirst oldSecond privateFirst privateSecond shared
      (Bool.eq_false_of_not_eq_true hOldHit)

end AiMathLab.P0054.MiddleSevenNineK4Finite
