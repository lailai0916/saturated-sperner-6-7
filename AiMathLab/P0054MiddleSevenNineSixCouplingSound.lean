import AiMathLab.P0054MiddleSevenNineThreeResidualRealization
import AiMathLab.P0054MiddleSevenNineSixCouplingCertificate

/-!
# Arbitrary-finite soundness for the six-row coupling certificate

This module keeps the actual points attached to the finite support masks.
That is essential because distinct points with the same mask must remain
distinct when the certificate counts two-point transversals.
-/

namespace AiMathLab.P0054.MiddleSevenNineSixCouplingSound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.MiddleSevenNineThreeResidualRealization
open AiMathLab.P0054.MiddleSevenNineSixCouplingFinite

def doubleDeletedRowLift {alpha : Type*} [DecidableEq alpha]
    (center common : alpha) (R : Row alpha) : Row alpha :=
  insert center (insert common R)

theorem doubleDelete_lift_image
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {center common : alpha}
    (hCenter : ∀ R ∈ H, center ∈ R)
    (hCommon : ∀ R ∈ deletePoint H center, common ∈ R) :
    H = (deletePoint (deletePoint H center) common).image
      (doubleDeletedRowLift center common) := by
  classical
  ext row
  constructor
  · intro hRow
    let centered := row.erase center
    have hCentered : centered ∈ deletePoint H center := by
      exact Finset.mem_image.mpr ⟨row, hRow, rfl⟩
    have hCommonCentered : common ∈ centered := hCommon centered hCentered
    let residual := centered.erase common
    have hResidual : residual ∈ deletePoint (deletePoint H center) common := by
      exact Finset.mem_image.mpr ⟨centered, hCentered, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨residual, hResidual, ?_⟩
    unfold doubleDeletedRowLift
    calc
      insert center (insert common residual) = insert center centered := by
        rw [show residual = centered.erase common by rfl,
          Finset.insert_erase hCommonCentered]
      _ = row := Finset.insert_erase (hCenter row hRow)
  · intro hImage
    obtain ⟨residual, hResidual, hLiftRow⟩ := Finset.mem_image.mp hImage
    obtain ⟨centered, hCentered, hCenteredResidual⟩ :=
      Finset.mem_image.mp hResidual
    obtain ⟨source, hSource, hSourceCentered⟩ :=
      Finset.mem_image.mp hCentered
    have hCommonCentered : common ∈ centered := hCommon centered hCentered
    have hCenterSource : center ∈ source := hCenter source hSource
    have hLiftSource :
        doubleDeletedRowLift center common residual = source := by
      unfold doubleDeletedRowLift
      rw [← hCenteredResidual, Finset.insert_erase hCommonCentered,
        ← hSourceCentered, Finset.insert_erase hCenterSource]
    rw [← hLiftRow, hLiftSource]
    exact hSource

theorem doubleDelete_rows_avoid_first
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {first second : alpha} {R : Row alpha}
    (hR : R ∈ deletePoint (deletePoint H first) second) :
    first ∉ R := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  intro hFirst
  exact deletePoint_rows_avoid hS (Finset.mem_of_mem_erase hFirst)

theorem doubleDelete_rows_avoid_external
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {first second external : alpha}
    (hAvoid : ∀ R ∈ H, external ∉ R)
    {R : Row alpha}
    (hR : R ∈ deletePoint (deletePoint H first) second) :
    external ∉ R := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hS
  intro hExternal
  exact hAvoid source hSource
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hExternal))

def threeLiftedRows {alpha : Type*} [DecidableEq alpha]
    (center common : alpha) (A B C : Row alpha) : G413.Hypergraph alpha :=
  {doubleDeletedRowLift center common A,
    doubleDeletedRowLift center common B,
    doubleDeletedRowLift center common C}

theorem threeLiftedRows_eq_of_doubleDelete
    {alpha : Type*} [DecidableEq alpha]
    {H residual : G413.Hypergraph alpha} {center common : alpha}
    {A B C : Row alpha}
    (hResidual : residual = deletePoint (deletePoint H center) common)
    (hRows : residual = {A, B, C})
    (hCenter : ∀ R ∈ H, center ∈ R)
    (hCommon : ∀ R ∈ deletePoint H center, common ∈ R) :
    H = threeLiftedRows center common A B C := by
  rw [doubleDelete_lift_image hCenter hCommon, ← hResidual, hRows]
  simp [threeLiftedRows]

def threeLiftedSupportMask {alpha : Type*} [DecidableEq alpha]
    (center common : alpha) (A B C : Row alpha) (point : alpha) : Nat :=
  if point = center ∨ point = common then 7
  else threeSupportMask A B C point

theorem threeLiftedSupportMask_eq
    {alpha : Type*} [DecidableEq alpha]
    (center common : alpha) (A B C : Row alpha) (point : alpha) :
    threeLiftedSupportMask center common A B C point =
      threeSupportMask
        (doubleDeletedRowLift center common A)
        (doubleDeletedRowLift center common B)
        (doubleDeletedRowLift center common C) point := by
  by_cases hCenter : point = center
  · subst point
    simp [threeLiftedSupportMask, threeSupportMask, doubleDeletedRowLift]
  · by_cases hCommon : point = common
    · subst point
      simp [threeLiftedSupportMask, threeSupportMask, doubleDeletedRowLift]
    · simp [threeLiftedSupportMask, threeSupportMask, doubleDeletedRowLift,
        hCenter, hCommon]

theorem threeLiftedSupportMask_rank_eq_degree
    {alpha : Type*} [DecidableEq alpha]
    {side : G413.Hypergraph alpha} {center common point : alpha}
    {A B C : Row alpha}
    (hSide : side = threeLiftedRows center common A B C)
    (hSideCard : side.card = 3) :
    threeMaskRank (threeLiftedSupportMask center common A B C point) =
      degree side point := by
  let LA := doubleDeletedRowLift center common A
  let LB := doubleDeletedRowLift center common B
  let LC := doubleDeletedRowLift center common C
  have hRows : side = {LA, LB, LC} := by
    simpa [threeLiftedRows, LA, LB, LC] using hSide
  have hRowsCard : ({LA, LB, LC} : G413.Hypergraph alpha).card = 3 :=
    (congrArg Finset.card hRows.symm).trans hSideCard
  obtain ⟨hLAB, hLAC, hLBC⟩ :=
    three_rows_pairwise_ne_of_card_eq_three hRowsCard
  rw [threeLiftedSupportMask_eq]
  simpa [LA, LB, LC] using
    threeMaskRank_supportMask_eq_degree hLAB hLAC hLBC hRows point

theorem map_threeLiftedSupportMask_append_common
    {alpha : Type*} [DecidableEq alpha]
    {center common : alpha} {A B C : Row alpha}
    {points : List alpha} {profile : List Nat}
    (hCenter : ∀ point ∈ points, point ≠ center)
    (hCommon : ∀ point ∈ points, point ≠ common)
    (hProfile : points.map (threeSupportMask A B C) = profile) :
    (points ++ [common]).map
        (threeLiftedSupportMask center common A B C) =
      profile ++ [7] := by
  have hMap :
      points.map (threeLiftedSupportMask center common A B C) =
        points.map (threeSupportMask A B C) := by
    apply List.map_congr_left
    intro point hPoint
    simp [threeLiftedSupportMask, hCenter point hPoint,
      hCommon point hPoint]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [hMap, hProfile]
  simp [threeLiftedSupportMask]

theorem nodup_append_singleton
    {alpha : Type*} [DecidableEq alpha]
    {points : List alpha} {point : alpha}
    (hNodup : points.Nodup) (hPoint : point ∉ points) :
    (points ++ [point]).Nodup := by
  apply hNodup.append (by simp)
  apply List.disjoint_left.mpr
  intro x hxPoints hxSingleton
  simp only [List.mem_singleton] at hxSingleton
  exact hPoint (hxSingleton ▸ hxPoints)

theorem point_not_mem_of_actual_points_avoid
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {points : List alpha} {point : alpha}
    (hPoints : ∀ x, x ∈ points ↔ ∃ R ∈ H, x ∈ R)
    (hAvoid : ∀ R ∈ H, point ∉ R) :
    point ∉ points := by
  intro hPoint
  obtain ⟨R, hRH, hPointR⟩ := (hPoints point).mp hPoint
  exact hAvoid R hRH hPointR

theorem threeLiftedSupportMask_cover
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {points : List alpha}
    {center common point : alpha} {A B C : Row alpha}
    (hRows : H = {A, B, C})
    (hPoints : ∀ x, x ∈ points ↔ ∃ R ∈ H, x ∈ R)
    (hNonzero : threeLiftedSupportMask center common A B C point ≠ 0) :
    point = center ∨ point ∈ points ++ [common] := by
  by_cases hCenter : point = center
  · exact Or.inl hCenter
  by_cases hCommon : point = common
  · exact Or.inr (by simp [hCommon])
  have hMembership : point ∈ A ∨ point ∈ B ∨ point ∈ C := by
    by_cases hA : point ∈ A
    · exact Or.inl hA
    by_cases hB : point ∈ B
    · exact Or.inr (Or.inl hB)
    by_cases hC : point ∈ C
    · exact Or.inr (Or.inr hC)
    · simp [threeLiftedSupportMask, threeSupportMask,
        hCenter, hCommon, hA, hB, hC] at hNonzero
  have hPointList : point ∈ points := by
    apply (hPoints point).mpr
    rcases hMembership with hA | hB | hC
    · exact ⟨A, by simp [hRows], hA⟩
    · exact ⟨B, by simp [hRows], hB⟩
    · exact ⟨C, by simp [hRows], hC⟩
  exact Or.inr (by simp [hPointList])

theorem threeLiftedSupportMask_eq_zero_of_avoids
    {alpha : Type*} [DecidableEq alpha]
    {center common point : alpha} {A B C : Row alpha}
    (hCenter : point ≠ center) (hCommon : point ≠ common)
    (hA : point ∉ A) (hB : point ∉ B) (hC : point ∉ C) :
    threeLiftedSupportMask center common A B C point = 0 := by
  simp [threeLiftedSupportMask, threeSupportMask,
    hCenter, hCommon, hA, hB, hC]

theorem degree_add_eq_of_union_disjoint
    {alpha : Type*} [DecidableEq alpha]
    {left right whole : G413.Hypergraph alpha}
    (hCover : left ∪ right = whole)
    (hDisjoint : Disjoint left right)
    (point : alpha) :
    degree left point + degree right point = degree whole point := by
  have hFiltered :
      Disjoint (left.filter fun R ↦ point ∈ R)
        (right.filter fun R ↦ point ∈ R) :=
    Finset.disjoint_left.mpr fun row hRowLeft hRowRight ↦
      Finset.disjoint_left.mp hDisjoint
        (Finset.filter_subset (fun R ↦ point ∈ R) left hRowLeft)
        (Finset.filter_subset (fun R ↦ point ∈ R) right hRowRight)
  rw [← hCover]
  unfold degree
  rw [Finset.filter_union, Finset.card_union_of_disjoint hFiltered]

theorem actualCouplingMergeAux
    {alpha : Type*} [DecidableEq alpha]
    {a b : alpha}
    (actualMask leftMask rightMask : alpha → Nat)
    {left right accumulated : List alpha}
    (hab : a ≠ b)
    (hActualA : actualMask a = 7)
    (hActualB : actualMask b = 56)
    (hActualJoin : ∀ point, point ≠ a → point ≠ b →
      actualMask point = sixJoinSupports (leftMask point) (rightMask point))
    (hLeftNodup : left.Nodup)
    (hRightNodup : right.Nodup)
    (hAccumulatedNodup : accumulated.Nodup)
    (hLeftAccumulated : List.Disjoint left accumulated)
    (hRightAccumulated : List.Disjoint right accumulated)
    (hLeftCover : ∀ point, leftMask point ≠ 0 →
      point = a ∨ point ∈ left ∨ point ∈ accumulated)
    (hRightCover : ∀ point, rightMask point ≠ 0 →
      point = b ∨ point ∈ right ∨ point ∈ accumulated)
    (haLeft : a ∉ left) (haRight : a ∉ right)
    (haAccumulated : a ∉ accumulated)
    (hbLeft : b ∉ left) (hbRight : b ∉ right)
    (hbAccumulated : b ∉ accumulated)
    (hRank : ∀ point ∈ left, point ∈ right →
      threeMaskRank (leftMask point) + threeMaskRank (rightMask point) ≤ 4) :
    ∃ (actualOutput : List alpha) (output : List Nat),
      SixRowCouplingGeneratedAux
          (left.map leftMask) (right.map rightMask)
          (accumulated.map actualMask) output ∧
        actualOutput.Nodup ∧
        actualOutput.map actualMask = output := by
  induction left generalizing right accumulated with
  | nil =>
      have hLeftZero : ∀ point ∈ right, leftMask point = 0 := by
        intro point hPointRight
        by_contra hNonzero
        rcases hLeftCover point hNonzero with
          hPointA | hPointLeft | hPointAccumulated
        · subst point
          exact haRight hPointRight
        · simp at hPointLeft
        · exact List.disjoint_left.mp hRightAccumulated
            hPointRight hPointAccumulated
      have hActualRight :
          right.map actualMask =
            right.map (fun point ↦ sixShiftRightSupport (rightMask point)) := by
        apply List.map_congr_left
        intro point hPointRight
        have hPointNeA : point ≠ a := by
          intro hEqual
          subst point
          exact haRight hPointRight
        have hPointNeB : point ≠ b := by
          intro hEqual
          subst point
          exact hbRight hPointRight
        rw [hActualJoin point hPointNeA hPointNeB,
          hLeftZero point hPointRight]
        simp [sixJoinSupports, sixShiftRightSupport]
      have hTailNodup : (accumulated ++ right).Nodup :=
        hAccumulatedNodup.append hRightNodup hRightAccumulated.symm
      have hOutputNodup :
          (a :: b :: (accumulated ++ right)).Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.mem_append]
        constructor
        · intro hPoint
          rcases hPoint with hAB | hAccumulated | hRight
          · exact hab hAB
          · exact haAccumulated hAccumulated
          · exact haRight hRight
        constructor
        · intro hPoint
          rcases hPoint with hAccumulated | hRight
          · exact hbAccumulated hAccumulated
          · exact hbRight hRight
        · exact hTailNodup
      refine ⟨a :: b :: (accumulated ++ right),
        [7, 56] ++ accumulated.map actualMask ++
          (right.map rightMask).map sixShiftRightSupport,
        SixRowCouplingGeneratedAux.nil _ _, hOutputNodup, ?_⟩
      simp only [List.map_cons, List.map_append, hActualA, hActualB]
      rw [hActualRight]
      simp [List.map_map, Function.comp_def]
  | cons point left ih =>
      have hPointNotLeft : point ∉ left :=
        (List.nodup_cons.mp hLeftNodup).1
      have hLeftTailNodup : left.Nodup :=
        (List.nodup_cons.mp hLeftNodup).2
      have hPointNotAccumulated : point ∉ accumulated := by
        intro hPointAccumulated
        exact List.disjoint_left.mp hLeftAccumulated (by simp)
          hPointAccumulated
      have hAccumulated' : (point :: accumulated).Nodup :=
        List.nodup_cons.mpr ⟨hPointNotAccumulated, hAccumulatedNodup⟩
      have hLeftAccumulated' : List.Disjoint left (point :: accumulated) := by
        apply List.disjoint_left.mpr
        intro z hzLeft hzNew
        simp only [List.mem_cons] at hzNew
        rcases hzNew with rfl | hzAccumulated
        · exact hPointNotLeft hzLeft
        · exact List.disjoint_left.mp hLeftAccumulated
            (List.mem_cons_of_mem point hzLeft) hzAccumulated
      have hLeftCover' : ∀ z, leftMask z ≠ 0 →
          z = a ∨ z ∈ left ∨ z ∈ point :: accumulated := by
        intro z hzMask
        rcases hLeftCover z hzMask with hzA | hzLeft | hzAccumulated
        · exact Or.inl hzA
        · simp only [List.mem_cons] at hzLeft
          rcases hzLeft with rfl | hzTail
          · exact Or.inr (Or.inr (by simp))
          · exact Or.inr (Or.inl hzTail)
        · exact Or.inr
            (Or.inr (List.mem_cons_of_mem point hzAccumulated))
      have hPointNeA : point ≠ a := by
        intro hEqual
        subst point
        exact haLeft (by simp)
      have hPointNeB : point ≠ b := by
        intro hEqual
        subst point
        exact hbLeft (by simp)
      have haLeft' : a ∉ left := by
        intro hPoint
        exact haLeft (List.mem_cons_of_mem point hPoint)
      have hbLeft' : b ∉ left := by
        intro hPoint
        exact hbLeft (List.mem_cons_of_mem point hPoint)
      have haAccumulated' : a ∉ point :: accumulated := by
        intro hPoint
        simp only [List.mem_cons] at hPoint
        rcases hPoint with hEqual | hOld
        · exact hPointNeA hEqual.symm
        · exact haAccumulated hOld
      have hbAccumulated' : b ∉ point :: accumulated := by
        intro hPoint
        simp only [List.mem_cons] at hPoint
        rcases hPoint with hEqual | hOld
        · exact hPointNeB hEqual.symm
        · exact hbAccumulated hOld
      by_cases hPointRight : point ∈ right
      · have hRightTailNodup : (right.erase point).Nodup :=
          hRightNodup.erase point
        have hRightAccumulated' :
            List.Disjoint (right.erase point) (point :: accumulated) := by
          apply List.disjoint_left.mpr
          intro z hzRight hzNew
          have hzData := hRightNodup.mem_erase_iff.mp hzRight
          simp only [List.mem_cons] at hzNew
          rcases hzNew with rfl | hzAccumulated
          · exact hzData.1 rfl
          · exact List.disjoint_left.mp hRightAccumulated
              hzData.2 hzAccumulated
        have hRightCover' : ∀ z, rightMask z ≠ 0 →
            z = b ∨ z ∈ right.erase point ∨
              z ∈ point :: accumulated := by
          intro z hzMask
          rcases hRightCover z hzMask with hzB | hzRight | hzAccumulated
          · exact Or.inl hzB
          · by_cases hzPoint : z = point
            · subst z
              exact Or.inr (Or.inr (by simp))
            · exact Or.inr (Or.inl
                (hRightNodup.mem_erase_iff.mpr ⟨hzPoint, hzRight⟩))
          · exact Or.inr
              (Or.inr (List.mem_cons_of_mem point hzAccumulated))
        have haRight' : a ∉ right.erase point := by
          intro hPoint
          exact haRight (List.mem_of_mem_erase hPoint)
        have hbRight' : b ∉ right.erase point := by
          intro hPoint
          exact hbRight (List.mem_of_mem_erase hPoint)
        have hRank' : ∀ z ∈ left, z ∈ right.erase point →
            threeMaskRank (leftMask z) + threeMaskRank (rightMask z) ≤ 4 := by
          intro z hzLeft hzRight
          exact hRank z (List.mem_cons_of_mem point hzLeft)
            (List.mem_of_mem_erase hzRight)
        obtain ⟨actualOutput, output, hGenerated, hOutputNodup,
            hOutputMap⟩ :=
          ih (right := right.erase point) (accumulated := point :: accumulated)
            hLeftTailNodup hRightTailNodup hAccumulated'
            hLeftAccumulated' hRightAccumulated' hLeftCover' hRightCover'
            haLeft' haRight' haAccumulated' hbLeft' hbRight' hbAccumulated'
            hRank'
        let index := right.idxOf point
        have hIndex : index < (right.map rightMask).length := by
          simpa [index] using List.idxOf_lt_length_of_mem hPointRight
        have hGet :
            (right.map rightMask)[index]? = some (rightMask point) := by
          simp [index, List.getElem?_map, List.getElem?_idxOf hPointRight]
        have hEraseMap :
            (right.map rightMask).eraseIdx index =
              (right.erase point).map rightMask := by
          calc
            (right.map rightMask).eraseIdx index =
                (right.eraseIdx index).map rightMask :=
              List.eraseIdx_map rightMask right index
            _ = (right.erase point).map rightMask :=
              congrArg (List.map rightMask)
                (List.erase_eq_eraseIdx_of_idxOf
                  (l := right) (a := point) (i := index) rfl).symm
        have hActualPoint :
            actualMask point =
              sixJoinSupports (leftMask point) (rightMask point) :=
          hActualJoin point hPointNeA hPointNeB
        have hGenerated' :
            SixRowCouplingGeneratedAux
              (left.map leftMask)
              ((right.map rightMask).eraseIdx index)
              (sixJoinSupports (leftMask point) (rightMask point) ::
                accumulated.map actualMask) output := by
          rw [hEraseMap]
          simpa [hActualPoint] using hGenerated
        have hRankPoint :
            threeMaskRank (leftMask point) +
                threeMaskRank (rightMask point) ≤ 4 :=
          hRank point (by simp) hPointRight
        exact ⟨actualOutput, output,
          SixRowCouplingGeneratedAux.matched hIndex hGet hRankPoint hGenerated',
          hOutputNodup, hOutputMap⟩
      · have hRightPointZero : rightMask point = 0 := by
          by_contra hNonzero
          rcases hRightCover point hNonzero with
            hPointB | hRight | hAccumulated
          · exact hPointNeB hPointB
          · exact hPointRight hRight
          · exact hPointNotAccumulated hAccumulated
        have hActualPoint : actualMask point = leftMask point := by
          rw [hActualJoin point hPointNeA hPointNeB, hRightPointZero]
          simp [sixJoinSupports, sixShiftRightSupport]
        have hRightAccumulated' :
            List.Disjoint right (point :: accumulated) := by
          apply List.disjoint_left.mpr
          intro z hzRight hzNew
          simp only [List.mem_cons] at hzNew
          rcases hzNew with rfl | hzAccumulated
          · exact hPointRight hzRight
          · exact List.disjoint_left.mp hRightAccumulated
              hzRight hzAccumulated
        have hRightCover' : ∀ z, rightMask z ≠ 0 →
            z = b ∨ z ∈ right ∨ z ∈ point :: accumulated := by
          intro z hzMask
          rcases hRightCover z hzMask with hzB | hzRight | hzAccumulated
          · exact Or.inl hzB
          · exact Or.inr (Or.inl hzRight)
          · exact Or.inr
              (Or.inr (List.mem_cons_of_mem point hzAccumulated))
        have hRank' : ∀ z ∈ left, z ∈ right →
            threeMaskRank (leftMask z) + threeMaskRank (rightMask z) ≤ 4 := by
          intro z hzLeft hzRight
          exact hRank z (List.mem_cons_of_mem point hzLeft) hzRight
        obtain ⟨actualOutput, output, hGenerated, hOutputNodup,
            hOutputMap⟩ :=
          ih (right := right) (accumulated := point :: accumulated)
            hLeftTailNodup hRightNodup hAccumulated'
            hLeftAccumulated' hRightAccumulated' hLeftCover' hRightCover'
            haLeft' haRight haAccumulated' hbLeft' hbRight hbAccumulated'
            hRank'
        have hGenerated' :
            SixRowCouplingGeneratedAux
              (left.map leftMask) (right.map rightMask)
              (leftMask point :: accumulated.map actualMask) output := by
          simpa [hActualPoint] using hGenerated
        exact ⟨actualOutput, output,
          SixRowCouplingGeneratedAux.unmatched hGenerated',
          hOutputNodup, hOutputMap⟩

theorem actualCouplingMerge
    {alpha : Type*} [DecidableEq alpha]
    {a b : alpha}
    (actualMask leftMask rightMask : alpha → Nat)
    {left right : List alpha}
    (hab : a ≠ b)
    (hActualA : actualMask a = 7)
    (hActualB : actualMask b = 56)
    (hActualJoin : ∀ point, point ≠ a → point ≠ b →
      actualMask point = sixJoinSupports (leftMask point) (rightMask point))
    (hLeftNodup : left.Nodup) (hRightNodup : right.Nodup)
    (hLeftCover : ∀ point, leftMask point ≠ 0 →
      point = a ∨ point ∈ left)
    (hRightCover : ∀ point, rightMask point ≠ 0 →
      point = b ∨ point ∈ right)
    (haLeft : a ∉ left) (haRight : a ∉ right)
    (hbLeft : b ∉ left) (hbRight : b ∉ right)
    (hRank : ∀ point ∈ left, point ∈ right →
      threeMaskRank (leftMask point) + threeMaskRank (rightMask point) ≤ 4) :
    ∃ (actualOutput : List alpha) (output : List Nat),
      SixRowCouplingGeneratedAux
          (left.map leftMask) (right.map rightMask) [] output ∧
        actualOutput.Nodup ∧ actualOutput.map actualMask = output := by
  apply actualCouplingMergeAux (accumulated := []) actualMask leftMask rightMask
    hab hActualA hActualB hActualJoin hLeftNodup hRightNodup
    (by simp) (by simp) (by simp)
  · intro point hPoint
    rcases hLeftCover point hPoint with rfl | hLeft
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hLeft)
  · intro point hPoint
    rcases hRightCover point hPoint with rfl | hRight
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hRight)
  · exact haLeft
  · exact haRight
  · simp
  · exact hbLeft
  · exact hbRight
  · simp
  · exact hRank

theorem actualCouplingMerge_profiles
    {alpha : Type*} [DecidableEq alpha]
    {a b : alpha}
    (actualMask leftMask rightMask : alpha → Nat)
    {left right : List alpha} {leftProfile rightProfile : List Nat}
    (hLeftProfile : left.map leftMask = leftProfile ++ [7])
    (hRightProfile : right.map rightMask = rightProfile ++ [7])
    (hab : a ≠ b)
    (hActualA : actualMask a = 7)
    (hActualB : actualMask b = 56)
    (hActualJoin : ∀ point, point ≠ a → point ≠ b →
      actualMask point = sixJoinSupports (leftMask point) (rightMask point))
    (hLeftNodup : left.Nodup) (hRightNodup : right.Nodup)
    (hLeftCover : ∀ point, leftMask point ≠ 0 →
      point = a ∨ point ∈ left)
    (hRightCover : ∀ point, rightMask point ≠ 0 →
      point = b ∨ point ∈ right)
    (haLeft : a ∉ left) (haRight : a ∉ right)
    (hbLeft : b ∉ left) (hbRight : b ∉ right)
    (hRank : ∀ point ∈ left, point ∈ right →
      threeMaskRank (leftMask point) + threeMaskRank (rightMask point) ≤ 4) :
    ∃ (actualOutput : List alpha) (output : List Nat),
      SixRowCouplingGenerated leftProfile rightProfile output ∧
        actualOutput.Nodup ∧ actualOutput.map actualMask = output := by
  obtain ⟨actualOutput, output, hGenerated, hOutputNodup, hOutputMap⟩ :=
    actualCouplingMerge actualMask leftMask rightMask hab
      hActualA hActualB hActualJoin hLeftNodup hRightNodup
      hLeftCover hRightCover haLeft haRight hbLeft hbRight hRank
  refine ⟨actualOutput, output, ?_, hOutputNodup, hOutputMap⟩
  unfold SixRowCouplingGenerated
  rw [← hLeftProfile, ← hRightProfile]
  exact hGenerated

def sixActualSupportMask
    {alpha : Type*} [DecidableEq alpha]
    (L0 L1 L2 R0 R1 R2 : Row alpha) (point : alpha) : Nat :=
  sixJoinSupports (threeSupportMask L0 L1 L2 point)
    (threeSupportMask R0 R1 R2 point)

theorem sixActualSupportMask_bits
    {alpha : Type*} [DecidableEq alpha]
    (L0 L1 L2 R0 R1 R2 : Row alpha) (point : alpha) :
    (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 0 =
        decide (point ∈ L0) ∧
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 1 =
        decide (point ∈ L1) ∧
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 2 =
        decide (point ∈ L2) ∧
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 3 =
        decide (point ∈ R0) ∧
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 4 =
        decide (point ∈ R1) ∧
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 point).testBit 5 =
        decide (point ∈ R2) := by
  by_cases hL0 : point ∈ L0 <;>
    by_cases hL1 : point ∈ L1 <;>
    by_cases hL2 : point ∈ L2 <;>
    by_cases hR0 : point ∈ R0 <;>
    by_cases hR1 : point ∈ R1 <;>
    by_cases hR2 : point ∈ R2 <;>
    simp [sixActualSupportMask, sixJoinSupports, sixShiftRightSupport,
      threeSupportMask, hL0, hL1, hL2, hR0, hR1, hR2] <;>
    decide

theorem hit_of_full_lor_bit
    {left right bit : Nat} {P Q : Prop} [Decidable P] [Decidable Q]
    (hLeft : left.testBit bit = decide P)
    (hRight : right.testBit bit = decide Q)
    (hFull : Nat.lor left right = 63)
    (hFullBit : (63 : Nat).testBit bit = true) :
    P ∨ Q := by
  have hBit := congrArg (fun value : Nat ↦ value.testBit bit) hFull
  rw [Nat.lor_eq, Nat.testBit_lor left right bit,
    hLeft, hRight, hFullBit] at hBit
  have hOr : decide P || decide Q = true := by simpa using hBit
  by_cases hP : P
  · exact Or.inl hP
  by_cases hQ : Q
  · exact Or.inr hQ
  simp [hP, hQ] at hOr

theorem sixActualSupportMask_lor_transversal
    {alpha : Type*} [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {L0 L1 L2 R0 R1 R2 : Row alpha}
    {x y : alpha}
    (hK : K = {L0, L1, L2, R0, R1, R2})
    (hFull : Nat.lor
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 x)
      (sixActualSupportMask L0 L1 L2 R0 R1 R2 y) = 63) :
    IsTransversal K ({x, y} : Row alpha) := by
  let left := sixActualSupportMask L0 L1 L2 R0 R1 R2 x
  let right := sixActualSupportMask L0 L1 L2 R0 R1 R2 y
  have hX := sixActualSupportMask_bits L0 L1 L2 R0 R1 R2 x
  have hY := sixActualSupportMask_bits L0 L1 L2 R0 R1 R2 y
  have hFull' : Nat.lor left right = 63 := by simpa [left, right] using hFull
  have hHitL0 : x ∈ L0 ∨ y ∈ L0 :=
    hit_of_full_lor_bit hX.1 hY.1 hFull' (by decide)
  have hHitL1 : x ∈ L1 ∨ y ∈ L1 :=
    hit_of_full_lor_bit hX.2.1 hY.2.1 hFull' (by decide)
  have hHitL2 : x ∈ L2 ∨ y ∈ L2 :=
    hit_of_full_lor_bit hX.2.2.1 hY.2.2.1 hFull' (by decide)
  have hHitR0 : x ∈ R0 ∨ y ∈ R0 :=
    hit_of_full_lor_bit hX.2.2.2.1 hY.2.2.2.1 hFull' (by decide)
  have hHitR1 : x ∈ R1 ∨ y ∈ R1 :=
    hit_of_full_lor_bit hX.2.2.2.2.1 hY.2.2.2.2.1 hFull' (by decide)
  have hHitR2 : x ∈ R2 ∨ y ∈ R2 :=
    hit_of_full_lor_bit hX.2.2.2.2.2 hY.2.2.2.2.2 hFull' (by decide)
  have pair_hits (R : Row alpha) (hHit : x ∈ R ∨ y ∈ R) :
      ∃ point ∈ ({x, y} : Row alpha), point ∈ R := by
    rcases hHit with hxR | hyR
    · exact ⟨x, by simp, hxR⟩
    · exact ⟨y, by simp, hyR⟩
  intro R hRK
  rw [hK] at hRK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
  rcases hRK with hRL0 | hRL1 | hRL2 | hRR0 | hRR1 | hRR2
  · exact pair_hits R (hRL0.symm ▸ hHitL0)
  · exact pair_hits R (hRL1.symm ▸ hHitL1)
  · exact pair_hits R (hRL2.symm ▸ hHitL2)
  · exact pair_hits R (hRR0.symm ▸ hHitR0)
  · exact pair_hits R (hRR1.symm ▸ hHitR1)
  · exact pair_hits R (hRR2.symm ▸ hHitR2)

def sixActualCoverPairList
    {alpha : Type*} (fullMask : alpha → Nat) :
    List alpha → List (Sym2 alpha)
  | [] => []
  | point :: points =>
      ((points.filter fun other ↦
          Nat.lor (fullMask point) (fullMask other) = 63).map
        fun other ↦ s(point, other)) ++
      sixActualCoverPairList fullMask points

theorem sixActualCoverPairList_length
    {alpha : Type*} (fullMask : alpha → Nat) (points : List alpha) :
    (sixActualCoverPairList fullMask points).length =
      sixPairCoverCount (points.map fullMask) := by
  induction points with
  | nil => rfl
  | cons point points ih =>
      simp [sixActualCoverPairList, sixPairCoverCount, ih,
        List.filter_map, Function.comp_def]

theorem sixActualCoverPairList_sublist_sym2
    {alpha : Type*} (fullMask : alpha → Nat) (points : List alpha) :
    List.Sublist (sixActualCoverPairList fullMask points) points.sym2 := by
  induction points with
  | nil => exact List.Sublist.slnil
  | cons point points ih =>
      let predicate := fun other ↦
        Nat.lor (fullMask point) (fullMask other) = 63
      let pairWithPoint := fun other ↦ s(point, other)
      have hFiltered :
          List.Sublist ((points.filter predicate).map pairWithPoint)
            (points.map pairWithPoint) :=
        List.Sublist.map pairWithPoint List.filter_sublist
      have hHead :
          List.Sublist ((points.filter predicate).map pairWithPoint)
            ((point :: points).map pairWithPoint) :=
        hFiltered.cons (pairWithPoint point)
      simpa [sixActualCoverPairList, List.sym2, predicate, pairWithPoint] using
        List.Sublist.append hHead ih

theorem sixActualCoverPairList_nodup
    {alpha : Type*} (fullMask : alpha → Nat) {points : List alpha}
    (hNodup : points.Nodup) :
    (sixActualCoverPairList fullMask points).Nodup :=
  List.Nodup.sublist
    (sixActualCoverPairList_sublist_sym2 fullMask points) hNodup.sym2

theorem mem_sixActualCoverPairList_data
    {alpha : Type*} (fullMask : alpha → Nat)
    {points : List alpha} {pair : Sym2 alpha}
    (hNodup : points.Nodup)
    (hPair : pair ∈ sixActualCoverPairList fullMask points) :
    ∃ x y, x ≠ y ∧ pair = s(x, y) ∧
      Nat.lor (fullMask x) (fullMask y) = 63 := by
  induction points with
  | nil => simp [sixActualCoverPairList] at hPair
  | cons point points ih =>
      have hPointNot : point ∉ points :=
        (List.nodup_cons.mp hNodup).1
      have hPointsNodup : points.Nodup :=
        (List.nodup_cons.mp hNodup).2
      simp only [sixActualCoverPairList, List.mem_append] at hPair
      rcases hPair with hHead | hTail
      · obtain ⟨other, hOther, hPairEq⟩ := List.mem_map.mp hHead
        obtain ⟨hOtherPoints, hFull⟩ := List.mem_filter.mp hOther
        refine ⟨point, other, ?_, hPairEq.symm, ?_⟩
        · intro hEqual
          subst other
          exact hPointNot hOtherPoints
        · simpa using hFull
      · exact ih hPointsNodup hTail

theorem sym2_toFinset_injective
    {alpha : Type*} [DecidableEq alpha] :
    Function.Injective (fun pair : Sym2 alpha ↦ pair.toFinset) := by
  intro left right hEqual
  change left.toFinset = right.toFinset at hEqual
  apply Sym2.ext
  intro point
  constructor
  · intro hPoint
    have hLeft : point ∈ left.toFinset := Sym2.mem_toFinset.mpr hPoint
    have hRight : point ∈ right.toFinset := by
      rw [← hEqual]
      exact hLeft
    exact Sym2.mem_toFinset.mp hRight
  · intro hPoint
    have hRight : point ∈ right.toFinset := Sym2.mem_toFinset.mpr hPoint
    have hLeft : point ∈ left.toFinset := by
      rw [hEqual]
      exact hRight
    exact Sym2.mem_toFinset.mp hLeft

theorem sixPairCoverCount_le_pairRows_of_actual
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {fullMask : alpha → Nat}
    {actualPoints : List alpha} {output : List Nat}
    (hNodup : actualPoints.Nodup)
    (hOutput : actualPoints.map fullMask = output)
    (hLorTransversal : ∀ x y,
      Nat.lor (fullMask x) (fullMask y) = 63 →
        IsTransversal K ({x, y} : Row alpha))
    (hBlockerRows : RowsCardAtLeast (blocker K) 2) :
    sixPairCoverCount output ≤ (pairRows (blocker K)).card := by
  classical
  let coverPairs := sixActualCoverPairList fullMask actualPoints
  let actualPairs : G413.Hypergraph alpha :=
    coverPairs.toFinset.image fun pair ↦ pair.toFinset
  have hCoverNodup : coverPairs.Nodup := by
    simpa [coverPairs] using sixActualCoverPairList_nodup fullMask hNodup
  have hActualPairsCard : actualPairs.card = coverPairs.length := by
    calc
      actualPairs.card = coverPairs.toFinset.card := by
        apply Finset.card_image_iff.mpr
        exact sym2_toFinset_injective.injOn
      _ = coverPairs.length := List.toFinset_card_of_nodup hCoverNodup
  have hActualPairsSubset : actualPairs ⊆ pairRows (blocker K) := by
    intro Q hQ
    obtain ⟨pair, hPair, hPairQ⟩ := Finset.mem_image.mp hQ
    have hPairList : pair ∈ coverPairs := List.mem_toFinset.mp hPair
    obtain ⟨x, y, hxy, hPairEq, hFull⟩ :=
      mem_sixActualCoverPairList_data fullMask hNodup (by
        simpa [coverPairs] using hPairList)
    have hPairBlocker : ({x, y} : Row alpha) ∈ blocker K :=
      pair_mem_blocker_of_transversal hBlockerRows
        (hLorTransversal x y hFull)
    have hPairRow : ({x, y} : Row alpha) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPairBlocker, Finset.card_pair hxy⟩
    rw [hPairEq, Sym2.toFinset_mk_eq] at hPairQ
    rw [← hPairQ]
    exact hPairRow
  have hCoverLength :
      coverPairs.length = sixPairCoverCount output := by
    have hLength := sixActualCoverPairList_length fullMask actualPoints
    rw [hOutput] at hLength
    simpa [coverPairs] using hLength
  calc
    sixPairCoverCount output = actualPairs.card := by
      rw [← hCoverLength, hActualPairsCard]
    _ ≤ (pairRows (blocker K)).card :=
      Finset.card_le_card hActualPairsSubset

end AiMathLab.P0054.MiddleSevenNineSixCouplingSound
