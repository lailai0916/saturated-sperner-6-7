import AiMathLab.P0054MiddleSevenNineSixCouplingSound
import AiMathLab.P0054MiddleSevenNineSixResidualSound

/-!
# Applying the six-row coupling certificate to an actual finite kernel
-/

namespace AiMathLab.P0054.MiddleSevenNineSixCouplingActual

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.MiddleSevenNineSixResidualSound
open AiMathLab.P0054.MiddleSevenNineThreeResidualRealization
open AiMathLab.P0054.MiddleSevenNineSixCouplingFinite
open AiMathLab.P0054.MiddleSevenNineSixCouplingSound

theorem sixRow_kernel_coupling_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hEMax : MaxDegreeAtMost E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) : False := by
  classical
  obtain ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, hData⟩ :=
    sixRow_kernel_residual_marginal_data hEClutter hECard hERows hEMax
      hDualCard hDualRows hDualMax hTBlocker hTCard hTMax
  let K := avoidPoint E x
  let aSide := pointSupport K a
  let bSide := pointSupport K b
  let aCentered := deletePoint aSide a
  let bCentered := deletePoint bSide b
  let aResidual := deletePoint aCentered c
  let bResidual := deletePoint bCentered d
  have hCore :
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        MaxDegreeAtMost K 4 ∧ RowsCardAtLeast (blocker K) 2 ∧
        (blocker K).card ≤ 7 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        aSide = avoidPoint K b ∧ bSide = avoidPoint K a ∧
        (∀ R ∈ aSide, a ∈ R) ∧ (∀ R ∈ bSide, b ∈ R) ∧
        (∀ R ∈ aCentered, c ∈ R) ∧
        (∀ R ∈ bCentered, d ∈ R) ∧
        pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} ∧
        (pairRows (blocker K)).card = 3 ∧
        c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d ∧
        IsClutter aResidual ∧ aResidual.card = 3 ∧
        RowsCardAtLeast aResidual 2 ∧
        (∀ R ∈ aResidual, R.card ≤ 5) ∧
        (∀ point, ∃ R ∈ aResidual, point ∉ R) ∧
        (blocker aResidual).card ≤ 4 ∧
        IsClutter bResidual ∧ bResidual.card = 3 ∧
        RowsCardAtLeast bResidual 2 ∧
        (∀ R ∈ bResidual, R.card ≤ 5) ∧
        (∀ point, ∃ R ∈ bResidual, point ∉ R) ∧
        (blocker bResidual).card ≤ 4 := by
    simpa [K, aSide, bSide, aCentered, bCentered, aResidual, bResidual]
      using hData
  rcases hCore with
    ⟨hKClutter, hKCard, hKRows, hKMax, hBKRows, hBKUpper,
      hASideCard, hBSideCard, hCover, hDisjoint, hASideAvoid,
      hBSideAvoid, hACenter, hBCenter, hcCommon, hdCommon,
      hPairRowsEq, hPairRowsCard, hcNeA, hcNeB, hdNeA, hdNeB, hcNeD,
      hAResidualClutter, hAResidualCard, hAResidualRows,
      hAResidualUpper, hAResidualNoCommon, hABlockerUpper,
      hBResidualClutter, hBResidualCard, hBResidualRows,
      hBResidualUpper, hBResidualNoCommon, hBBlockerUpper⟩
  obtain ⟨LA, LB, LC, leftIndex, leftPoints,
      hLAB, hLAC, hLBC, hAResidualRowsEq, hLeftIndex,
      hLeftPointsNodup, hLeftPoints, hLeftProfile⟩ :=
    threeRow_residual_actual_profile hAResidualClutter hAResidualCard
      hAResidualRows hAResidualUpper hAResidualNoCommon hABlockerUpper
  obtain ⟨RA, RB, RC, rightIndex, rightPoints,
      hRAB, hRAC, hRBC, hBResidualRowsEq, hRightIndex,
      hRightPointsNodup, hRightPoints, hRightProfile⟩ :=
    threeRow_residual_actual_profile hBResidualClutter hBResidualCard
      hBResidualRows hBResidualUpper hBResidualNoCommon hBBlockerUpper
  have hASideLifted : aSide = threeLiftedRows a c LA LB LC := by
    apply threeLiftedRows_eq_of_doubleDelete
      (H := aSide) (residual := aResidual)
    · rfl
    · exact hAResidualRowsEq
    · exact hACenter
    · simpa [aCentered] using hcCommon
  have hBSideLifted : bSide = threeLiftedRows b d RA RB RC := by
    apply threeLiftedRows_eq_of_doubleDelete
      (H := bSide) (residual := bResidual)
    · rfl
    · exact hBResidualRowsEq
    · exact hBCenter
    · simpa [bCentered] using hdCommon
  have hASideAvoidsB : ∀ R ∈ aSide, b ∉ R := by
    intro R hR
    have hRAvoid : R ∈ avoidPoint K b := by
      rw [← hASideAvoid]
      exact hR
    exact (mem_avoidPoint.mp hRAvoid).2
  have hBSideAvoidsA : ∀ R ∈ bSide, a ∉ R := by
    intro R hR
    have hRAvoid : R ∈ avoidPoint K a := by
      rw [← hBSideAvoid]
      exact hR
    exact (mem_avoidPoint.mp hRAvoid).2
  have hAResidualAvoidA : ∀ R ∈ aResidual, a ∉ R := by
    intro R hR
    exact doubleDelete_rows_avoid_first
      (H := aSide) (first := a) (second := c)
      (by simpa [aResidual, aCentered] using hR)
  have hAResidualAvoidB : ∀ R ∈ aResidual, b ∉ R := by
    intro R hR
    exact doubleDelete_rows_avoid_external hASideAvoidsB
      (H := aSide) (first := a) (second := c)
      (by simpa [aResidual, aCentered] using hR)
  have hAResidualAvoidC : ∀ R ∈ aResidual, c ∉ R := by
    intro R hR
    exact deletePoint_rows_avoid (by simpa [aResidual] using hR)
  have hBResidualAvoidA : ∀ R ∈ bResidual, a ∉ R := by
    intro R hR
    exact doubleDelete_rows_avoid_external hBSideAvoidsA
      (H := bSide) (first := b) (second := d)
      (by simpa [bResidual, bCentered] using hR)
  have hBResidualAvoidB : ∀ R ∈ bResidual, b ∉ R := by
    intro R hR
    exact doubleDelete_rows_avoid_first
      (H := bSide) (first := b) (second := d)
      (by simpa [bResidual, bCentered] using hR)
  have hBResidualAvoidD : ∀ R ∈ bResidual, d ∉ R := by
    intro R hR
    exact deletePoint_rows_avoid (by simpa [bResidual] using hR)
  have haNotLeftPoints : a ∉ leftPoints :=
    point_not_mem_of_actual_points_avoid hLeftPoints hAResidualAvoidA
  have hbNotLeftPoints : b ∉ leftPoints :=
    point_not_mem_of_actual_points_avoid hLeftPoints hAResidualAvoidB
  have hcNotLeftPoints : c ∉ leftPoints :=
    point_not_mem_of_actual_points_avoid hLeftPoints hAResidualAvoidC
  have haNotRightPoints : a ∉ rightPoints :=
    point_not_mem_of_actual_points_avoid hRightPoints hBResidualAvoidA
  have hbNotRightPoints : b ∉ rightPoints :=
    point_not_mem_of_actual_points_avoid hRightPoints hBResidualAvoidB
  have hdNotRightPoints : d ∉ rightPoints :=
    point_not_mem_of_actual_points_avoid hRightPoints hBResidualAvoidD
  let leftList := leftPoints ++ [c]
  let rightList := rightPoints ++ [d]
  let leftMask := threeLiftedSupportMask a c LA LB LC
  let rightMask := threeLiftedSupportMask b d RA RB RC
  have hLeftListNodup : leftList.Nodup := by
    simpa [leftList] using
      nodup_append_singleton hLeftPointsNodup hcNotLeftPoints
  have hRightListNodup : rightList.Nodup := by
    simpa [rightList] using
      nodup_append_singleton hRightPointsNodup hdNotRightPoints
  have hLeftMap :
      leftList.map leftMask = sixResidualProfile leftIndex ++ [7] := by
    simpa [leftList, leftMask] using
      map_threeLiftedSupportMask_append_common
        (center := a) (common := c) (A := LA) (B := LB) (C := LC)
        (fun point hPoint hEqual ↦ haNotLeftPoints (hEqual ▸ hPoint))
        (fun point hPoint hEqual ↦ hcNotLeftPoints (hEqual ▸ hPoint))
        hLeftProfile
  have hRightMap :
      rightList.map rightMask = sixResidualProfile rightIndex ++ [7] := by
    simpa [rightList, rightMask] using
      map_threeLiftedSupportMask_append_common
        (center := b) (common := d) (A := RA) (B := RB) (C := RC)
        (fun point hPoint hEqual ↦ hbNotRightPoints (hEqual ▸ hPoint))
        (fun point hPoint hEqual ↦ hdNotRightPoints (hEqual ▸ hPoint))
        hRightProfile
  have haNotLeftList : a ∉ leftList := by
    intro hPoint
    simp only [leftList, List.mem_append, List.mem_singleton] at hPoint
    rcases hPoint with hPoint | hEqual
    · exact haNotLeftPoints hPoint
    · exact hcNeA hEqual.symm
  have hbNotLeftList : b ∉ leftList := by
    intro hPoint
    simp only [leftList, List.mem_append, List.mem_singleton] at hPoint
    rcases hPoint with hPoint | hEqual
    · exact hbNotLeftPoints hPoint
    · exact hcNeB hEqual.symm
  have haNotRightList : a ∉ rightList := by
    intro hPoint
    simp only [rightList, List.mem_append, List.mem_singleton] at hPoint
    rcases hPoint with hPoint | hEqual
    · exact haNotRightPoints hPoint
    · exact hdNeA hEqual.symm
  have hbNotRightList : b ∉ rightList := by
    intro hPoint
    simp only [rightList, List.mem_append, List.mem_singleton] at hPoint
    rcases hPoint with hPoint | hEqual
    · exact hbNotRightPoints hPoint
    · exact hdNeB hEqual.symm
  let L0 := doubleDeletedRowLift a c LA
  let L1 := doubleDeletedRowLift a c LB
  let L2 := doubleDeletedRowLift a c LC
  let R0 := doubleDeletedRowLift b d RA
  let R1 := doubleDeletedRowLift b d RB
  let R2 := doubleDeletedRowLift b d RC
  have hKLiteral : K = {L0, L1, L2, R0, R1, R2} := by
    rw [← hCover, hASideLifted, hBSideLifted]
    ext R
    simp [threeLiftedRows, L0, L1, L2, R0, R1, R2,
      or_comm, or_left_comm, or_assoc]
  have haRA : a ∉ RA :=
    hBResidualAvoidA RA (by simp [hBResidualRowsEq])
  have haRB : a ∉ RB :=
    hBResidualAvoidA RB (by simp [hBResidualRowsEq])
  have haRC : a ∉ RC :=
    hBResidualAvoidA RC (by simp [hBResidualRowsEq])
  have hbLA : b ∉ LA :=
    hAResidualAvoidB LA (by simp [hAResidualRowsEq])
  have hbLB : b ∉ LB :=
    hAResidualAvoidB LB (by simp [hAResidualRowsEq])
  have hbLC : b ∉ LC :=
    hAResidualAvoidB LC (by simp [hAResidualRowsEq])
  let fullMask := sixActualSupportMask L0 L1 L2 R0 R1 R2
  have hLeftMaskRows (point : alpha) :
      leftMask point = threeSupportMask L0 L1 L2 point := by
    simpa [leftMask, L0, L1, L2] using
      threeLiftedSupportMask_eq a c LA LB LC point
  have hRightMaskRows (point : alpha) :
      rightMask point = threeSupportMask R0 R1 R2 point := by
    simpa [rightMask, R0, R1, R2] using
      threeLiftedSupportMask_eq b d RA RB RC point
  have hFullJoin (point : alpha) :
      fullMask point =
        sixJoinSupports (leftMask point) (rightMask point) := by
    change sixJoinSupports
        (threeSupportMask L0 L1 L2 point)
        (threeSupportMask R0 R1 R2 point) = _
    rw [← hLeftMaskRows point, ← hRightMaskRows point]
  have hRightMaskA : rightMask a = 0 := by
    simpa [rightMask] using
      threeLiftedSupportMask_eq_zero_of_avoids
        (center := b) (common := d) (point := a)
        hab hdNeA.symm haRA haRB haRC
  have hLeftMaskB : leftMask b = 0 := by
    simpa [leftMask] using
      threeLiftedSupportMask_eq_zero_of_avoids
        (center := a) (common := c) (point := b)
        hab.symm hcNeB.symm hbLA hbLB hbLC
  have hLeftMaskA : leftMask a = 7 := by
    simp [leftMask, threeLiftedSupportMask]
  have hRightMaskB : rightMask b = 7 := by
    simp [rightMask, threeLiftedSupportMask]
  have hFullA : fullMask a = 7 := by
    rw [hFullJoin, hLeftMaskA, hRightMaskA]
    decide
  have hFullB : fullMask b = 56 := by
    rw [hFullJoin, hLeftMaskB, hRightMaskB]
    decide
  have hLeftCover : ∀ point, leftMask point ≠ 0 →
      point = a ∨ point ∈ leftList := by
    intro point hNonzero
    simpa [leftMask, leftList] using
      threeLiftedSupportMask_cover hAResidualRowsEq hLeftPoints hNonzero
  have hRightCover : ∀ point, rightMask point ≠ 0 →
      point = b ∨ point ∈ rightList := by
    intro point hNonzero
    simpa [rightMask, rightList] using
      threeLiftedSupportMask_cover hBResidualRowsEq hRightPoints hNonzero
  have hLeftRank (point : alpha) :
      threeMaskRank (leftMask point) = degree aSide point := by
    simpa [leftMask] using
      threeLiftedSupportMask_rank_eq_degree
        (side := aSide) (center := a) (common := c)
        (A := LA) (B := LB) (C := LC) (point := point)
        hASideLifted hASideCard
  have hRightRank (point : alpha) :
      threeMaskRank (rightMask point) = degree bSide point := by
    simpa [rightMask] using
      threeLiftedSupportMask_rank_eq_degree
        (side := bSide) (center := b) (common := d)
        (A := RA) (B := RB) (C := RC) (point := point)
        hBSideLifted hBSideCard
  have hRank : ∀ point ∈ leftList, point ∈ rightList →
      threeMaskRank (leftMask point) + threeMaskRank (rightMask point) ≤ 4 := by
    intro point _hPointLeft _hPointRight
    have hDegree := degree_add_eq_of_union_disjoint hCover hDisjoint point
    have hMax := hKMax point
    rw [hLeftRank point, hRightRank point]
    omega
  obtain ⟨actualOutput, output, hGenerated, hOutputNodup, hOutputMap⟩ :=
    actualCouplingMerge_profiles
      (a := a) (b := b) fullMask leftMask rightMask
      hLeftMap hRightMap hab hFullA hFullB
      (fun point _hPointA _hPointB ↦ hFullJoin point)
      hLeftListNodup hRightListNodup hLeftCover hRightCover
      haNotLeftList haNotRightList hbNotLeftList hbNotRightList hRank
  have hCheck :
      sixRowCouplingCheck (sixResidualProfile leftIndex)
          (sixResidualProfile rightIndex) = true := by
    have hAll := six_row_coupling_certificate_check
    unfold sixRowCouplingCertificateCheck at hAll
    have hLeftCheck := List.all_eq_true.mp hAll leftIndex
      (List.mem_range.mpr hLeftIndex)
    exact List.all_eq_true.mp hLeftCheck rightIndex
      (List.mem_range.mpr hRightIndex)
  have hCountLower : 4 ≤ sixPairCoverCount output :=
    sixRowCouplingCheck_sound hGenerated hCheck
  have hLorTransversal : ∀ p q,
      Nat.lor (fullMask p) (fullMask q) = 63 →
        IsTransversal K ({p, q} : Row alpha) := by
    intro p q hFull
    apply sixActualSupportMask_lor_transversal hKLiteral
    simpa [fullMask] using hFull
  have hCountUpper :
      sixPairCoverCount output ≤ (pairRows (blocker K)).card :=
    sixPairCoverCount_le_pairRows_of_actual
      hOutputNodup hOutputMap hLorTransversal hBKRows
  rw [hPairRowsCard] at hCountUpper
  omega

end AiMathLab.P0054.MiddleSevenNineSixCouplingActual
