import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

def fourKernelMatchedRows (a b c u v w : FourPoint) : Nat :=
  (if fourTriplePointCover a u v then 1 else 0) +
    (if fourTriplePointCover b u w then 1 else 0) +
      (if fourTriplePointCover c v w then 1 else 0)

def fourKernelOrderedCompatibleExact
    (m : FourMultiplicity) (outside : List FourPoint) (a b c : FourPoint) : Bool :=
  outside.any fun u =>
    outside.any fun v =>
      decide (v ≠ u) &&
        outside.any fun w =>
          decide (w ≠ u ∧ w ≠ v) &&
            decide (fourWeightedCoverCount m ≤ fourKernelMatchedRows a b c u v w + 3)

def fourKernelCompatibleExact (m : FourMultiplicity) : Bool :=
  let points := fourActivePoints m
  (List.range 4).any fun row =>
    let rowPoints := points.filter fun point => fourSupportContains point.1 row
    decide (rowPoints.length = 3) &&
      match rowPoints with
      | [p, q, r] =>
          let outside := points.filter fun point => !fourSupportContains point.1 row
          fourKernelOrderedCompatibleExact m outside p q r ||
            fourKernelOrderedCompatibleExact m outside p r q ||
              fourKernelOrderedCompatibleExact m outside q p r ||
                fourKernelOrderedCompatibleExact m outside q r p ||
                  fourKernelOrderedCompatibleExact m outside r p q ||
                    fourKernelOrderedCompatibleExact m outside r q p
      | _ => false

def fourKernelAExclusionCheck (values : List Nat) : Bool :=
  !fourKernelCompatibleExact values.toArray

theorem fourKernelOrderedCompatibleExact_of_threshold
    (m : FourMultiplicity) (outside : List FourPoint) (a b c u v w : FourPoint)
    (hu : u ∈ outside) (hv : v ∈ outside) (hw : w ∈ outside)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hThreshold :
      fourWeightedCoverCount m ≤ fourKernelMatchedRows a b c u v w + 3) :
    fourKernelOrderedCompatibleExact m outside a b c = true := by
  unfold fourKernelOrderedCompatibleExact
  apply List.any_eq_true.mpr
  refine ⟨u, hu, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨v, hv, Bool.and_eq_true_iff.mpr ⟨decide_eq_true huv.symm, ?_⟩⟩
  apply List.any_eq_true.mpr
  refine ⟨w, hw, Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨huw.symm, hvw.symm⟩, ?_⟩⟩
  exact decide_eq_true hThreshold

theorem fourKernelOrderedCompatibleExact_of_witness
    (m : FourMultiplicity) (outside : List FourPoint) (a b c u v w : FourPoint)
    (hu : u ∈ outside) (hv : v ∈ outside) (hw : w ∈ outside)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA : fourTriplePointCover a u v = true)
    (hB : fourTriplePointCover b u w = true)
    (hC : fourTriplePointCover c v w = true)
    (hWeighted : fourWeightedCoverCount m ≤ 6) :
    fourKernelOrderedCompatibleExact m outside a b c = true := by
  apply fourKernelOrderedCompatibleExact_of_threshold m outside a b c u v w
    hu hv hw huv huw hvw
  simpa [fourKernelMatchedRows, hA, hB, hC] using hWeighted

theorem three_distinct_members_order_cases {α : Type*} [DecidableEq α]
    {p q r a b c : α}
    (ha : a ∈ [p, q, r]) (hb : b ∈ [p, q, r]) (hc : c ∈ [p, q, r])
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (p = a ∧ q = b ∧ r = c) ∨
      (p = a ∧ q = c ∧ r = b) ∨
        (p = b ∧ q = a ∧ r = c) ∨
          (p = b ∧ q = c ∧ r = a) ∨
            (p = c ∧ q = a ∧ r = b) ∨
              (p = c ∧ q = b ∧ r = a) := by
  simp only [List.mem_cons] at ha hb hc
  aesop

theorem fourKernelCompatibleExact_of_threshold_witness
    (m : FourMultiplicity) (row : Nat) (a b c u v w : FourPoint)
    (hrow : row < 4)
    (hRowLength :
      ((fourActivePoints m).filter fun point =>
        fourSupportContains point.1 row).length = 3)
    (ha : a ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hb : b ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hc : c ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu : u ∈ fourActivePoints m) (hv : v ∈ fourActivePoints m)
    (hw : w ∈ fourActivePoints m)
    (huRow : fourSupportContains u.1 row = false)
    (hvRow : fourSupportContains v.1 row = false)
    (hwRow : fourSupportContains w.1 row = false)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hThreshold :
      fourWeightedCoverCount m ≤ fourKernelMatchedRows a b c u v w + 3) :
    fourKernelCompatibleExact m = true := by
  let points := fourActivePoints m
  let rowPoints := points.filter fun point => fourSupportContains point.1 row
  let outside := points.filter fun point => !fourSupportContains point.1 row
  have hOutsideU : u ∈ outside := by
    exact List.mem_filter.mpr ⟨hu, by simp [huRow]⟩
  have hOutsideV : v ∈ outside := by
    exact List.mem_filter.mpr ⟨hv, by simp [hvRow]⟩
  have hOutsideW : w ∈ outside := by
    exact List.mem_filter.mpr ⟨hw, by simp [hwRow]⟩
  have hRowLength' : rowPoints.length = 3 := by
    simpa [rowPoints, points] using hRowLength
  obtain ⟨p, q, r, hRowPoints⟩ := List.length_eq_three.mp hRowLength'
  have ha' : a ∈ [p, q, r] := by simpa [rowPoints, points, hRowPoints] using ha
  have hb' : b ∈ [p, q, r] := by simpa [rowPoints, points, hRowPoints] using hb
  have hc' : c ∈ [p, q, r] := by simpa [rowPoints, points, hRowPoints] using hc
  have hOrdered := fourKernelOrderedCompatibleExact_of_threshold
    m outside a b c u v w hOutsideU hOutsideV hOutsideW
    huv huw hvw hThreshold
  have hOrderedExpanded :
      fourKernelOrderedCompatibleExact m
        ((fourActivePoints m).filter fun point =>
          !fourSupportContains point.1 row) a b c = true := by
    simpa [outside, points] using hOrdered
  have hRowPointsExpanded :
      (fourActivePoints m).filter (fun point =>
        fourSupportContains point.1 row) = [p, q, r] := by
    simpa [rowPoints, points] using hRowPoints
  unfold fourKernelCompatibleExact
  apply List.any_eq_true.mpr
  refine ⟨row, List.mem_range.mpr hrow, ?_⟩
  change (decide (((fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row).length = 3) &&
    (match (fourActivePoints m).filter fun point => fourSupportContains point.1 row with
    | [p, q, r] =>
        let outside := (fourActivePoints m).filter fun point =>
          !fourSupportContains point.1 row
        fourKernelOrderedCompatibleExact m outside p q r ||
          fourKernelOrderedCompatibleExact m outside p r q ||
            fourKernelOrderedCompatibleExact m outside q p r ||
              fourKernelOrderedCompatibleExact m outside q r p ||
                fourKernelOrderedCompatibleExact m outside r p q ||
                  fourKernelOrderedCompatibleExact m outside r q p
    | _ => false)) = true
  rw [hRowPointsExpanded]
  simp only [List.length_cons, List.length_nil, decide_true, Bool.true_and]
  rcases three_distinct_members_order_cases ha' hb' hc' hab hac hbc with
    h | h | h | h | h | h
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]
  · simp [h.1, h.2.1, h.2.2, hOrderedExpanded]

theorem fourKernelCompatibleExact_of_witness
    (m : FourMultiplicity) (row : Nat) (a b c u v w : FourPoint)
    (hrow : row < 4)
    (hRowLength :
      ((fourActivePoints m).filter fun point =>
        fourSupportContains point.1 row).length = 3)
    (ha : a ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hb : b ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hc : c ∈ (fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu : u ∈ fourActivePoints m) (hv : v ∈ fourActivePoints m)
    (hw : w ∈ fourActivePoints m)
    (huRow : fourSupportContains u.1 row = false)
    (hvRow : fourSupportContains v.1 row = false)
    (hwRow : fourSupportContains w.1 row = false)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hA : fourTriplePointCover a u v = true)
    (hB : fourTriplePointCover b u w = true)
    (hC : fourTriplePointCover c v w = true)
    (hWeighted : fourWeightedCoverCount m ≤ 6) :
    fourKernelCompatibleExact m = true := by
  apply fourKernelCompatibleExact_of_threshold_witness m row a b c u v w
    hrow hRowLength ha hb hc hab hac hbc hu hv hw huRow hvRow hwRow huv huw hvw
  simpa [fourKernelMatchedRows, hA, hB, hC] using hWeighted

end AiMathLab.P0054.G419
