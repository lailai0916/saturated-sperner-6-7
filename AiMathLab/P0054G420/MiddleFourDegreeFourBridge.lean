import AiMathLab.P0054G420.MiddleFourDegreeFourActual
import AiMathLab.P0054G413.PairGraphs.ThreeK2Lift

namespace AiMathLab.P0054.G420

open G413 G419

abbrev MiddleFourActivePoint {alpha : Type*} [DecidableEq alpha]
    (T : G413.Hypergraph alpha) :=
  {x : alpha // x ∈ fourActiveUniverse T}

def middleFourActiveRow {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (E : G413.Row alpha) :
    G413.Row (MiddleFourActivePoint T) :=
  Finset.univ.filter fun x ↦ x.1 ∈ E

def middleFourActiveKernelRows {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    List (G413.Row (MiddleFourActivePoint T)) :=
  (List.finRange 4).map fun row ↦ middleFourActiveRow (rowOrder row)

theorem fourActivePoints_nodup (m : FourMultiplicity) :
    (fourActivePoints m).Nodup := by
  unfold fourActivePoints
  rw [List.nodup_flatMap]
  constructor
  · intro support hSupport
    have hCopies : (List.range (fourMultiplicityDigit m support)).Nodup :=
      List.nodup_range
    exact hCopies.map (by
      intro left right hEq
      exact congrArg Prod.snd hEq)
  · exact List.nodup_range.imp (by
      intro left right hne point hPointLeft hPointRight
      obtain ⟨leftCopy, -, rfl⟩ := List.mem_map.mp hPointLeft
      obtain ⟨rightCopy, -, hEq⟩ := List.mem_map.mp hPointRight
      exact hne (congrArg Prod.fst hEq).symm)

theorem fourActualPoint_surjective_on_activePoints {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    {point : FourPoint}
    (hPoint : point ∈ fourActivePoints
      (fourActualSupportMultiplicity rowOrder)) :
    ∃ x, x ∈ fourActiveUniverse T ∧ fourActualPoint rowOrder x = point := by
  unfold fourActivePoints at hPoint
  obtain ⟨support, hSupport, hPoint⟩ := List.mem_flatMap.mp hPoint
  obtain ⟨copy, hCopy, rfl⟩ := List.mem_map.mp hPoint
  have hSupportLt : support < 14 := List.mem_range.mp hSupport
  let supportIndex : FourSupportIndex := ⟨support, hSupportLt⟩
  have hCopyLt : copy < (fourSupportFiber rowOrder supportIndex).card := by
    rw [← fourMultiplicityDigit_actualSupportMultiplicity rowOrder supportIndex]
    exact List.mem_range.mp hCopy
  let copyIndex : Fin (fourSupportFiber rowOrder supportIndex).card :=
    ⟨copy, hCopyLt⟩
  let actualPoint :=
    (Finset.equivFin (fourSupportFiber rowOrder supportIndex)).symm copyIndex
  have hActualFiber :
      actualPoint.1 ∈ fourSupportFiber rowOrder supportIndex := actualPoint.2
  have hActualActive : actualPoint.1 ∈ fourActiveUniverse T :=
    (Finset.mem_filter.mp hActualFiber).1
  have hActualSupport :
      fourActualSupportIndex rowOrder actualPoint.1 = supportIndex :=
    (Finset.mem_filter.mp hActualFiber).2
  refine ⟨actualPoint.1, hActualActive, ?_⟩
  apply Prod.ext
  · exact congrArg Fin.val hActualSupport
  · unfold fourActualPoint fourActualCopyIndex
    dsimp only
    rw [hActualSupport]
    simp only [hActualFiber, dite_true]
    have hInverse :=
      (Finset.equivFin (fourSupportFiber rowOrder supportIndex)).apply_symm_apply
        copyIndex
    exact congrArg Fin.val hInverse

theorem middleFourModelSupports_toList (m : FourMultiplicity) :
    middleFourModelSupports m.toList = (fourActivePoints m).map Prod.fst := by
  unfold middleFourModelSupports fourActivePoints fourMultiplicityDigit
  simp only [List.map_flatMap, List.map_map, Function.comp_apply]
  apply List.flatMap_congr
  intro support hSupport
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]
  change List.replicate (m[support]?.getD 0) support =
    (List.range (m[support]?.getD 0)).map (fun _ ↦ support)
  simpa only [List.length_range] using
    (List.map_const' (l := List.range (m[support]?.getD 0))
      (b := support)).symm

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_model_supports_length :
    ∀ values ∈ middleFourMultiplicityCertificate,
      (middleFourModelSupports values).length < 16 := by
  decide

set_option maxRecDepth 100000 in
theorem middleFourMultiplicityCertificate_model_supports_length_le_seven :
    ∀ values ∈ middleFourMultiplicityCertificate,
      (middleFourModelSupports values).length ≤ 7 := by
  decide

theorem middleFourActualPoints_length_lt_sixteen {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hBound :=
    middleFourMultiplicityCertificate_model_supports_length values hValues
  rw [← hList] at hBound
  rw [middleFourModelSupports_toList, List.length_map] at hBound
  exact hBound

theorem middleFourActualPoints_length_le_seven {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length ≤ 7 := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hBound :=
    middleFourMultiplicityCertificate_model_supports_length_le_seven
      values hValues
  rw [← hList] at hBound
  rw [middleFourModelSupports_toList, List.length_map] at hBound
  exact hBound

noncomputable def middleFourActualModelIndex {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (x : MiddleFourActivePoint T) : Nat :=
  (fourActivePoints (fourActualSupportMultiplicity rowOrder)).idxOf
    (fourActualPoint rowOrder x.1)

theorem middleFourActualModelIndex_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    Function.Injective (middleFourActualModelIndex rowOrder) := by
  intro left right hEq
  apply Subtype.ext
  apply fourActualPoint_injective_on_active rowOrder left.2 right.2
  apply (List.idxOf_inj
    (fourActualPoint_mem_activePoints rowOrder left.2)).mp
  exact hEq

noncomputable def middleFourActualModelPoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (x : MiddleFourActivePoint T) : MiddleFourModelPoint :=
  ⟨middleFourActualModelIndex rowOrder x % 16,
    Nat.mod_lt _ (by omega)⟩

@[simp]
theorem middleFourActualModelPoint_val {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (x : MiddleFourActivePoint T) :
    (middleFourActualModelPoint rowOrder x).val =
      middleFourActualModelIndex rowOrder x % 16 := rfl

theorem middleFourActualModelPoint_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    Function.Injective (middleFourActualModelPoint rowOrder) := by
  intro left right hEq
  have hLeftLt : middleFourActualModelIndex rowOrder left < 16 :=
    (List.idxOf_lt_length_of_mem
      (fourActualPoint_mem_activePoints rowOrder left.2)).trans hLength
  have hRightLt : middleFourActualModelIndex rowOrder right < 16 :=
    (List.idxOf_lt_length_of_mem
      (fourActualPoint_mem_activePoints rowOrder right.2)).trans hLength
  apply middleFourActualModelIndex_injective rowOrder
  have hVal := congrArg Fin.val hEq
  simpa only [middleFourActualModelPoint_val,
    Nat.mod_eq_of_lt hLeftLt, Nat.mod_eq_of_lt hRightLt] using hVal

theorem middleFourActualModelPoint_val_lt_activePoints_length
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (point : MiddleFourActivePoint T) :
    (middleFourActualModelPoint rowOrder point).val <
      (fourActivePoints
        (fourActualSupportMultiplicity rowOrder)).length := by
  have hIndex := List.idxOf_lt_length_of_mem
    (fourActualPoint_mem_activePoints rowOrder point.2)
  have hIndexSixteen := hIndex.trans hLength
  rw [middleFourActualModelPoint_val]
  unfold middleFourActualModelIndex
  rw [Nat.mod_eq_of_lt hIndexSixteen]
  exact hIndex

theorem middleFourModelSupport_actualPoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (x : MiddleFourActivePoint T) :
    (middleFourModelSupports
      (fourActualSupportMultiplicity rowOrder).toList).getD
        (middleFourActualModelPoint rowOrder x).val 0 =
      (fourActualPoint rowOrder x.1).1 := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hMem : fourActualPoint rowOrder x.1 ∈ fourActivePoints actual :=
    fourActualPoint_mem_activePoints rowOrder x.2
  have hIndexLt : middleFourActualModelIndex rowOrder x <
      (fourActivePoints actual).length :=
    List.idxOf_lt_length_of_mem hMem
  have hIndexSixteen : middleFourActualModelIndex rowOrder x < 16 :=
    hIndexLt.trans hLength
  have hMapIdxOfLt :
      (fourActivePoints actual).idxOf (fourActualPoint rowOrder x.1) <
        ((fourActivePoints actual).map Prod.fst).length := by
    simpa only [List.length_map] using List.idxOf_lt_length_of_mem hMem
  rw [middleFourActualModelPoint_val, Nat.mod_eq_of_lt hIndexSixteen,
    middleFourModelSupports_toList]
  change ((fourActivePoints actual).map Prod.fst).getD
      ((fourActivePoints actual).idxOf (fourActualPoint rowOrder x.1)) 0 =
    (fourActualPoint rowOrder x.1).1
  rw [List.getD_eq_getElem _ _ hMapIdxOfLt]
  simp only [List.getElem_map]
  exact congrArg Prod.fst
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem hMem))

def middleFourModelKernelRow (values : List Nat) (row : Nat) :
    G413.Row MiddleFourModelPoint :=
  Finset.univ.filter fun point ↦
    point.val < (middleFourModelSupports values).length &&
      fourSupportContains
        ((middleFourModelSupports values).getD point.val 0) row

theorem middleFourModelKernelRows_eq (values : List Nat) :
    middleFourModelKernelRows values =
      (List.range 4).map (middleFourModelKernelRow values) := rfl

theorem middleFourActualModelPoint_mem_kernelRow_iff {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (row : FourVertex) (x : MiddleFourActivePoint T) :
    middleFourActualModelPoint rowOrder x ∈
        middleFourModelKernelRow
          (fourActualSupportMultiplicity rowOrder).toList row.val ↔
      x.1 ∈ (rowOrder row : G413.Row alpha) := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hMem : fourActualPoint rowOrder x.1 ∈ fourActivePoints actual :=
    fourActualPoint_mem_activePoints rowOrder x.2
  have hIndexLt : middleFourActualModelIndex rowOrder x <
      (fourActivePoints actual).length :=
    List.idxOf_lt_length_of_mem hMem
  have hIndexSixteen : middleFourActualModelIndex rowOrder x < 16 :=
    hIndexLt.trans hLength
  have hSupportsLength :
      (middleFourModelSupports actual.toList).length =
        (fourActivePoints actual).length := by
    have hEq := congrArg List.length (middleFourModelSupports_toList actual)
    simpa only [List.length_map] using hEq
  have hPointLt : (middleFourActualModelPoint rowOrder x).val <
      (middleFourModelSupports actual.toList).length := by
    rw [middleFourActualModelPoint_val, Nat.mod_eq_of_lt hIndexSixteen,
      hSupportsLength]
    exact hIndexLt
  simp only [middleFourModelKernelRow, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [show decide ((middleFourActualModelPoint rowOrder x).val <
      (middleFourModelSupports actual.toList).length) = true by
        exact decide_eq_true hPointLt]
  simp only [Bool.true_and]
  rw [middleFourModelSupport_actualPoint rowOrder hLength x,
    fourSupportContains_actualPoint rowOrder hBRows x.2 row,
    decide_eq_true_eq]

theorem middleFourActiveRow_image_eq_modelKernelRow {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (row : FourVertex) :
    (middleFourActiveRow (rowOrder row)).image
        (middleFourActualModelPoint rowOrder) =
      middleFourModelKernelRow
        (fourActualSupportMultiplicity rowOrder).toList row.val := by
  let actual := fourActualSupportMultiplicity rowOrder
  let modelRow := middleFourModelKernelRow actual.toList row.val
  have hSupportsLength :
      (middleFourModelSupports actual.toList).length =
        (fourActivePoints actual).length := by
    have hEq := congrArg List.length (middleFourModelSupports_toList actual)
    simpa only [List.length_map] using hEq
  ext point
  constructor
  · intro hPoint
    obtain ⟨x, hxRow, rfl⟩ := Finset.mem_image.mp hPoint
    apply (middleFourActualModelPoint_mem_kernelRow_iff
      rowOrder hBRows hLength row x).mpr
    exact (Finset.mem_filter.mp hxRow).2
  · intro hPoint
    have hPointModel : point ∈ modelRow := by simpa [modelRow] using hPoint
    have hFilter := (Finset.mem_filter.mp hPointModel).2
    have hPointLt : point.val <
        (middleFourModelSupports actual.toList).length := by
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hFilter).1
    have hPointActive : point.val < (fourActivePoints actual).length := by
      simpa only [hSupportsLength] using hPointLt
    let pointData : FourPoint := (fourActivePoints actual)[point.val]
    have hPointDataMem : pointData ∈ fourActivePoints actual := by
      exact List.getElem_mem ..
    obtain ⟨x, hxActive, hActualPoint⟩ :=
      fourActualPoint_surjective_on_activePoints rowOrder hPointDataMem
    let activePoint : MiddleFourActivePoint T := ⟨x, hxActive⟩
    have hEncoded : middleFourActualModelPoint rowOrder activePoint = point := by
      apply Fin.ext
      rw [middleFourActualModelPoint_val]
      have hIndex : middleFourActualModelIndex rowOrder activePoint = point.val := by
        unfold middleFourActualModelIndex
        rw [hActualPoint]
        exact (fourActivePoints_nodup actual).idxOf_getElem
          point.val hPointActive
      rw [hIndex, Nat.mod_eq_of_lt point.isLt]
    apply Finset.mem_image.mpr
    refine ⟨activePoint, ?_, hEncoded⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (middleFourActualModelPoint_mem_kernelRow_iff
      rowOrder hBRows hLength row activePoint).mp
    simpa [modelRow, hEncoded] using hPointModel

theorem middleFourActiveKernel_image_eq_modelKernel {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow ↦ activeRow.image
          (middleFourActualModelPoint rowOrder)) =
      middleFourModelKernel
        (fourActualSupportMultiplicity rowOrder).toList := by
  let actual := fourActualSupportMultiplicity rowOrder
  ext modelRow
  rw [middleFourModelKernel]
  constructor
  · intro hModelRow
    obtain ⟨activeRow, hActiveRow, rfl⟩ := Finset.mem_image.mp hModelRow
    obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp
      (List.mem_toFinset.mp hActiveRow)
    rw [middleFourActiveRow_image_eq_modelKernelRow
      rowOrder hBRows hLength row]
    apply List.mem_toFinset.mpr
    rw [middleFourModelKernelRows_eq]
    exact List.mem_map.mpr
      ⟨row.val, List.mem_range.mpr row.isLt, rfl⟩
  · intro hModelRow
    rw [middleFourModelKernelRows_eq] at hModelRow
    obtain ⟨row, hRow, hModelRowEq⟩ := List.mem_map.mp
      (List.mem_toFinset.mp hModelRow)
    have hRowLt : row < 4 := List.mem_range.mp hRow
    let rowIndex : FourVertex := ⟨row, hRowLt⟩
    apply Finset.mem_image.mpr
    refine ⟨middleFourActiveRow (rowOrder rowIndex), ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨rowIndex, List.mem_finRange rowIndex, rfl⟩
    · rw [middleFourActiveRow_image_eq_modelKernelRow
        rowOrder hBRows hLength rowIndex]
      simpa [rowIndex] using hModelRowEq

theorem middleFourActiveRow_image_subtypeVal {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} {E : G413.Row alpha} (hET : E ∈ T) :
    (middleFourActiveRow (T := T) E).image Subtype.val = E := by
  ext x
  constructor
  · intro hx
    obtain ⟨activePoint, hActivePoint, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hActivePoint).2
  · intro hxE
    have hxActive : x ∈ fourActiveUniverse T :=
      mem_fourActiveUniverse.mpr ⟨E, hET, hxE⟩
    let activePoint : MiddleFourActivePoint T := ⟨x, hxActive⟩
    apply Finset.mem_image.mpr
    refine ⟨activePoint, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxE⟩

theorem middleFourActiveKernel_image_subtypeVal {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    (middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow ↦ activeRow.image Subtype.val) = T := by
  ext E
  constructor
  · intro hE
    obtain ⟨activeRow, hActiveRow, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp
      (List.mem_toFinset.mp hActiveRow)
    rw [middleFourActiveRow_image_subtypeVal (rowOrder row).property]
    exact (rowOrder row).property
  · intro hET
    let e : T := ⟨E, hET⟩
    obtain ⟨row, hRow⟩ := rowOrder.surjective e
    have hRowValue : (rowOrder row : G413.Row alpha) = E := by
      simpa [e] using congrArg Subtype.val hRow
    apply Finset.mem_image.mpr
    refine ⟨middleFourActiveRow (rowOrder row), ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      exact List.mem_map.mpr
        ⟨row, List.mem_finRange row, rfl⟩
    · rw [middleFourActiveRow_image_subtypeVal (rowOrder row).property]
      exact hRowValue

theorem middleFourModelKernel_blocker_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    blocker (middleFourModelKernel
        (fourActualSupportMultiplicity rowOrder).toList) =
      (blocker (middleFourActiveKernelRows rowOrder).toFinset).image
        (fun activeRow ↦ activeRow.image
          (middleFourActualModelPoint rowOrder)) := by
  calc
    blocker (middleFourModelKernel
        (fourActualSupportMultiplicity rowOrder).toList) =
        blocker ((middleFourActiveKernelRows rowOrder).toFinset.image
          (fun activeRow ↦ activeRow.image
            (middleFourActualModelPoint rowOrder))) :=
      congrArg blocker
        (middleFourActiveKernel_image_eq_modelKernel
          rowOrder hBRows hLength).symm
    _ = _ := blocker_image_eq_of_injective
      (middleFourActualModelPoint_injective rowOrder hLength)

theorem middleFourActiveKernel_blocker_image_subtypeVal {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T) :
    blocker T =
      (blocker (middleFourActiveKernelRows rowOrder).toFinset).image
        (fun activeRow ↦ activeRow.image Subtype.val) := by
  calc
    blocker T = blocker ((middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow ↦ activeRow.image Subtype.val)) :=
      congrArg blocker (middleFourActiveKernel_image_subtypeVal rowOrder).symm
    _ = _ := blocker_image_eq_of_injective Subtype.val_injective

theorem middleFourListPowerset_toFinset {alpha : Type*}
    [DecidableEq alpha] (values : List alpha) :
    ((middleFourListPowerset values).map List.toFinset).toFinset =
      values.toFinset.powerset := by
  induction values with
  | nil => simp [middleFourListPowerset]
  | cons value values ih =>
      rw [middleFourListPowerset, List.map_append, List.toFinset_append]
      rw [List.toFinset_cons, Finset.powerset_insert, ← ih]
      congr 1
      ext row
      simp [Function.comp_def]

theorem middleFourListPowerset_toFinset_nodup {alpha : Type*}
    [DecidableEq alpha] {values : List alpha} (hValues : values.Nodup) :
    ((middleFourListPowerset values).map List.toFinset).Nodup := by
  induction values with
  | nil => simp [middleFourListPowerset]
  | cons value values ih =>
      have hValue : value ∉ values := (List.nodup_cons.mp hValues).1
      have hTail : values.Nodup := (List.nodup_cons.mp hValues).2
      let rows := (middleFourListPowerset values).map List.toFinset
      have hRows : rows.Nodup := by
        simpa [rows] using ih hTail
      have hValueRows : ∀ row ∈ rows, value ∉ row := by
        intro row hRow hValueRow
        have hPowerset : row ∈ values.toFinset.powerset := by
          rw [← middleFourListPowerset_toFinset values]
          exact List.mem_toFinset.mpr hRow
        have hValueList : value ∈ values := by
          apply List.mem_toFinset.mp
          exact (Finset.mem_powerset.mp hPowerset) hValueRow
        exact hValue hValueList
      rw [middleFourListPowerset, List.map_append, List.map_map]
      simp only [Function.comp_def]
      have hInsertRows :
          (middleFourListPowerset values).map
              (fun row ↦ (value :: row).toFinset) =
            rows.map (fun row ↦ insert value row) := by
        simp [rows, List.map_map, Function.comp_def]
      rw [hInsertRows]
      change (rows ++ rows.map (fun row ↦ insert value row)).Nodup
      apply hRows.append
      · apply hRows.map_on
        intro left hLeft right hRight hEq
        have hErase := congrArg (fun row : Finset alpha ↦ row.erase value) hEq
        simpa [hValueRows left hLeft, hValueRows right hRight] using hErase
      · rw [List.disjoint_left]
        intro left hLeft hLeftInserted
        obtain ⟨right, hRight, hRightEq⟩ := List.mem_map.mp hLeftInserted
        have hValueLeft := hValueRows left hLeft
        apply hValueLeft
        rw [← hRightEq]
        exact Finset.mem_insert_self value right

theorem middleFourListPowerset_filter_mem {alpha : Type*}
    (predicate : alpha → Bool) (values : List alpha) :
    values.filter predicate ∈ middleFourListPowerset values := by
  induction values with
  | nil => simp [middleFourListPowerset]
  | cons value values ih =>
      cases hPredicate : predicate value <;>
        simp [middleFourListPowerset, hPredicate, ih]

theorem middleFourModelBlockerRows_nodup (values : List Nat) :
    (middleFourModelBlockerRows values).Nodup := by
  unfold middleFourModelBlockerRows
  apply List.Nodup.filter
  apply middleFourListPowerset_toFinset_nodup
  exact (List.nodup_finRange 16).filter _

theorem middleFourModelPairBlockerRows_toFinset (values : List Nat) :
    (middleFourModelPairBlockerRows values).toFinset =
      pairRows (middleFourModelBlocker values) := by
  ext row
  simp [middleFourModelPairBlockerRows, middleFourModelBlocker,
    pairRows]

theorem middleFourModelOtherBlockerRows_toFinset (values : List Nat) :
    (middleFourModelOtherBlockerRows values).toFinset =
      (middleFourModelBlocker values).filter fun row ↦ row.card ≠ 2 := by
  ext row
  simp [middleFourModelOtherBlockerRows, middleFourModelBlocker]

theorem middleFourModelKernel_biUnion_subset_activePoints
    (values : List Nat) :
    (middleFourModelKernel values).biUnion id ⊆
      (middleFourModelActivePoints values).toFinset := by
  intro point hPoint
  obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
  rw [middleFourModelKernel, middleFourModelKernelRows_eq] at hRow
  obtain ⟨rowIndex, hRowIndex, rfl⟩ := List.mem_map.mp
    (List.mem_toFinset.mp hRow)
  have hFilter := (Finset.mem_filter.mp hPointRow).2
  have hPointLt : point.val < (middleFourModelSupports values).length :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hFilter).1
  apply List.mem_toFinset.mpr
  apply List.mem_filter.mpr
  exact ⟨List.mem_finRange point, decide_eq_true hPointLt⟩

theorem middleFourModelBlocker_eq_blocker (values : List Nat) :
    middleFourModelBlocker values = blocker (middleFourModelKernel values) := by
  ext row
  constructor
  · intro hRow
    have hRowList := List.mem_toFinset.mp hRow
    unfold middleFourModelBlocker middleFourModelBlockerRows at hRowList
    obtain ⟨hRowCandidate, hRowFast⟩ := List.mem_filter.mp hRowList
    have hRowBlocker : row ∈
        fastBlocker (middleFourModelKernelRows values) :=
      of_decide_eq_true hRowFast
    rw [fastBlocker_eq_blocker] at hRowBlocker
    simpa only [middleFourModelKernel] using hRowBlocker
  · intro hRow
    have hRowSubset : row ⊆
        (middleFourModelActivePoints values).toFinset :=
      (blocker_row_subset_biUnion hRow).trans
        (middleFourModelKernel_biUnion_subset_activePoints values)
    have hRowPowerset : row ∈
        (middleFourModelActivePoints values).toFinset.powerset :=
      Finset.mem_powerset.mpr hRowSubset
    have hRowEnumerated : row ∈
        ((middleFourListPowerset
          (middleFourModelActivePoints values)).map List.toFinset).toFinset := by
      rw [middleFourListPowerset_toFinset]
      exact hRowPowerset
    obtain ⟨candidate, hCandidate, hCandidateRow⟩ := List.mem_map.mp
      (List.mem_toFinset.mp hRowEnumerated)
    rw [← hCandidateRow]
    apply List.mem_toFinset.mpr
    unfold middleFourModelBlockerRows
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨candidate, hCandidate, rfl⟩, ?_⟩
    apply decide_eq_true
    rw [fastBlocker_eq_blocker]
    simpa only [middleFourModelKernel, hCandidateRow] using hRow

theorem middleFourModelBlocker_card_eq_actual {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourModelBlocker
        (fourActualSupportMultiplicity rowOrder).toList).card =
      (blocker T).card := by
  rw [middleFourModelBlocker_eq_blocker,
    middleFourModelKernel_blocker_image rowOrder hBRows hLength,
    middleFourActiveKernel_blocker_image_subtypeVal rowOrder]
  rw [Finset.card_image_of_injective _
    (Finset.image_injective
      (middleFourActualModelPoint_injective rowOrder hLength))]
  rw [Finset.card_image_of_injective _
    (Finset.image_injective Subtype.val_injective)]

theorem middleFourActualModelBlocker_card_seven_or_eight {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    (middleFourModelBlocker actual.toList).card = 7 ∨
      (middleFourModelBlocker actual.toList).card = 8 := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hLength := middleFourActualPoints_length_lt_sixteen rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  have hCard := middleFourModelBlocker_card_eq_actual rowOrder hBRows hLength
  have hLower := fourWeightedCoverCount_le_blocker_card rowOrder hBRows
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  dsimp only [actual] at hCard hLower hProfile ⊢
  rcases hProfile with hEight | hSeven
  · right
    omega
  · omega

theorem middleFourModelSupports_length_eq_activePoints
    (m : FourMultiplicity) :
    (middleFourModelSupports m.toList).length =
      (fourActivePoints m).length := by
  have hLength := congrArg List.length (middleFourModelSupports_toList m)
  simpa only [List.length_map] using hLength

theorem middleFourModelCenter_val_eq_activePoints_length
    (m : FourMultiplicity)
    (hLength : (fourActivePoints m).length < 16) :
    (middleFourModelCenter m.toList).val =
      (fourActivePoints m).length := by
  unfold middleFourModelCenter
  change (middleFourModelSupports m.toList).length % 16 =
    (fourActivePoints m).length
  rw [middleFourModelSupports_length_eq_activePoints,
    Nat.mod_eq_of_lt hLength]

noncomputable def middleFourBasePoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (_centerPoint : alpha) (point : alpha) : MiddleFourModelPoint :=
  if hPoint : point ∈ fourActiveUniverse T then
    middleFourActualModelPoint rowOrder ⟨point, hPoint⟩
  else
    middleFourModelCenter (fourActualSupportMultiplicity rowOrder).toList

theorem middleFourBasePoint_active {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha) (point : MiddleFourActivePoint T) :
    middleFourBasePoint rowOrder centerPoint point.1 =
      middleFourActualModelPoint rowOrder point := by
  simp [middleFourBasePoint, point.2]

theorem middleFourBasePoint_injOn_active {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    Set.InjOn (middleFourBasePoint rowOrder centerPoint)
      (fourActiveUniverse T) := by
  intro left hLeft right hRight hEq
  have hEncoded :
      middleFourActualModelPoint rowOrder ⟨left, hLeft⟩ =
        middleFourActualModelPoint rowOrder ⟨right, hRight⟩ := by
    calc
      middleFourActualModelPoint rowOrder ⟨left, hLeft⟩ =
          middleFourBasePoint rowOrder centerPoint left :=
        (middleFourBasePoint_active rowOrder centerPoint ⟨left, hLeft⟩).symm
      _ = middleFourBasePoint rowOrder centerPoint right := hEq
      _ = middleFourActualModelPoint rowOrder ⟨right, hRight⟩ :=
        middleFourBasePoint_active rowOrder centerPoint ⟨right, hRight⟩
  exact congrArg Subtype.val
    (middleFourActualModelPoint_injective rowOrder hLength hEncoded)

theorem middleFourBlockerRow_subset_activeUniverse {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} {row : G413.Row alpha}
    (hRow : row ∈ blocker T) : row ⊆ fourActiveUniverse T := by
  intro point hPoint
  apply mem_fourActiveUniverse.mpr
  exact Finset.mem_biUnion.mp (blocker_row_subset_biUnion hRow hPoint)

theorem middleFourBlockerRow_basePoint_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    {row : G413.Row alpha} (hRow : row ∈ blocker T) :
    (row.image (middleFourBasePoint rowOrder centerPoint)).card = row.card := by
  apply Finset.card_image_iff.mpr
  exact (middleFourBasePoint_injOn_active
    rowOrder centerPoint hLength).mono
      (middleFourBlockerRow_subset_activeUniverse hRow)

theorem middleFourBlockerRow_basePoint_injOn {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    Set.InjOn (fun row : G413.Row alpha ↦
      row.image (middleFourBasePoint rowOrder centerPoint))
        (blocker T) := by
  intro left hLeft right hRight hRows
  have hRows' :
      left.image (middleFourBasePoint rowOrder centerPoint) =
        right.image (middleFourBasePoint rowOrder centerPoint) := hRows
  have hPointInj := middleFourBasePoint_injOn_active
    rowOrder centerPoint hLength
  ext point
  constructor
  · intro hPointLeft
    have hImagePoint : middleFourBasePoint rowOrder centerPoint point ∈
        right.image (middleFourBasePoint rowOrder centerPoint) := by
      rw [← hRows']
      exact Finset.mem_image.mpr ⟨point, hPointLeft, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointActive := middleFourBlockerRow_subset_activeUniverse hLeft hPointLeft
    have hOtherActive := middleFourBlockerRow_subset_activeUniverse hRight hOther
    exact (hPointInj hOtherActive hPointActive hOtherEq) ▸ hOther
  · intro hPointRight
    have hImagePoint : middleFourBasePoint rowOrder centerPoint point ∈
        left.image (middleFourBasePoint rowOrder centerPoint) := by
      rw [hRows']
      exact Finset.mem_image.mpr ⟨point, hPointRight, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointActive := middleFourBlockerRow_subset_activeUniverse hRight hPointRight
    have hOtherActive := middleFourBlockerRow_subset_activeUniverse hLeft hOther
    exact (hPointInj hOtherActive hPointActive hOtherEq) ▸ hOther

theorem middleFourActualBlocker_image_basePoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (centerPoint : alpha)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (blocker T).image (fun row ↦ row.image
        (middleFourBasePoint rowOrder centerPoint)) =
      middleFourModelBlocker
        (fourActualSupportMultiplicity rowOrder).toList := by
  rw [middleFourModelBlocker_eq_blocker,
    middleFourActiveKernel_blocker_image_subtypeVal rowOrder,
    middleFourModelKernel_blocker_image rowOrder hBRows hLength,
    Finset.image_image]
  apply Finset.image_congr
  intro activeRow _hActiveRow
  simp only [Function.comp_apply]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro point _hPoint
  exact middleFourBasePoint_active rowOrder centerPoint point

end AiMathLab.P0054.G420
