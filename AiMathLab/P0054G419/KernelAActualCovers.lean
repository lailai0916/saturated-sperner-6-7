import AiMathLab.P0054G419.KernelAActualClutter
import AiMathLab.P0054G419.KernelACoverComplete

namespace AiMathLab.P0054.G419

open G413

theorem fourActualSupportCover_of_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {B : Row α} (hBT : B ∈ blocker T) :
    fourMinimalSupportCover (B.image (fourActualSupportIndex rowOrder)) := by
  classical
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  have hMinimal := mem_blocker.mp hBT
  constructor
  · intro row
    obtain ⟨x, hxB, hxRow⟩ := hMinimal.prop
      (rowOrder row : Row α) (rowOrder row).property
    have hxActive : x ∈ fourActiveUniverse T :=
      mem_fourActiveUniverse.mpr ⟨rowOrder row, (rowOrder row).property, hxRow⟩
    let s := fourActualSupportIndex rowOrder x
    refine ⟨s, Finset.mem_image.mpr ⟨x, hxB, rfl⟩, ?_⟩
    rw [fourSupport_actualSupportIndex rowOrder hProper hxActive]
    exact (mem_fourSupportOfPoint rowOrder x row).mpr hxRow
  · intro s hsC hErasedCover
    obtain ⟨x, hxB, hxIndex⟩ := Finset.mem_image.mp hsC
    obtain ⟨E, hPrivate⟩ := hMinimal.exists_privateRow hxB
    let e : T := ⟨E, hPrivate.1⟩
    obtain ⟨row, hRow⟩ := rowOrder.surjective e
    obtain ⟨t, htErased, hrowt⟩ := hErasedCover row
    have htC : t ∈ B.image (fourActualSupportIndex rowOrder) :=
      Finset.mem_of_mem_erase htErased
    obtain ⟨y, hyB, hyIndex⟩ := Finset.mem_image.mp htC
    obtain ⟨F, hYPrivate⟩ := hMinimal.exists_privateRow hyB
    have hyActive : y ∈ fourActiveUniverse T :=
      mem_fourActiveUniverse.mpr ⟨F, hYPrivate.1, hYPrivate.2.2.1⟩
    have hyRow : y ∈ (rowOrder row : Row α) := by
      apply (mem_fourSupportOfPoint rowOrder y row).mp
      rw [← fourSupport_actualSupportIndex rowOrder hProper hyActive, hyIndex]
      exact hrowt
    have hRowValue : (rowOrder row : Row α) = E := by
      simpa [e] using congrArg Subtype.val hRow
    have hyE : y ∈ E := by simpa [hRowValue] using hyRow
    have hyx : y = x := hPrivate.2.2.2 hyB hyE
    have hts : t = s := by
      calc
        t = fourActualSupportIndex rowOrder y := hyIndex.symm
        _ = fourActualSupportIndex rowOrder x := congrArg _ hyx
        _ = s := hxIndex
    exact (Finset.mem_erase.mp htErased).1 hts

theorem fourActualSupportMultiplicity_active_supports_covered_of_complete
    {α : Type*} [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hComplete : ∀ C : Finset FourSupportIndex, fourMinimalSupportCover C →
      ∃ L ∈ fourMinimalSupportIndexCovers, L.toFinset = C) :
    fourActiveSupportsCovered (fourActualSupportMultiplicity rowOrder) = true := by
  classical
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  unfold fourActiveSupportsCovered
  rw [List.all_eq_true]
  intro s hsRange
  by_cases hsZero :
      fourMultiplicityDigit (fourActualSupportMultiplicity rowOrder) s = 0
  · simp [hsZero]
  · have hsLt : s < 14 := List.mem_range.mp hsRange
    let si : FourSupportIndex := ⟨s, hsLt⟩
    have hsFiberCard : (fourSupportFiber rowOrder si).card ≠ 0 := by
      intro hCard
      apply hsZero
      simpa [si] using
        (fourMultiplicityDigit_actualSupportMultiplicity rowOrder si).trans hCard
    obtain ⟨x, hxFiber⟩ :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hsFiberCard)
    have hxActive : x ∈ fourActiveUniverse T := (Finset.mem_filter.mp hxFiber).1
    have hxIndex : fourActualSupportIndex rowOrder x = si :=
      (Finset.mem_filter.mp hxFiber).2
    obtain ⟨E, hET, hxE⟩ := mem_fourActiveUniverse.mp hxActive
    obtain ⟨B, hBT, hPrivate⟩ :=
      exists_blocker_private_at_row hTClutter hET hxE
    have hCover := fourActualSupportCover_of_blocker rowOrder hBRows hBT
    obtain ⟨L, hL, hLC⟩ := hComplete _ hCover
    let values := L.map fun i ↦ i.val
    have hValues : values ∈ fourMinimalSupportCovers := by
      have hMapped : values ∈
          fourMinimalSupportIndexCovers.map (fun C ↦ C.map fun i ↦ i.val) :=
        List.mem_map.mpr ⟨L, hL, rfl⟩
      rwa [four_minimal_support_index_covers_values] at hMapped
    have hsiC : si ∈ B.image (fourActualSupportIndex rowOrder) :=
      Finset.mem_image.mpr ⟨x, hPrivate.2.1, hxIndex⟩
    have hsiL : si ∈ L.toFinset := by rw [hLC]; exact hsiC
    have hsValues : s ∈ values := by
      apply List.mem_map.mpr
      exact ⟨si, List.mem_toFinset.mp hsiL, rfl⟩
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨values, hValues, ?_⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact decide_eq_true hsValues
    · rw [List.all_eq_true]
      intro t htValues
      obtain ⟨ti, htiL, rfl⟩ := List.mem_map.mp htValues
      have htiC : ti ∈ B.image (fourActualSupportIndex rowOrder) := by
        rw [← hLC]
        exact List.mem_toFinset.mpr htiL
      obtain ⟨y, hyB, hyIndex⟩ := Finset.mem_image.mp htiC
      obtain ⟨F, hYPrivate⟩ := (mem_blocker.mp hBT).exists_privateRow hyB
      have hyActive : y ∈ fourActiveUniverse T :=
        mem_fourActiveUniverse.mpr ⟨F, hYPrivate.1, hYPrivate.2.2.1⟩
      have hyFiber : y ∈ fourSupportFiber rowOrder ti :=
        Finset.mem_filter.mpr ⟨hyActive, hyIndex⟩
      apply decide_eq_true
      rw [fourMultiplicityDigit_actualSupportMultiplicity]
      exact Finset.card_pos.mpr ⟨y, hyFiber⟩

end AiMathLab.P0054.G419
