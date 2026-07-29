import AiMathLab.P0054G419.KernelAActualEnumerated
import AiMathLab.P0054G419.KernelAExclusion

namespace AiMathLab.P0054.G419

open G413

noncomputable def fourActualCopyIndex {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α) : Nat :=
  let s := fourActualSupportIndex rowOrder x
  if hx : x ∈ fourSupportFiber rowOrder s then
    (Finset.equivFin (fourSupportFiber rowOrder s) ⟨x, hx⟩).val
  else 0

noncomputable def fourActualPoint {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α) : FourPoint :=
  ((fourActualSupportIndex rowOrder x).val, fourActualCopyIndex rowOrder x)

theorem fourActualPoint_mem_activePoints {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    {x : α} (hx : x ∈ fourActiveUniverse T) :
    fourActualPoint rowOrder x ∈
      fourActivePoints (fourActualSupportMultiplicity rowOrder) := by
  classical
  let s := fourActualSupportIndex rowOrder x
  have hxFiber : x ∈ fourSupportFiber rowOrder s :=
    Finset.mem_filter.mpr ⟨hx, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨s.val, List.mem_range.mpr s.isLt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨fourActualCopyIndex rowOrder x, List.mem_range.mpr ?_, ?_⟩
  · rw [fourMultiplicityDigit_actualSupportMultiplicity]
    simp [fourActualCopyIndex, s, hxFiber]
  · simp [fourActualPoint, s]

theorem fourActualPoint_injective_on_active {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) :
    Set.InjOn (fourActualPoint rowOrder) (fourActiveUniverse T) := by
  classical
  intro x hx y hy hxy
  let sx := fourActualSupportIndex rowOrder x
  have hxFiber : x ∈ fourSupportFiber rowOrder sx :=
    Finset.mem_filter.mpr ⟨hx, rfl⟩
  have hyFiber : y ∈ fourSupportFiber rowOrder (fourActualSupportIndex rowOrder y) :=
    Finset.mem_filter.mpr ⟨hy, rfl⟩
  have hsVal : (fourActualSupportIndex rowOrder x).val =
      (fourActualSupportIndex rowOrder y).val := congrArg Prod.fst hxy
  have hs : fourActualSupportIndex rowOrder y = sx := by
    apply Fin.ext
    simpa [sx] using hsVal.symm
  have hyFiber' : y ∈ fourSupportFiber rowOrder sx := by
    simpa [hs] using hyFiber
  have hCopy : fourActualCopyIndex rowOrder x = fourActualCopyIndex rowOrder y :=
    congrArg Prod.snd hxy
  have hCopyFin :
      Finset.equivFin (fourSupportFiber rowOrder sx) ⟨x, hxFiber⟩ =
        Finset.equivFin (fourSupportFiber rowOrder sx) ⟨y, hyFiber'⟩ := by
    apply Fin.ext
    unfold fourActualCopyIndex at hCopy
    dsimp only at hCopy
    rw [show fourActualSupportIndex rowOrder x = sx by rfl, hs] at hCopy
    simpa [hxFiber, hyFiber'] using hCopy
  exact congrArg Subtype.val
    ((Finset.equivFin (fourSupportFiber rowOrder sx)).injective hCopyFin)

theorem fourSupportContains_actualPoint {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {x : α} (hx : x ∈ fourActiveUniverse T) (row : FourVertex) :
    fourSupportContains (fourActualPoint rowOrder x).1 row.val =
      decide (x ∈ (rowOrder row : Row α)) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change fourSupportContains (fourActualSupportIndex rowOrder x).val row.val = true ↔ _
  rw [← mem_fourSupport, fourSupport_actualSupportIndex rowOrder
    (fourRows_actual_support_proper rowOrder hBRows) hx,
    mem_fourSupportOfPoint]

theorem fourActivePoints_filter_length (m : FourMultiplicity) (row : Nat) :
    ((fourActivePoints m).filter fun point =>
      fourSupportContains point.1 row).length = fourRowDegree m row := by
  unfold fourActivePoints fourRowDegree
  generalize List.range 14 = supports
  induction supports with
  | nil => rfl
  | cons s supports ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons, ih]
      by_cases hs : fourSupportContains s row = true
      · have hFilter :
            (List.map (fun copy => (s, copy))
              (List.range (fourMultiplicityDigit m s))).filter
                (fun point => fourSupportContains point.1 row) =
              List.map (fun copy => (s, copy))
                (List.range (fourMultiplicityDigit m s)) := by
          apply List.filter_eq_self.mpr
          intro point hPoint
          obtain ⟨copy, _hCopy, rfl⟩ := List.mem_map.mp hPoint
          exact hs
        rw [hFilter]
        rw [hs]
        simp
      · have hsFalse := Bool.eq_false_of_not_eq_true hs
        have hFilter :
            (List.map (fun copy => (s, copy))
              (List.range (fourMultiplicityDigit m s))).filter
                (fun point => fourSupportContains point.1 row) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro point hPoint
          obtain ⟨copy, _hCopy, rfl⟩ := List.mem_map.mp hPoint
          simp [hsFalse]
        rw [hFilter]
        rw [hsFalse]
        simp

theorem fourActualPoint_active_of_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} {B : Row α} (hBT : B ∈ blocker T)
    {x : α} (hxB : x ∈ B) : x ∈ fourActiveUniverse T := by
  obtain ⟨E, hPrivate⟩ := (mem_blocker.mp hBT).exists_privateRow hxB
  exact mem_fourActiveUniverse.mpr ⟨E, hPrivate.1, hPrivate.2.2.1⟩

theorem fourActualSupportMask_pair_ne_full {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {x y : α} (hx : x ∈ fourActiveUniverse T) (hy : y ∈ fourActiveUniverse T)
    (row : FourVertex) (hxRow : x ∉ (rowOrder row : Row α))
    (hyRow : y ∉ (rowOrder row : Row α)) :
    Nat.lor (fourSupportMask (fourActualPoint rowOrder x).1)
      (fourSupportMask (fourActualPoint rowOrder y).1) ≠ 15 := by
  intro hFull
  have hBit := congrArg (fun mask => mask.testBit row.val) hFull
  rw [Nat.lor_eq] at hBit
  rw [Nat.testBit_lor
    (fourSupportMask (fourActualPoint rowOrder x).1)
    (fourSupportMask (fourActualPoint rowOrder y).1) row.val] at hBit
  change (fourSupportContains (fourActualPoint rowOrder x).1 row.val ||
    fourSupportContains (fourActualPoint rowOrder y).1 row.val) =
      Nat.testBit 15 row.val at hBit
  rw [fourSupportContains_actualPoint rowOrder hBRows hx row,
    fourSupportContains_actualPoint rowOrder hBRows hy row] at hBit
  have hFullBit : Nat.testBit 15 row.val = true := by
    rw [show 15 = 2 ^ 4 - 1 by decide, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true row.isLt
  simp [hxRow, hyRow, hFullBit] at hBit

theorem fourActualSupportMasks_union_eq_full {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {B : Row α} (hBT : B ∈ blocker T) {a b c : α}
    (hB : B = {a, b, c}) :
    Nat.lor (fourSupportMask (fourActualPoint rowOrder a).1)
      (Nat.lor (fourSupportMask (fourActualPoint rowOrder b).1)
        (fourSupportMask (fourActualPoint rowOrder c).1)) = 15 := by
  have haB : a ∈ B := by simp [hB]
  have hbB : b ∈ B := by simp [hB]
  have hcB : c ∈ B := by simp [hB]
  have ha := fourActualPoint_active_of_mem_blocker hBT haB
  have hb := fourActualPoint_active_of_mem_blocker hBT hbB
  have hc := fourActualPoint_active_of_mem_blocker hBT hcB
  have hTransversal := (mem_blocker.mp hBT).prop
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.lor_eq, Nat.lor_eq]
  rw [Nat.testBit_lor, Nat.testBit_lor,
    show 15 = 2 ^ 4 - 1 by decide, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 4
  · let row : FourVertex := ⟨i, hi⟩
    obtain ⟨x, hxB, hxRow⟩ :=
      hTransversal (rowOrder row : Row α) (rowOrder row).property
    have hxCases : x = a ∨ x = b ∨ x = c := by
      simpa [hB] using hxB
    change (fourSupportContains (fourActualPoint rowOrder a).1 i ||
      (fourSupportContains (fourActualPoint rowOrder b).1 i ||
        fourSupportContains (fourActualPoint rowOrder c).1 i)) = decide (i < 4)
    rw [show decide (i < 4) = true by exact decide_eq_true hi]
    rw [show i = row.val by rfl,
      fourSupportContains_actualPoint rowOrder hBRows ha row,
      fourSupportContains_actualPoint rowOrder hBRows hb row,
      fourSupportContains_actualPoint rowOrder hBRows hc row]
    rcases hxCases with rfl | rfl | rfl <;> simp [hxRow]
  · have hPower : 16 ≤ 2 ^ i := by
      have hPow : 2 ^ 4 ≤ 2 ^ i :=
        Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at hPow ⊢
      exact hPow
    have hMaskA : fourSupportMask (fourActualPoint rowOrder a).1 < 2 ^ i := by
      apply lt_of_lt_of_le _ hPower
      change (fourActualSupportIndex rowOrder a).val + 1 < 16
      omega
    have hMaskB : fourSupportMask (fourActualPoint rowOrder b).1 < 2 ^ i := by
      apply lt_of_lt_of_le _ hPower
      change (fourActualSupportIndex rowOrder b).val + 1 < 16
      omega
    have hMaskC : fourSupportMask (fourActualPoint rowOrder c).1 < 2 ^ i := by
      apply lt_of_lt_of_le _ hPower
      change (fourActualSupportIndex rowOrder c).val + 1 < 16
      omega
    rw [Nat.testBit_eq_false_of_lt hMaskA,
      Nat.testBit_eq_false_of_lt hMaskB,
      Nat.testBit_eq_false_of_lt hMaskC]
    exact (decide_eq_false_iff_not.mpr hi).symm

theorem fourTriplePointCover_actual_of_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {B : Row α} (hBT : B ∈ blocker T) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hB : B = {a, b, c}) :
    fourTriplePointCover (fourActualPoint rowOrder a)
      (fourActualPoint rowOrder b) (fourActualPoint rowOrder c) = true := by
  have haB : a ∈ B := by simp [hB]
  have hbB : b ∈ B := by simp [hB]
  have hcB : c ∈ B := by simp [hB]
  have ha := fourActualPoint_active_of_mem_blocker hBT haB
  have hb := fourActualPoint_active_of_mem_blocker hBT hbB
  have hc := fourActualPoint_active_of_mem_blocker hBT hcB
  have hMinimal := mem_blocker.mp hBT
  have hPairBC :
      Nat.lor (fourSupportMask (fourActualPoint rowOrder b).1)
        (fourSupportMask (fourActualPoint rowOrder c).1) ≠ 15 := by
    obtain ⟨E, hPrivate⟩ := hMinimal.exists_privateRow haB
    let e : T := ⟨E, hPrivate.1⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    have hRow : (rowOrder row : Row α) = E := by
      simpa [e] using congrArg Subtype.val hrow
    apply fourActualSupportMask_pair_ne_full rowOrder hBRows hb hc row
    · intro hbE
      exact hab (hPrivate.2.2.2 hbB (by simpa [hRow] using hbE)).symm
    · intro hcE
      exact hac (hPrivate.2.2.2 hcB (by simpa [hRow] using hcE)).symm
  have hPairAC :
      Nat.lor (fourSupportMask (fourActualPoint rowOrder a).1)
        (fourSupportMask (fourActualPoint rowOrder c).1) ≠ 15 := by
    obtain ⟨E, hPrivate⟩ := hMinimal.exists_privateRow hbB
    let e : T := ⟨E, hPrivate.1⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    have hRow : (rowOrder row : Row α) = E := by
      simpa [e] using congrArg Subtype.val hrow
    apply fourActualSupportMask_pair_ne_full rowOrder hBRows ha hc row
    · intro haE
      exact hab (hPrivate.2.2.2 haB (by simpa [hRow] using haE))
    · intro hcE
      exact hbc (hPrivate.2.2.2 hcB (by simpa [hRow] using hcE)).symm
  have hPairAB :
      Nat.lor (fourSupportMask (fourActualPoint rowOrder a).1)
        (fourSupportMask (fourActualPoint rowOrder b).1) ≠ 15 := by
    obtain ⟨E, hPrivate⟩ := hMinimal.exists_privateRow hcB
    let e : T := ⟨E, hPrivate.1⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    have hRow : (rowOrder row : Row α) = E := by
      simpa [e] using congrArg Subtype.val hrow
    apply fourActualSupportMask_pair_ne_full rowOrder hBRows ha hb row
    · intro haE
      exact hac (hPrivate.2.2.2 haB (by simpa [hRow] using haE))
    · intro hbE
      exact hbc (hPrivate.2.2.2 hbB (by simpa [hRow] using hbE))
  have hUnion := fourActualSupportMasks_union_eq_full
    rowOrder hBRows hBT hB
  unfold fourTriplePointCover
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨⟨⟨hUnion, hPairBC⟩, hPairAC⟩, hPairAB⟩

theorem fourKernelCompatibleExact_actual_of_threshold {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {A : Row α} (hAT : A ∈ T) {a b c u v w : α}
    (hA : A = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huA : u ∉ A) (hvA : v ∉ A) (hwA : w ∉ A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huActive : u ∈ fourActiveUniverse T)
    (hvActive : v ∈ fourActiveUniverse T)
    (hwActive : w ∈ fourActiveUniverse T)
    (hThreshold :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) ≤
        fourKernelMatchedRows
          (fourActualPoint rowOrder a) (fourActualPoint rowOrder b)
          (fourActualPoint rowOrder c) (fourActualPoint rowOrder u)
          (fourActualPoint rowOrder v) (fourActualPoint rowOrder w) + 3) :
    fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = true := by
  let actual := fourActualSupportMultiplicity rowOrder
  have haA : a ∈ A := by simp [hA]
  have hbA : b ∈ A := by simp [hA]
  have hcA : c ∈ A := by simp [hA]
  have haActive : a ∈ fourActiveUniverse T :=
    mem_fourActiveUniverse.mpr ⟨A, hAT, haA⟩
  have hbActive : b ∈ fourActiveUniverse T :=
    mem_fourActiveUniverse.mpr ⟨A, hAT, hbA⟩
  have hcActive : c ∈ fourActiveUniverse T :=
    mem_fourActiveUniverse.mpr ⟨A, hAT, hcA⟩
  let e : T := ⟨A, hAT⟩
  obtain ⟨row, hrow⟩ := rowOrder.surjective e
  have hRow : (rowOrder row : Row α) = A := by
    simpa [e] using congrArg Subtype.val hrow
  have hRowLength :
      ((fourActivePoints actual).filter fun point =>
        fourSupportContains point.1 row.val).length = 3 := by
    rw [fourActivePoints_filter_length,
      fourRowDegree_actualSupportMultiplicity rowOrder
        (fourRows_actual_support_proper rowOrder hBRows) row,
      hRow, hA]
    simp [hab, hac, hbc]
  have haPoint : fourActualPoint rowOrder a ∈
      (fourActivePoints actual).filter fun point =>
        fourSupportContains point.1 row.val := by
    apply List.mem_filter.mpr
    refine ⟨fourActualPoint_mem_activePoints rowOrder haActive, ?_⟩
    rw [fourSupportContains_actualPoint rowOrder hBRows haActive row]
    exact decide_eq_true (by simpa [hRow] using haA)
  have hbPoint : fourActualPoint rowOrder b ∈
      (fourActivePoints actual).filter fun point =>
        fourSupportContains point.1 row.val := by
    apply List.mem_filter.mpr
    refine ⟨fourActualPoint_mem_activePoints rowOrder hbActive, ?_⟩
    rw [fourSupportContains_actualPoint rowOrder hBRows hbActive row]
    exact decide_eq_true (by simpa [hRow] using hbA)
  have hcPoint : fourActualPoint rowOrder c ∈
      (fourActivePoints actual).filter fun point =>
        fourSupportContains point.1 row.val := by
    apply List.mem_filter.mpr
    refine ⟨fourActualPoint_mem_activePoints rowOrder hcActive, ?_⟩
    rw [fourSupportContains_actualPoint rowOrder hBRows hcActive row]
    exact decide_eq_true (by simpa [hRow] using hcA)
  have huRow : fourSupportContains (fourActualPoint rowOrder u).1 row.val = false := by
    rw [fourSupportContains_actualPoint rowOrder hBRows huActive row]
    apply decide_eq_false_iff_not.mpr
    simpa [hRow] using huA
  have hvRow : fourSupportContains (fourActualPoint rowOrder v).1 row.val = false := by
    rw [fourSupportContains_actualPoint rowOrder hBRows hvActive row]
    apply decide_eq_false_iff_not.mpr
    simpa [hRow] using hvA
  have hwRow : fourSupportContains (fourActualPoint rowOrder w).1 row.val = false := by
    rw [fourSupportContains_actualPoint rowOrder hBRows hwActive row]
    apply decide_eq_false_iff_not.mpr
    simpa [hRow] using hwA
  have hPointAB : fourActualPoint rowOrder a ≠ fourActualPoint rowOrder b := by
    intro hPoints
    exact hab (fourActualPoint_injective_on_active rowOrder haActive hbActive hPoints)
  have hPointAC : fourActualPoint rowOrder a ≠ fourActualPoint rowOrder c := by
    intro hPoints
    exact hac (fourActualPoint_injective_on_active rowOrder haActive hcActive hPoints)
  have hPointBC : fourActualPoint rowOrder b ≠ fourActualPoint rowOrder c := by
    intro hPoints
    exact hbc (fourActualPoint_injective_on_active rowOrder hbActive hcActive hPoints)
  have hPointUV : fourActualPoint rowOrder u ≠ fourActualPoint rowOrder v := by
    intro hPoints
    exact huv (fourActualPoint_injective_on_active rowOrder huActive hvActive hPoints)
  have hPointUW : fourActualPoint rowOrder u ≠ fourActualPoint rowOrder w := by
    intro hPoints
    exact huw (fourActualPoint_injective_on_active rowOrder huActive hwActive hPoints)
  have hPointVW : fourActualPoint rowOrder v ≠ fourActualPoint rowOrder w := by
    intro hPoints
    exact hvw (fourActualPoint_injective_on_active rowOrder hvActive hwActive hPoints)
  apply fourKernelCompatibleExact_of_threshold_witness actual row.val
    (fourActualPoint rowOrder a) (fourActualPoint rowOrder b)
    (fourActualPoint rowOrder c) (fourActualPoint rowOrder u)
    (fourActualPoint rowOrder v) (fourActualPoint rowOrder w)
  · exact row.isLt
  · exact hRowLength
  · exact haPoint
  · exact hbPoint
  · exact hcPoint
  · exact hPointAB
  · exact hPointAC
  · exact hPointBC
  · exact fourActualPoint_mem_activePoints rowOrder huActive
  · exact fourActualPoint_mem_activePoints rowOrder hvActive
  · exact fourActualPoint_mem_activePoints rowOrder hwActive
  · exact huRow
  · exact hvRow
  · exact hwRow
  · exact hPointUV
  · exact hPointUW
  · exact hPointVW
  · exact hThreshold

theorem fourKernelCompatibleExact_actual_of_kernel {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {A : Row α} (hAT : A ∈ T) {a b c u v w : α}
    (hA : A = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huA : u ∉ A) (hvA : v ∉ A) (hwA : w ∉ A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hAUV : ({a, u, v} : Row α) ∈ blocker T)
    (hBUW : ({b, u, w} : Row α) ∈ blocker T)
    (hCVW : ({c, v, w} : Row α) ∈ blocker T)
    (hBCard : (blocker T).card ≤ 6) :
    fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = true := by
  have haA : a ∈ A := by simp [hA]
  have hbA : b ∈ A := by simp [hA]
  have hcA : c ∈ A := by simp [hA]
  have huActive : u ∈ fourActiveUniverse T :=
    fourActualPoint_active_of_mem_blocker hAUV (by simp)
  have hvActive : v ∈ fourActiveUniverse T :=
    fourActualPoint_active_of_mem_blocker hAUV (by simp)
  have hwActive : w ∈ fourActiveUniverse T :=
    fourActualPoint_active_of_mem_blocker hBUW (by simp)
  have hau : a ≠ u := fun hau => huA (hau ▸ haA)
  have hav : a ≠ v := fun hav => hvA (hav ▸ haA)
  have hbu : b ≠ u := fun hbu => huA (hbu ▸ hbA)
  have hbw : b ≠ w := fun hbw => hwA (hbw ▸ hbA)
  have hcv : c ≠ v := fun hcv => hvA (hcv ▸ hcA)
  have hcw : c ≠ w := fun hcw => hwA (hcw ▸ hcA)
  have hTripleA := fourTriplePointCover_actual_of_blocker rowOrder hBRows
    hAUV hau hav huv rfl
  have hTripleB := fourTriplePointCover_actual_of_blocker rowOrder hBRows
    hBUW hbu hbw huw rfl
  have hTripleC := fourTriplePointCover_actual_of_blocker rowOrder hBRows
    hCVW hcv hcw hvw rfl
  have hThreshold :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) ≤
        fourKernelMatchedRows
          (fourActualPoint rowOrder a) (fourActualPoint rowOrder b)
          (fourActualPoint rowOrder c) (fourActualPoint rowOrder u)
          (fourActualPoint rowOrder v) (fourActualPoint rowOrder w) + 3 := by
    have hWeighted :=
      (fourWeightedCoverCount_le_blocker_card rowOrder hBRows).trans hBCard
    simpa [fourKernelMatchedRows, hTripleA, hTripleB, hTripleC] using hWeighted
  exact fourKernelCompatibleExact_actual_of_threshold rowOrder hBRows hAT hA
    hab hac hbc huA hvA hwA huv huw hvw huActive hvActive hwActive hThreshold

theorem inter_three_card_eq_indicator_sum {α : Type*} [DecidableEq α]
    (R : Finset (Finset α)) (D₁ D₂ D₃ : Finset α)
    (h₁₂ : D₁ ≠ D₂) (h₁₃ : D₁ ≠ D₃) (h₂₃ : D₂ ≠ D₃) :
    (R ∩ {D₁, D₂, D₃}).card =
      (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
        (if D₃ ∈ R then 1 else 0) := by
  by_cases h₁ : D₁ ∈ R <;> by_cases h₂ : D₂ ∈ R <;>
    by_cases h₃ : D₃ ∈ R <;> simp [h₁, h₂, h₃, h₁₂, h₁₃, h₂₃]

theorem fourKernelCompatibleExact_actual_of_budget {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {A : Row α} (hAT : A ∈ T) {a b c u v w : α}
    (hA : A = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huA : u ∉ A) (hvA : v ∉ A) (hwA : w ∉ A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huActive : u ∈ fourActiveUniverse T)
    (hvActive : v ∈ fourActiveUniverse T)
    (hwActive : w ∈ fourActiveUniverse T)
    (hD₁D₂ : ({a, u, v} : Row α) ≠ {b, u, w})
    (hD₁D₃ : ({a, u, v} : Row α) ≠ {c, v, w})
    (hD₂D₃ : ({b, u, w} : Row α) ≠ {c, v, w})
    (extra : G413.Hypergraph α)
    (hBlockerSubset : blocker T ⊆
      insert ({a, u, v} : Row α)
        (insert ({b, u, w} : Row α)
          (insert ({c, v, w} : Row α) extra)))
    (hExtraCard : extra.card ≤ 3) :
    fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = true := by
  let R := blocker T
  let D₁ : Row α := {a, u, v}
  let D₂ : Row α := {b, u, w}
  let D₃ : Row α := {c, v, w}
  let D : G413.Hypergraph α := {D₁, D₂, D₃}
  have hRetainedSubset : R ⊆ (R ∩ D) ∪ extra := by
    intro E hER
    have hCases := hBlockerSubset hER
    simp only [Finset.mem_insert] at hCases
    rcases hCases with hED₁ | hED₂ | hED₃ | hEExtra
    · subst E
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hER, by simp [D, D₁]⟩)
    · subst E
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hER, by simp [D, D₂]⟩)
    · subst E
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hER, by simp [D, D₃]⟩)
    · exact Finset.mem_union_right _ hEExtra
  have hRetainedCard :
      (R ∩ D).card =
        (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
          (if D₃ ∈ R then 1 else 0) := by
    exact inter_three_card_eq_indicator_sum R D₁ D₂ D₃
      (by simpa [D₁, D₂] using hD₁D₂)
      (by simpa [D₁, D₃] using hD₁D₃)
      (by simpa [D₂, D₃] using hD₂D₃)
  have hCardBudget :
      R.card ≤
        (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
          (if D₃ ∈ R then 1 else 0) + 3 := by
    calc
      R.card ≤ ((R ∩ D) ∪ extra).card := Finset.card_le_card hRetainedSubset
      _ ≤ (R ∩ D).card + extra.card := Finset.card_union_le _ _
      _ ≤ (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
          (if D₃ ∈ R then 1 else 0) + 3 := by rw [hRetainedCard]; omega
  have haA : a ∈ A := by simp [hA]
  have hbA : b ∈ A := by simp [hA]
  have hcA : c ∈ A := by simp [hA]
  have hau : a ≠ u := fun hau => huA (hau ▸ haA)
  have hav : a ≠ v := fun hav => hvA (hav ▸ haA)
  have hbu : b ≠ u := fun hbu => huA (hbu ▸ hbA)
  have hbw : b ≠ w := fun hbw => hwA (hbw ▸ hbA)
  have hcv : c ≠ v := fun hcv => hvA (hcv ▸ hcA)
  have hcw : c ≠ w := fun hcw => hwA (hcw ▸ hcA)
  have hMatch₁ :
      (if D₁ ∈ R then 1 else 0) ≤
        if fourTriplePointCover (fourActualPoint rowOrder a)
          (fourActualPoint rowOrder u) (fourActualPoint rowOrder v) then 1 else 0 := by
    by_cases hD₁ : D₁ ∈ R
    · have hTriple := fourTriplePointCover_actual_of_blocker rowOrder hBRows
        (by simpa [R, D₁] using hD₁) hau hav huv rfl
      simp [hD₁, hTriple]
    · simp [hD₁]
  have hMatch₂ :
      (if D₂ ∈ R then 1 else 0) ≤
        if fourTriplePointCover (fourActualPoint rowOrder b)
          (fourActualPoint rowOrder u) (fourActualPoint rowOrder w) then 1 else 0 := by
    by_cases hD₂ : D₂ ∈ R
    · have hTriple := fourTriplePointCover_actual_of_blocker rowOrder hBRows
        (by simpa [R, D₂] using hD₂) hbu hbw huw rfl
      simp [hD₂, hTriple]
    · simp [hD₂]
  have hMatch₃ :
      (if D₃ ∈ R then 1 else 0) ≤
        if fourTriplePointCover (fourActualPoint rowOrder c)
          (fourActualPoint rowOrder v) (fourActualPoint rowOrder w) then 1 else 0 := by
    by_cases hD₃ : D₃ ∈ R
    · have hTriple := fourTriplePointCover_actual_of_blocker rowOrder hBRows
        (by simpa [R, D₃] using hD₃) hcv hcw hvw rfl
      simp [hD₃, hTriple]
    · simp [hD₃]
  have hThreshold :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) ≤
        fourKernelMatchedRows
          (fourActualPoint rowOrder a) (fourActualPoint rowOrder b)
          (fourActualPoint rowOrder c) (fourActualPoint rowOrder u)
          (fourActualPoint rowOrder v) (fourActualPoint rowOrder w) + 3 := by
    calc
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) ≤ R.card := by
        exact fourWeightedCoverCount_le_blocker_card rowOrder hBRows
      _ ≤ (if D₁ ∈ R then 1 else 0) + (if D₂ ∈ R then 1 else 0) +
          (if D₃ ∈ R then 1 else 0) + 3 := hCardBudget
      _ ≤ fourKernelMatchedRows
          (fourActualPoint rowOrder a) (fourActualPoint rowOrder b)
          (fourActualPoint rowOrder c) (fourActualPoint rowOrder u)
          (fourActualPoint rowOrder v) (fourActualPoint rowOrder w) + 3 := by
        unfold fourKernelMatchedRows
        omega
  exact fourKernelCompatibleExact_actual_of_threshold rowOrder hBRows hAT hA
    hab hac hbc huA hvA hwA huv huw hvw huActive hvActive hwActive hThreshold

end AiMathLab.P0054.G419
