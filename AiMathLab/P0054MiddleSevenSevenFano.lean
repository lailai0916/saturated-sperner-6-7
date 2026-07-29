import AiMathLab.P0054MiddleSevenSeven

/-!
# The Fano equality case for seven mutual blockers

The `K₄` deletion kernel reconstructs a seven-row Fano clutter.  Equal
cardinalities then identify the reconstructed clutter with both blocker sides.
-/

namespace AiMathLab.P0054.MiddleSevenSevenFano

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.FanoStep
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.MiddleSevenSeven

theorem k4_kernel_is_fano {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHRows : RowsCardAtLeast H 3)
    (hBCard : (blocker H).card = 7)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMax : MaxDegreeAtMost (blocker H) 3)
    (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hValues :
      (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values) :
    H = blocker H ∧
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card = 1) ∧
      ∃ pointMap : alpha → MiddleFourModelPoint,
        Set.InjOn pointMap (H.biUnion id) ∧
        sevenEightFanoBase =
          H.image (fun row ↦ row.image pointMap) := by
  classical
  let K := avoidPoint H x
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    exact hHRows row (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hKUpper : ∀ row ∈ K, row.card ≤ 8 := by
    intro row hRow
    have hRowH : row ∈ H :=
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
    have hRowDouble : row ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hRowH
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hRowDouble)
    omega
  have hBKUpper : (blocker K).card ≤ 8 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    have : (blocker K).card ≤ 7 := by simpa [K, hBCard] using hLift
    omega
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 3 := hBMax x
  have hLength :
      (fourActivePoints
        (fourActualSupportMultiplicity rowOrder)).length < 16 :=
    middleFourActualPoints_length_lt_sixteen rowOrder hKClutter hBKRows
      hKRows hKUpper hBKUpper (hPairUpper.trans (by omega))
  have hPairLength :
      (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).length = 3 := by
    rw [hValues]
    decide
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hBRows hBKRows hLength (hBMax x)
  have hSelectionEmpty : middleFourSemanticSelected H x rowOrder = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have hModelCard :
      (middleFourModelBlocker
        (fourActualSupportMultiplicity rowOrder).toList).card =
        (blocker K).card :=
    middleFourModelBlocker_card_eq_actual rowOrder hBKRows hLength
  have hModelSeven :
      (middleFourModelBlocker
        (fourActualSupportMultiplicity rowOrder).toList).card = 7 := by
    rw [hValues]
    decide
  have hBKCard : (blocker K).card = 7 := by omega
  let lifted := middleFourSemanticLiftFamily H x
  let pointMap := middleFourBasePoint rowOrder x
  let domain := insert x (fourActiveUniverse K)
  have hLiftedSubset : lifted ⊆ blocker H := by
    simpa [lifted] using middleFourSemanticLiftFamily_subset_blocker H x
  have hLiftedCard : lifted.card = 7 := by
    simpa [lifted, K, hBKCard] using middleFourSemanticLiftFamily_card H x
  have hLiftedDomain : lifted.biUnion id ⊆ domain := by
    intro point hPoint
    obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
    have hRow' := hRow
    change row ∈ (blocker (avoidPoint H x)).image (avoidBlockerLift H x) at hRow'
    obtain ⟨source, hSource, hSourceEq⟩ := Finset.mem_image.mp hRow'
    rw [← hSourceEq] at hPointRow
    simpa [domain, K] using
      middleFourAvoidBlockerLift_subset_active_insert H x hSource hPointRow
  have hPointInj : Set.InjOn pointMap domain := by
    simpa [pointMap, domain, K] using
      middleFourBasePoint_injOn_active_insert H x rowOrder hLength
  have hBaseSet : sevenEightFanoBase =
      lifted.image (fun row ↦ row.image pointMap) := by
    have hSemantic := middleFourSemanticLiftBaseRows_toFinset
      H x rowOrder hBRows hBKRows hLength
    have hZeroBase :
        (middleFourModelLiftBaseRows
          (fourActualSupportMultiplicity rowOrder).toList
          (middleFourSemanticSelected H x rowOrder)).toFinset =
          sevenEightFanoBase := by
      rw [hValues, hSelectionEmpty]
      simpa [sevenEightFanoBase, sevenEightZeroBase] using
        congrArg List.toFinset sevenEight_k4_zero_base
    rw [hZeroBase] at hSemantic
    calc
      sevenEightFanoBase =
          (blocker (avoidPoint H x)).image (fun row ↦
            (avoidBlockerLift H x row).image pointMap) := by
        simpa [pointMap] using hSemantic
      _ = lifted.image (fun row ↦ row.image pointMap) := by
        change
          (blocker (avoidPoint H x)).image (fun row ↦
              (avoidBlockerLift H x row).image pointMap) =
            ((blocker (avoidPoint H x)).image (avoidBlockerLift H x)).image
              (fun row ↦ row.image pointMap)
        rw [Finset.image_image]
        rfl
  have hLiftedRows : ∀ E ∈ lifted, E.card = 3 := by
    intro E hE
    have hImageMember : E.image pointMap ∈ sevenEightFanoBase := by
      rw [hBaseSet]
      exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
    have hImageCard : (E.image pointMap).card = E.card := by
      apply Finset.card_image_iff.mpr
      exact hPointInj.mono (fun point hPoint ↦ hLiftedDomain
        (Finset.mem_biUnion.mpr ⟨E, hE, hPoint⟩))
    rw [← hImageCard]
    exact sevenEight_fano_rows _ hImageMember
  have hRowMapInj : Set.InjOn
      (fun row : G413.Row alpha ↦ row.image pointMap) lifted :=
    row_image_injOn_of_injOn hLiftedDomain hPointInj
  have hLiftedPairs : ∀ E ∈ lifted, ∀ F ∈ lifted,
      E ≠ F → (E ∩ F).card = 1 := by
    intro E hE F hF hEF
    have hEImage : E.image pointMap ∈ sevenEightFanoBase := by
      rw [hBaseSet]
      exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
    have hFImage : F.image pointMap ∈ sevenEightFanoBase := by
      rw [hBaseSet]
      exact Finset.mem_image.mpr ⟨F, hF, rfl⟩
    have hImageNe : E.image pointMap ≠ F.image pointMap := by
      intro hEq
      exact hEF (hRowMapInj hE hF hEq)
    have hImageInter : (E ∩ F).image pointMap =
        E.image pointMap ∩ F.image pointMap := by
      ext modelPoint
      constructor
      · intro hPoint
        obtain ⟨point, hPointInter, rfl⟩ := Finset.mem_image.mp hPoint
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr
              ⟨point, (Finset.mem_inter.mp hPointInter).1, rfl⟩,
            Finset.mem_image.mpr
              ⟨point, (Finset.mem_inter.mp hPointInter).2, rfl⟩⟩
      · intro hPoint
        obtain ⟨hPointE, hPointF⟩ := Finset.mem_inter.mp hPoint
        obtain ⟨left, hLeftE, hLeftEq⟩ := Finset.mem_image.mp hPointE
        obtain ⟨right, hRightF, hRightEq⟩ := Finset.mem_image.mp hPointF
        have hLeftDomain := hLiftedDomain
          (Finset.mem_biUnion.mpr ⟨E, hE, hLeftE⟩)
        have hRightDomain := hLiftedDomain
          (Finset.mem_biUnion.mpr ⟨F, hF, hRightF⟩)
        have hLeftRight : left = right :=
          hPointInj hLeftDomain hRightDomain (hLeftEq.trans hRightEq.symm)
        subst right
        exact Finset.mem_image.mpr
          ⟨left, Finset.mem_inter.mpr ⟨hLeftE, hRightF⟩, hLeftEq⟩
    have hInterCard : ((E ∩ F).image pointMap).card = (E ∩ F).card := by
      apply Finset.card_image_iff.mpr
      exact hPointInj.mono (fun point hPoint ↦ hLiftedDomain
        (Finset.mem_biUnion.mpr
          ⟨E, hE, (Finset.mem_inter.mp hPoint).1⟩))
    rw [← hInterCard, hImageInter]
    exact sevenEight_fano_pairs _ hEImage _ hFImage hImageNe
  have hPointInjActive : Set.InjOn pointMap (lifted.biUnion id) :=
    hPointInj.mono hLiftedDomain
  have hImageBlocker :
      blocker (lifted.image fun row ↦ row.image pointMap) =
        (blocker lifted).image fun row ↦ row.image pointMap :=
    blocker_image_eq_of_injOn_active hPointInjActive
  have hBlockerImages :
      (blocker lifted).image (fun row ↦ row.image pointMap) =
        lifted.image (fun row ↦ row.image pointMap) := by
    rw [← hImageBlocker, ← hBaseSet, sevenEight_fano_self_blocker, hBaseSet]
  have hLiftedSelf : blocker lifted = lifted := by
    ext E
    constructor
    · intro hE
      have hImage : E.image pointMap ∈
          lifted.image (fun row ↦ row.image pointMap) := by
        rw [← hBlockerImages]
        exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
      obtain ⟨F, hF, hImageEq⟩ := Finset.mem_image.mp hImage
      have hEDomain : E ⊆ lifted.biUnion id := blocker_row_subset_biUnion hE
      have hFDomain : F ⊆ lifted.biUnion id := fun point hPoint ↦
        Finset.mem_biUnion.mpr ⟨F, hF, hPoint⟩
      have hEF : E = F := by
        ext point
        constructor
        · intro hPoint
          have hMapped : pointMap point ∈ F.image pointMap := by
            rw [hImageEq]
            exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
          obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hMapped
          exact (hPointInjActive (hFDomain hOther) (hEDomain hPoint)
            hOtherEq) ▸ hOther
        · intro hPoint
          have hMapped : pointMap point ∈ E.image pointMap := by
            rw [← hImageEq]
            exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
          obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hMapped
          exact (hPointInjActive (hEDomain hOther) (hFDomain hPoint)
            hOtherEq) ▸ hOther
      simpa [hEF] using hF
    · intro hE
      have hImage : E.image pointMap ∈
          (blocker lifted).image (fun row ↦ row.image pointMap) := by
        rw [hBlockerImages]
        exact Finset.mem_image.mpr ⟨E, hE, rfl⟩
      obtain ⟨F, hF, hImageEq⟩ := Finset.mem_image.mp hImage
      have hFDomain : F ⊆ lifted.biUnion id := blocker_row_subset_biUnion hF
      have hEDomain : E ⊆ lifted.biUnion id := fun point hPoint ↦
        Finset.mem_biUnion.mpr ⟨E, hE, hPoint⟩
      have hFE : F = E := by
        ext point
        constructor
        · intro hPoint
          have hMapped : pointMap point ∈ E.image pointMap := by
            rw [← hImageEq]
            exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
          obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hMapped
          exact (hPointInjActive (hEDomain hOther) (hFDomain hPoint)
            hOtherEq) ▸ hOther
        · intro hPoint
          have hMapped : pointMap point ∈ F.image pointMap := by
            rw [hImageEq]
            exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
          obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hMapped
          exact (hPointInjActive (hFDomain hOther) (hEDomain hPoint)
            hOtherEq) ▸ hOther
      simpa [hFE] using hF
  have hLiftedEq : lifted = blocker H :=
    Finset.eq_of_subset_of_card_le hLiftedSubset (by
      rw [hLiftedCard, hBCard])
  have hHEq : H = lifted := by
    calc
      H = blocker (blocker H) := (blocker_involution hHClutter).symm
      _ = blocker lifted := by rw [hLiftedEq]
      _ = lifted := hLiftedSelf
  refine ⟨hHEq.trans hLiftedEq, ?_, ?_, ?_⟩
  · intro E hEH
    apply hLiftedRows E
    rw [← hHEq]
    exact hEH
  · intro E hEH F hFH hEF
    apply hLiftedPairs E
    · rw [← hHEq]
      exact hEH
    · rw [← hHEq]
      exact hFH
    · exact hEF
  · refine ⟨pointMap, ?_, ?_⟩
    · rw [hHEq]
      exact hPointInjActive
    · rw [hHEq]
      exact hBaseSet

theorem sevenSeven_is_fano {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    H = blocker H ∧
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card = 1) ∧
      ∃ pointMap : alpha → MiddleFourModelPoint,
        Set.InjOn pointMap (H.biUnion id) ∧
        sevenEightFanoBase =
          H.image (fun row ↦ row.image pointMap) := by
  classical
  have hHMax := sevenSeven_maxDegreeAtMost_three
    hHClutter hHCard hHRows hBRows hBCard
  have hDualClutter : IsClutter (blocker H) := blocker_isClutter H
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualCard : (blocker (blocker H)).card = 7 := by
    simpa [blocker_involution hHClutter] using hHCard
  have hBMax := sevenSeven_maxDegreeAtMost_three
    hDualClutter hBCard hBRows hDualRows hDualCard
  have hDoubleMax : MaxDegreeAtMost (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHMax
  rcases sevenSeven_has_k4_kernel hHClutter hHCard hHRows hBRows hBCard with
      ⟨x, -, rowOrder, hValues⟩ |
      ⟨x, -, rowOrder, hValues⟩
  · exact k4_kernel_is_fano hHClutter hHRows hBCard hBRows
      hBMax x rowOrder hValues
  · obtain ⟨hDualSelf, hDualFanoRows, hDualFanoPairs, hDualModel⟩ :=
      k4_kernel_is_fano hDualClutter hBRows hDualCard hDualRows
        hDoubleMax x rowOrder hValues
    have hSelf : H = blocker H := by
      simpa [blocker_involution hHClutter] using hDualSelf.symm
    refine ⟨hSelf, ?_, ?_, ?_⟩
    · intro E hEH
      apply hDualFanoRows E
      rw [← hSelf]
      exact hEH
    · intro E hEH F hFH hEF
      apply hDualFanoPairs E
      · rw [← hSelf]
        exact hEH
      · rw [← hSelf]
        exact hFH
      · exact hEF
    · rw [hSelf]
      exact hDualModel

end AiMathLab.P0054.MiddleSevenSevenFano
