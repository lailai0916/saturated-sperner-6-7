import AiMathLab.P0054MiddleSevenNineExtension.Check
import AiMathLab.P0054MiddleSevenNineFourActual
import AiMathLab.P0054MiddleSevenNineDegree

/-!
# Semantic bridge for the non-`K₄` 7+9 four-row kernels

The finite checker is applied only after an arbitrary finite kernel has been
encoded by exact incidence-support multiplicities.  The nine-row case has no
extra row; the eight-row case has one extra row whose old and fresh points are
mapped injectively into the finite model.
-/

namespace AiMathLab.P0054.MiddleSevenNineExtension

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightDegree
open AiMathLab.P0054.MiddleSevenNineFinite
open AiMathLab.P0054.MiddleSevenNineExtensionFinite

theorem sevenNineExtensionActualCheck {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    sevenNineExtensionValuesCheck
        (fourActualSupportMultiplicity rowOrder).toList = true := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold MiddleSevenNineFinite.middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  rw [hList]
  have hAll : MiddleSevenNineFinite.middleFourMultiplicityCertificate.all
      sevenNineExtensionValuesCheck = true := by
    simpa [sevenNineExtensionCertificateCheck] using
      sevenNineExtensionCertificateCheck_true
  exact List.all_eq_true.mp hAll values hValues

theorem liftFamily_exists_unique_extra {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    {liftCard blockerCard : Nat}
    (hLiftCard : (blocker (avoidPoint H x)).card = liftCard)
    (hBlockerCard : (blocker H).card = blockerCard)
    (hNext : blockerCard = liftCard + 1) :
    ∃ extra ∈ blocker H,
      extra ∉ middleFourSemanticLiftFamily H x ∧
        blocker H = insert extra (middleFourSemanticLiftFamily H x) := by
  have hFamilyCard : (middleFourSemanticLiftFamily H x).card = liftCard := by
    rw [middleFourSemanticLiftFamily_card, hLiftCard]
  obtain ⟨extra, hExtraBlocker, hExtraNotFamily⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := middleFourSemanticLiftFamily H x) (t := blocker H) (by omega)
  refine ⟨extra, hExtraBlocker, hExtraNotFamily, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro row hRow
    rcases Finset.mem_insert.mp hRow with rfl | hRow
    · exact hExtraBlocker
    · exact middleFourSemanticLiftFamily_subset_blocker H x hRow
  · rw [Finset.card_insert_of_notMem hExtraNotFamily,
      hFamilyCard, hBlockerCard]
    omega

theorem modelMaxDegreeAtMostFour_of_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (rows : List (G413.Row MiddleFourModelPoint))
    {family : G413.Hypergraph alpha} {domain : Finset alpha}
    (pointMap : alpha → MiddleFourModelPoint)
    (hRows : rows.toFinset =
      family.image fun row ↦ row.image pointMap)
    (hFamilyDomain : family.biUnion id ⊆ domain)
    (hPointMap : Set.InjOn pointMap domain)
    (hMaxDegree : MaxDegreeAtMost family 4) :
    sevenNineModelMaxDegreeAtMostFour rows = true := by
  rw [sevenNineModelMaxDegreeAtMostFour, List.all_eq_true]
  intro modelPoint _hModelPoint
  apply decide_eq_true
  by_cases hActive : modelPoint ∈ rows.toFinset.biUnion id
  · rw [hRows] at hActive
    obtain ⟨imageRow, hImageRow, hModelImage⟩ :=
      Finset.mem_biUnion.mp hActive
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
    obtain ⟨point, hPointSource, hPointEq⟩ :=
      Finset.mem_image.mp hModelImage
    have hPointDomain : point ∈ domain :=
      hFamilyDomain (Finset.mem_biUnion.mpr
        ⟨source, hSource, hPointSource⟩)
    rw [← hPointEq, hRows,
      degree_image_eq_of_injOn hPointDomain hFamilyDomain hPointMap]
    exact hMaxDegree point
  · have hFilter : rows.toFinset.filter
        (fun row ↦ modelPoint ∈ row) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro row hRow
      apply hActive
      exact Finset.mem_biUnion.mpr
        ⟨row, (Finset.mem_filter.mp hRow).1,
          (Finset.mem_filter.mp hRow).2⟩
    simp [degree, hFilter]

theorem modelRowsCardBetweenThreeAndSeven_of_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (rows : List (G413.Row MiddleFourModelPoint))
    {family : G413.Hypergraph alpha} {domain : Finset alpha}
    (pointMap : alpha → MiddleFourModelPoint)
    (hRows : rows.toFinset =
      family.image fun row ↦ row.image pointMap)
    (hFamilyDomain : family.biUnion id ⊆ domain)
    (hPointMap : Set.InjOn pointMap domain)
    (hFamilyRows : RowsCardAtLeast family 3)
    (hFamilyUpper : ∀ row ∈ family, row.card ≤ 7) :
    sevenNineModelRowsCardBetweenThreeAndSeven rows = true := by
  rw [sevenNineModelRowsCardBetweenThreeAndSeven, List.all_eq_true]
  intro imageRow hImageRow
  have hImageRowSet : imageRow ∈ rows.toFinset :=
    List.mem_toFinset.mpr hImageRow
  rw [hRows] at hImageRowSet
  obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRowSet
  have hSourceDomain : source ⊆ domain := by
    intro point hPoint
    exact hFamilyDomain (Finset.mem_biUnion.mpr ⟨source, hSource, hPoint⟩)
  apply decide_eq_true
  rw [Finset.card_image_iff.mpr (hPointMap.mono hSourceDomain)]
  exact ⟨hFamilyRows source hSource, hFamilyUpper source hSource⟩

theorem sevenNineModelCandidateCheck_ne_true_of_valid
    (rows : List (G413.Row MiddleFourModelPoint))
    (hRows : sevenNineModelRowsCardBetweenThreeAndSeven rows = true)
    (hCard : rows.toFinset.card = 9)
    (hMax : sevenNineModelMaxDegreeAtMostFour rows = true)
    (hBlockerCard : (blocker rows.toFinset).card = 7) :
    sevenNineModelCandidateCheck rows ≠ true := by
  intro hCheck
  unfold sevenNineModelCandidateCheck at hCheck
  simp only [hRows, Bool.not_true, Bool.false_or] at hCheck
  rw [if_pos hCard, hMax] at hCheck
  have hNe : (fastBlocker rows).card ≠ 7 := of_decide_eq_true hCheck
  rw [fastBlocker_eq_blocker, hBlockerCard] at hNe
  exact hNe rfl

theorem base_mem_candidates_of_card_nine
    (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint))
    (hSelection : selected ∈ middleFourModelLiftSelectionRows values)
    (hCard : (middleFourModelLiftBaseRows values selected).toFinset.card = 9) :
    middleFourModelLiftBaseRows values selected ∈
      sevenNineModelCandidateRows values := by
  unfold sevenNineModelCandidateRows
  apply List.mem_flatMap.mpr
  refine ⟨selected, hSelection, ?_⟩
  unfold sevenNineModelCandidateRowsForSelection
  rw [if_pos hCard]
  simp

theorem extra_mem_candidates_of_card_eight
    (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint))
    (extra : G413.Row MiddleFourModelPoint)
    (hSelection : selected ∈ middleFourModelLiftSelectionRows values)
    (hCard : (middleFourModelLiftBaseRows values selected).toFinset.card = 8)
    (hExtra : extra ∈ middleFourModelExtraRowList values
      (middleFourModelLiftBaseRows values selected)) :
    extra :: middleFourModelLiftBaseRows values selected ∈
      sevenNineModelCandidateRows values := by
  unfold sevenNineModelCandidateRows
  apply List.mem_flatMap.mpr
  refine ⟨selected, hSelection, ?_⟩
  unfold sevenNineModelCandidateRowsForSelection
  rw [if_neg (by omega), if_pos hCard]
  exact List.mem_map.mpr ⟨extra, hExtra, rfl⟩

set_option maxHeartbeats 3000000 in
theorem blocker_card_nine_contradicts_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 9)
    (hHBlockerCard : (blocker H).card = 9)
    (hHCard : H.card = 7)
    (hMaxDegree : MaxDegreeAtMost (blocker H) 4)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hCheck : sevenNineExtensionValuesCheck
      (fourActualSupportMultiplicity rowOrder).toList = true) : False := by
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let selected := middleFourSemanticSelected H x rowOrder
  let base := middleFourModelLiftBaseRows values selected
  let pointMap := middleFourBasePoint rowOrder x
  have hBaseCard : base.toFinset.card = 9 := by
    calc
      base.toFinset.card = (blocker (avoidPoint H x)).card := by
        simpa [base, values, selected] using middleFourSemanticLiftBaseRows_card
          H x rowOrder hHBlockerRows hBRows hLength
      _ = 9 := hAvoidBlockerCard
  have hValuesCheck : sevenNineExtensionValuesCheck values = true := by
    simpa [values] using hCheck
  unfold sevenNineExtensionValuesCheck at hValuesCheck
  have hSelectionCheck := (List.all_eq_true.mp hValuesCheck) selected
    (by simpa [values, selected] using hSelection)
  unfold sevenNineModelSelectionCheck at hSelectionCheck
  rw [if_pos hBaseCard] at hSelectionCheck
  have hLiftEq : middleFourSemanticLiftFamily H x = blocker H :=
    middleFourSemanticLiftFamily_eq_blocker_of_card_eq H x
      (hAvoidBlockerCard.trans hHBlockerCard.symm)
  have hActiveSubset : (blocker H).biUnion id ⊆
      insert x (fourActiveUniverse (avoidPoint H x)) := by
    intro point hPoint
    obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
    rw [← hLiftEq] at hRow
    obtain ⟨source, hSource, hSourceLift⟩ := Finset.mem_image.mp hRow
    rw [← hSourceLift] at hPointRow
    exact middleFourAvoidBlockerLift_subset_active_insert
      H x hSource hPointRow
  have hPointMap : Set.InjOn pointMap ((blocker H).biUnion id) :=
    (middleFourBasePoint_injOn_active_insert H x rowOrder hLength).mono
      hActiveSubset
  have hBaseSet : base.toFinset =
      (blocker H).image fun row ↦ row.image pointMap := by
    calc
      base.toFinset = (blocker (avoidPoint H x)).image (fun row ↦
          (avoidBlockerLift H x row).image pointMap) := by
        simpa [base, values, selected, pointMap] using
          middleFourSemanticLiftBaseRows_toFinset
            H x rowOrder hHBlockerRows hBRows hLength
      _ = (middleFourSemanticLiftFamily H x).image
          (fun row ↦ row.image pointMap) := by
        rw [middleFourSemanticLiftFamily, Finset.image_image]
        rfl
      _ = (blocker H).image (fun row ↦ row.image pointMap) := by rw [hLiftEq]
  have hModelMax : sevenNineModelMaxDegreeAtMostFour base = true :=
    modelMaxDegreeAtMostFour_of_image base pointMap hBaseSet
      (fun _ hPoint ↦ hPoint) hPointMap hMaxDegree
  have hModelRows : sevenNineModelRowsCardBetweenThreeAndSeven base = true :=
    modelRowsCardBetweenThreeAndSeven_of_image base pointMap hBaseSet
      (fun _ hPoint ↦ hPoint) hPointMap hHBlockerRows
      (fun _ hRow ↦ (minimalTransversal_card_le_rows
        (mem_blocker.mp hRow)).trans_eq hHCard)
  have hCandidateCheck : sevenNineModelCandidateCheck base = true :=
    hSelectionCheck
  have hBaseBlockerCard : (blocker base.toFinset).card = 7 := by
    calc
      (blocker base.toFinset).card = H.card := by
        change (blocker (middleFourModelLiftBaseRows
          (fourActualSupportMultiplicity rowOrder).toList
          (middleFourSemanticSelected H x rowOrder)).toFinset).card = H.card
        exact semanticLiftBase_blocker_card_eq_family x rowOrder hHClutter
          hHBlockerRows hBRows hLength
            (hAvoidBlockerCard.trans hHBlockerCard.symm)
      _ = 7 := hHCard
  exact sevenNineModelCandidateCheck_ne_true_of_valid base hModelRows
    hBaseCard hModelMax hBaseBlockerCard hCandidateCheck

set_option maxHeartbeats 3000000 in
theorem blocker_card_eight_contradicts_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hHBlockerCard : (blocker H).card = 9)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLengthLeEight : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length ≤ 8)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 8)
    (hMaxDegree : MaxDegreeAtMost (blocker H) 4)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hCheck : sevenNineExtensionValuesCheck
      (fourActualSupportMultiplicity rowOrder).toList = true) : False := by
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  obtain ⟨extra, hExtraBlocker, hExtraNotFamily, hBlocker⟩ :=
    liftFamily_exists_unique_extra H x hAvoidBlockerCard hHBlockerCard
      (by omega)
  have hExtraCard : extra.card ≤ 7 := by
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hExtraBlocker)).trans_eq hHCard
  have hFreshCard : (middleFourExtraFresh H x extra).card ≤ 7 :=
    (Finset.card_le_card Finset.sdiff_subset).trans hExtraCard
  have hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16 := by omega
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let selected := middleFourSemanticSelected H x rowOrder
  let base := middleFourModelLiftBaseRows values selected
  let extraPoint := middleFourExtraPoint H x rowOrder extra hBound
  let extraModel := extra.image extraPoint
  have hBaseCard : base.toFinset.card = 8 := by
    calc
      base.toFinset.card = (blocker (avoidPoint H x)).card := by
        simpa [base, values, selected] using middleFourSemanticLiftBaseRows_card
          H x rowOrder hHBlockerRows hBRows hLength
      _ = 8 := hAvoidBlockerCard
  obtain ⟨old, hOldPowerset, hOldSet⟩ :=
    middleFourExtraOldModel_exists_list x rowOrder extra hExtraBlocker
      hExtraNotFamily hBlocker hHBlockerRows hBRows hLength hMaxDegree
  have hExtraModelEq : extraModel = old.toFinset ∪
      (middleFourModelFreshPointList values
        (middleFourExtraFresh H x extra).card).toFinset := by
    calc
      extraModel =
          (extra.filter fun point ↦ point ∈
            middleFourExtraActiveDomain H x).image
              (middleFourBasePoint rowOrder x) ∪
            (middleFourExtraFresh H x extra).image extraPoint := by
        simpa [extraModel, extraPoint] using
          middleFourExtra_image_decompose H x rowOrder extra hBound
      _ = old.toFinset ∪
          (middleFourModelFreshPointList values
            (middleFourExtraFresh H x extra).card).toFinset := by
        rw [hOldSet, middleFourExtraFresh_image H x rowOrder extra hBound]
  have hExtraEnumerated : extraModel ∈
      middleFourModelExtraRowList values base := by
    unfold middleFourModelExtraRowList
    apply List.mem_flatMap.mpr
    refine ⟨old, ?_, ?_⟩
    · simpa [base, values, selected] using hOldPowerset
    · apply List.mem_map.mpr
      refine ⟨(middleFourExtraFresh H x extra).card,
        List.mem_range.mpr (by omega), hExtraModelEq.symm⟩
  have hValuesCheck : sevenNineExtensionValuesCheck values = true := by
    simpa [values] using hCheck
  unfold sevenNineExtensionValuesCheck at hValuesCheck
  have hSelectionCheck := (List.all_eq_true.mp hValuesCheck) selected
    (by simpa [values, selected] using hSelection)
  unfold sevenNineModelSelectionCheck at hSelectionCheck
  change (if base.toFinset.card = 9 then
      sevenNineModelCandidateCheck base
    else if base.toFinset.card = 8 then
      (middleFourModelExtraRowList values base).all
        (sevenNineModelExtraCandidateCheck base (fastBlocker base))
    else true) = true at hSelectionCheck
  rw [hBaseCard] at hSelectionCheck
  norm_num at hSelectionCheck
  have hExtraCheck := hSelectionCheck extraModel hExtraEnumerated
  have hBaseImage : base.toFinset =
      (middleFourSemanticLiftFamily H x).image (fun row ↦
        row.image extraPoint) := by
    simpa [base, values, selected, extraPoint] using
      middleFourSemanticBase_image_extraPoint H x rowOrder extra
        hHBlockerRows hBRows hLength hBound
  have hCandidateSet : (extraModel :: base).toFinset =
      (blocker H).image (fun row ↦ row.image extraPoint) := by
    calc
      (extraModel :: base).toFinset = insert extraModel base.toFinset :=
        List.toFinset_cons
      _ = insert (extra.image extraPoint)
          ((middleFourSemanticLiftFamily H x).image
            (fun row ↦ row.image extraPoint)) := by
        simpa [extraModel] using congrArg
          (fun rows ↦ insert (extra.image extraPoint) rows) hBaseImage
      _ = (insert extra (middleFourSemanticLiftFamily H x)).image
          (fun row ↦ row.image extraPoint) := by rw [Finset.image_insert]
      _ = (blocker H).image (fun row ↦ row.image extraPoint) := by rw [← hBlocker]
  have hSupportSubset : (blocker H).biUnion id ⊆
      middleFourExtraActiveDomain H x ∪ middleFourExtraFresh H x extra :=
    middleFourBlocker_biUnion_subset_extra_domain H x extra hBlocker
  have hPointMap : Set.InjOn extraPoint ((blocker H).biUnion id) :=
    (middleFourExtraPoint_injOn_active_union_fresh
      H x rowOrder extra hLength hBound).mono hSupportSubset
  have hFamilyRowMap : Set.InjOn
      (fun row : G413.Row alpha ↦ row.image extraPoint) (blocker H) :=
    row_image_injOn_of_injOn (fun _ hPoint ↦ hPoint) hPointMap
  have hBlockerRowMap : Set.InjOn
      (fun row : G413.Row alpha ↦ row.image extraPoint)
        (blocker (blocker H)) :=
    blocker_row_image_injOn_of_injOn_active hPointMap
  have hCandidateCard : (extraModel :: base).toFinset.card = 9 := by
    rw [hCandidateSet, Finset.card_image_iff.mpr hFamilyRowMap,
      hHBlockerCard]
  have hModelMax :
      sevenNineModelMaxDegreeAtMostFour (extraModel :: base) = true :=
    modelMaxDegreeAtMostFour_of_image (extraModel :: base) extraPoint
      hCandidateSet (fun _ hPoint ↦ hPoint) hPointMap hMaxDegree
  have hModelRows : sevenNineModelRowsCardBetweenThreeAndSeven
      (extraModel :: base) = true :=
    modelRowsCardBetweenThreeAndSeven_of_image (extraModel :: base) extraPoint
      hCandidateSet (fun _ hPoint ↦ hPoint) hPointMap hHBlockerRows
      (fun _ hRow ↦ (minimalTransversal_card_le_rows
        (mem_blocker.mp hRow)).trans_eq hHCard)
  have hCandidateBlockerCard :
      (blocker (extraModel :: base).toFinset).card = 7 := by
    rw [hCandidateSet, blocker_image_eq_of_injOn_active hPointMap,
      Finset.card_image_iff.mpr hBlockerRowMap,
      blocker_involution hHClutter, hHCard]
  have hCandidateCheck : sevenNineModelCandidateCheck
      (extraModel :: base) = true := by
    rw [← sevenNineModelExtraCandidateCheck_eq]
    exact hExtraCheck
  exact sevenNineModelCandidateCheck_ne_true_of_valid (extraModel :: base)
    hModelRows hCandidateCard hModelMax hCandidateBlockerCard hCandidateCheck

end AiMathLab.P0054.MiddleSevenNineExtension
