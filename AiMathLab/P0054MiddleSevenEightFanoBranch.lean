import AiMathLab.P0054MiddleSevenEightDegree

/-!
# The Fano branch of the seven-plus-eight exclusion

If a three-point row lies on the eight-row side, one of its points has
degree three on the seven-row side.  Removing that point leaves the unique
four-row `K₄` kernel.  Its seven lifted blockers are a Fano plane and hence
self-blocking.  Adding the eighth row makes the blocker strictly larger
than seven, contradicting blocker involution.
-/

namespace AiMathLab.P0054.MiddleSevenEightFanoBranch

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.FanoStep
open AiMathLab.P0054.MiddleSevenEightFinite

theorem exists_degree_three_mem_three_blocker_row_of_card_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} {T : G413.Row α}
    (hT : T ∈ blocker H)
    (hTCard : T.card = 3)
    (hHCard : H.card = 7)
    (hMaxDegree : MaxDegreeAtMost H 3) :
    ∃ x ∈ T, degree H x = 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hTForm⟩ :=
    Finset.card_eq_three.mp hTCard
  subst T
  let aRows := H.filter fun row ↦ a ∈ row
  let bRows := H.filter fun row ↦ b ∈ row
  let cRows := H.filter fun row ↦ c ∈ row
  have hCover : H ⊆ (aRows ∪ bRows) ∪ cRows := by
    intro row hRow
    obtain ⟨x, hxT, hxRow⟩ := (mem_blocker.mp hT).prop row hRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with rfl | rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩)
  have hUnionUpper : ((aRows ∪ bRows) ∪ cRows).card ≤
      aRows.card + bRows.card + cRows.card := by
    calc
      ((aRows ∪ bRows) ∪ cRows).card ≤
          (aRows ∪ bRows).card + cRows.card := Finset.card_union_le _ _
      _ ≤ (aRows.card + bRows.card) + cRows.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hSum : 7 ≤ degree H a + degree H b + degree H c := by
    have hCard := (Finset.card_le_card hCover).trans hUnionUpper
    rw [hHCard] at hCard
    simpa [aRows, bRows, cRows, degree] using hCard
  by_cases ha : degree H a = 3
  · exact ⟨a, by simp, ha⟩
  by_cases hb : degree H b = 3
  · exact ⟨b, by simp, hb⟩
  by_cases hc : degree H c = 3
  · exact ⟨c, by simp, hc⟩
  have haUpper := hMaxDegree a
  have hbUpper := hMaxDegree b
  have hcUpper := hMaxDegree c
  omega

theorem sevenRows_degreeThree_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 8)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 3)
    {x : α} (hDegree : degree H x = 3) :
    False := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 4 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
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
    have hRowDual : row ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hRowH
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hRowDual)).trans_eq hBCard
  have hBKUpper : (blocker K).card ≤ 8 := by
    simpa [K, hBCard] using blocker_avoidPoint_card_le_blocker H x
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 3 := hBMaxDegree x
  let rowOrder := fourRowOrder hKCard
  have hValues : (fourActualSupportMultiplicity rowOrder).toList =
      sevenEightK4Values :=
    sevenEight_actual_values_eq_k4 rowOrder hKClutter hBKRows hKRows
      hKUpper hBKUpper hPairUpper
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 :=
    middleFourActualPoints_length_lt_sixteen rowOrder hKClutter hBKRows
      hKRows hKUpper hBKUpper (hPairUpper.trans (by omega))
  have hPairLength :
      (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).length = 3 := by
    rw [hValues]
    decide
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hBRows hBKRows hLength (hBMaxDegree x)
  have hSelectionEmpty : middleFourSemanticSelected H x rowOrder = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have hModelCard : (middleFourModelBlocker
      (fourActualSupportMultiplicity rowOrder).toList).card =
      (blocker K).card :=
    middleFourModelBlocker_card_eq_actual rowOrder hBKRows hLength
  have hModelSeven : (middleFourModelBlocker
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
    obtain ⟨source, hSource, hSourceEq⟩ :=
      Finset.mem_image.mp hRow'
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
      (fun row : G413.Row α ↦ row.image pointMap) lifted :=
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
          ⟨Finset.mem_image.mpr ⟨point, (Finset.mem_inter.mp hPointInter).1, rfl⟩,
           Finset.mem_image.mpr ⟨point, (Finset.mem_inter.mp hPointInter).2, rfl⟩⟩
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
        (Finset.mem_biUnion.mpr ⟨E, hE, (Finset.mem_inter.mp hPoint).1⟩))
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
      have hEDomain : E ⊆ lifted.biUnion id :=
        blocker_row_subset_biUnion hE
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
      have hFDomain : F ⊆ lifted.biUnion id :=
        blocker_row_subset_biUnion hF
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
  obtain ⟨extra, hExtraB, hExtraNotLifted, hBInsert⟩ :=
    middleFourSemanticLiftFamily_exists_extra H x
      (by simpa [K] using hBKCard) hBCard
  have hExtraCard : 3 ≤ extra.card := hBRows extra hExtraB
  have hDisjoint : ∃ L ∈ lifted, Disjoint L extra := by
    by_contra hNo
    push Not at hNo
    have hTransversal : IsTransversal lifted extra := by
      intro L hL
      obtain ⟨point, hPointL, hPointExtra⟩ :=
        Finset.not_disjoint_iff.mp (hNo L hL)
      exact ⟨point, hPointExtra, hPointL⟩
    obtain ⟨minimal, hMinimalExtra, hMinimal⟩ :=
      exists_minimalTransversal_subset hTransversal
    have hMinimalLifted : minimal ∈ lifted := by
      rw [← hLiftedSelf]
      exact mem_blocker.mpr hMinimal
    have hMinimalB := hLiftedSubset hMinimalLifted
    have hEq : minimal = extra :=
      (blocker_isClutter H) hMinimalB hExtraB hMinimalExtra
    exact hExtraNotLifted (hEq ▸ hMinimalLifted)
  have hStepLarge : 7 < (fastBlockerStep lifted extra).card :=
    seven_lt_fastBlockerStep hLiftedCard hLiftedRows hLiftedPairs
      hExtraCard hDisjoint
  have hStepEq : fastBlockerStep lifted extra = H := by
    calc
      fastBlockerStep lifted extra = blocker (insert extra lifted) :=
        fastBlockerStep_eq_blocker_insert lifted lifted extra hLiftedSelf.symm
      _ = blocker (blocker H) := by rw [← hBInsert]
      _ = H := blocker_involution hHClutter
  rw [hStepEq, hHCard] at hStepLarge
  omega

theorem threeRow_on_eightSide_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 8)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 3)
    {T : G413.Row α} (hT : T ∈ blocker H) (hTCard : T.card = 3) :
    False := by
  obtain ⟨x, -, hDegree⟩ :=
    exists_degree_three_mem_three_blocker_row_of_card_seven
      hT hTCard hHCard hHMaxDegree
  exact sevenRows_degreeThree_impossible hHClutter hHCard hHRows
    hHMaxDegree hBCard hBRows hBMaxDegree hDegree

end AiMathLab.P0054.MiddleSevenEightFanoBranch
