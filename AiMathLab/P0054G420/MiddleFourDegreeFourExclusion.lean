import AiMathLab.P0054G420.MiddleFourDegreeFourBridge

namespace AiMathLab.P0054.G420

open G413 G419

noncomputable def middleFourSemanticSelected {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) :
    List (G413.Row MiddleFourModelPoint) :=
  let values := (fourActualSupportMultiplicity rowOrder).toList
  (middleFourModelOtherBlockerRows values).filter fun modelRow ↦
    decide (∃ row ∈ blocker (avoidPoint H x),
      row.image (middleFourBasePoint rowOrder x) = modelRow ∧
        x ∈ avoidBlockerLift H x row)

theorem middleFourSemanticSelected_toFinset {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourSemanticSelected H x rowOrder).toFinset =
      ((blocker (avoidPoint H x)).filter fun row ↦
          row.card ≠ 2 ∧ x ∈ avoidBlockerLift H x row).image
        (fun row ↦ row.image (middleFourBasePoint rowOrder x)) := by
  classical
  let T := avoidPoint H x
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let pointMap := middleFourBasePoint rowOrder x
  ext modelRow
  constructor
  · intro hModelRow
    have hSelected := List.mem_toFinset.mp hModelRow
    unfold middleFourSemanticSelected at hSelected
    obtain ⟨hOther, hWitness⟩ := List.mem_filter.mp hSelected
    have hWitnessProp : ∃ row ∈ blocker T,
        row.image pointMap = modelRow ∧
          x ∈ avoidBlockerLift H x row := by
      simpa [T, pointMap] using of_decide_eq_true hWitness
    obtain ⟨row, hRow, hRowImage, hLift⟩ := hWitnessProp
    have hModelOther : modelRow.card ≠ 2 := by
      have hOtherSet : modelRow ∈
          (middleFourModelBlocker values).filter fun candidate ↦
            candidate.card ≠ 2 := by
        rw [← middleFourModelOtherBlockerRows_toFinset]
        exact List.mem_toFinset.mpr hOther
      exact (Finset.mem_filter.mp hOtherSet).2
    have hRowCard := middleFourBlockerRow_basePoint_card
      rowOrder x hLength hRow
    apply Finset.mem_image.mpr
    refine ⟨row, Finset.mem_filter.mpr ⟨hRow, ?_⟩, hRowImage⟩
    constructor
    · intro hCard
      apply hModelOther
      rw [← hRowImage, hRowCard, hCard]
    · exact hLift
  · intro hModelRow
    obtain ⟨row, hRowSelected, hRowImage⟩ := Finset.mem_image.mp hModelRow
    obtain ⟨hRow, hRowOther, hLift⟩ := Finset.mem_filter.mp hRowSelected
    have hImageFamily := middleFourActualBlocker_image_basePoint
      rowOrder x hBRows hLength
    have hModelBlocker : modelRow ∈ middleFourModelBlocker values := by
      rw [← hImageFamily]
      exact Finset.mem_image.mpr ⟨row, hRow, hRowImage⟩
    have hRowCard := middleFourBlockerRow_basePoint_card
      rowOrder x hLength hRow
    have hModelOther : modelRow.card ≠ 2 := by
      intro hCard
      apply hRowOther
      rw [← hRowImage, hRowCard] at hCard
      exact hCard
    apply List.mem_toFinset.mpr
    unfold middleFourSemanticSelected
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_toFinset.mp
      rw [middleFourModelOtherBlockerRows_toFinset]
      exact Finset.mem_filter.mpr ⟨by simpa [values] using hModelBlocker,
        hModelOther⟩
    · apply decide_eq_true
      exact ⟨row, by simpa [T] using hRow, by simpa [pointMap] using hRowImage,
        hLift⟩

theorem middleFourSemanticPairRows_toFinset {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).toFinset =
      (pairRows (blocker (avoidPoint H x))).image
        (fun row ↦ row.image (middleFourBasePoint rowOrder x)) := by
  classical
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let pointMap := middleFourBasePoint rowOrder x
  have hImageFamily := middleFourActualBlocker_image_basePoint
    rowOrder x hBRows hLength
  ext modelRow
  constructor
  · intro hModelRow
    have hModelPair : modelRow ∈ pairRows (middleFourModelBlocker values) := by
      rw [← middleFourModelPairBlockerRows_toFinset]
      simpa [values] using hModelRow
    obtain ⟨hModelBlocker, hModelCard⟩ := Finset.mem_filter.mp hModelPair
    have hModelImage : modelRow ∈
        (blocker (avoidPoint H x)).image (fun row ↦ row.image pointMap) := by
      rw [hImageFamily]
      simpa [values, pointMap] using hModelBlocker
    obtain ⟨row, hRow, hRowImage⟩ := Finset.mem_image.mp hModelImage
    have hRowCard := middleFourBlockerRow_basePoint_card
      rowOrder x hLength hRow
    apply Finset.mem_image.mpr
    refine ⟨row, Finset.mem_filter.mpr ⟨hRow, ?_⟩, hRowImage⟩
    rw [← hModelCard, ← hRowImage, hRowCard]
  · intro hModelRow
    obtain ⟨row, hRowPair, hRowImage⟩ := Finset.mem_image.mp hModelRow
    obtain ⟨hRow, hRowCard⟩ := Finset.mem_filter.mp hRowPair
    have hModelBlocker : modelRow ∈ middleFourModelBlocker values := by
      rw [← hImageFamily]
      exact Finset.mem_image.mpr ⟨row, hRow, by simpa [pointMap] using hRowImage⟩
    have hImageCard := middleFourBlockerRow_basePoint_card
      rowOrder x hLength hRow
    have hModelCard : modelRow.card = 2 := by
      rw [← hRowImage, hImageCard, hRowCard]
    rw [middleFourModelPairBlockerRows_toFinset]
    exact Finset.mem_filter.mpr ⟨by simpa [values] using hModelBlocker,
      hModelCard⟩

theorem middleFourSemanticSelected_length_bound {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {bound : Nat}
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hDegree : degree (blocker H) x ≤ bound) :
    (middleFourSemanticSelected H x rowOrder).length +
      (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).length ≤ bound := by
  classical
  let T := avoidPoint H x
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let pointMap := middleFourBasePoint rowOrder x
  let selectedActual := (blocker T).filter fun row ↦
    row.card ≠ 2 ∧ x ∈ avoidBlockerLift H x row
  let pairActual := pairRows (blocker T)
  have hSelectedNodup : (middleFourSemanticSelected H x rowOrder).Nodup := by
    unfold middleFourSemanticSelected
    exact ((middleFourModelBlockerRows_nodup values).filter _).filter _
  have hPairNodup : (middleFourModelPairBlockerRows values).Nodup := by
    exact (middleFourModelBlockerRows_nodup values).filter _
  have hRowMapInj := middleFourBlockerRow_basePoint_injOn
    rowOrder x hLength
  have hSelectedSet := middleFourSemanticSelected_toFinset
    H x rowOrder hBRows hLength
  have hPairSet := middleFourSemanticPairRows_toFinset
    H x rowOrder hBRows hLength
  have hSelectedCard :
      (middleFourSemanticSelected H x rowOrder).length =
        selectedActual.card := by
    calc
      (middleFourSemanticSelected H x rowOrder).length =
          (middleFourSemanticSelected H x rowOrder).toFinset.card :=
        (List.toFinset_card_of_nodup hSelectedNodup).symm
      _ = (selectedActual.image fun row ↦ row.image pointMap).card := by
        simpa [T, selectedActual, pointMap] using
          congrArg Finset.card hSelectedSet
      _ = selectedActual.card := by
        rw [Finset.card_image_iff.mpr]
        exact hRowMapInj.mono (Finset.filter_subset _ _)
  have hPairCard :
      (middleFourModelPairBlockerRows values).length = pairActual.card := by
    calc
      (middleFourModelPairBlockerRows values).length =
          (middleFourModelPairBlockerRows values).toFinset.card :=
        (List.toFinset_card_of_nodup hPairNodup).symm
      _ = (pairActual.image fun row ↦ row.image pointMap).card := by
        simpa [T, values, pairActual, pointMap] using
          congrArg Finset.card hPairSet
      _ = pairActual.card := by
        rw [Finset.card_image_iff.mpr]
        exact hRowMapInj.mono (Finset.filter_subset _ _)
  have hDisjoint : Disjoint selectedActual pairActual := by
    rw [Finset.disjoint_left]
    intro row hSelected hPair
    have hOther := (Finset.mem_filter.mp hSelected).2.1
    exact hOther (Finset.mem_filter.mp hPair).2
  have hCombinedSubset : selectedActual ∪ pairActual ⊆ blocker T := by
    intro row hRow
    rcases Finset.mem_union.mp hRow with hSelected | hPair
    · exact (Finset.mem_filter.mp hSelected).1
    · exact (Finset.mem_filter.mp hPair).1
  have hLiftedSubset :
      (selectedActual ∪ pairActual).image (avoidBlockerLift H x) ⊆
        (blocker H).filter fun row ↦ x ∈ row := by
    intro lifted hLifted
    obtain ⟨row, hRow, rfl⟩ := Finset.mem_image.mp hLifted
    have hRowBlocker : row ∈ blocker T := hCombinedSubset hRow
    refine Finset.mem_filter.mpr
      ⟨by simpa [T] using avoidBlockerLift_mem_blocker hRowBlocker, ?_⟩
    rcases Finset.mem_union.mp hRow with hSelected | hPair
    · exact (Finset.mem_filter.mp hSelected).2.2
    · have hRowCard : row.card = 2 := (Finset.mem_filter.mp hPair).2
      unfold avoidBlockerLift
      split
      · rename_i hTransversal
        exact (false_of_small_transversal hHBlockerRows hTransversal
          (by omega)).elim
      · simp
  have hCombinedCard :
      (selectedActual ∪ pairActual).card ≤ degree (blocker H) x := by
    calc
      (selectedActual ∪ pairActual).card =
          ((selectedActual ∪ pairActual).image
            (avoidBlockerLift H x)).card := by
        symm
        rw [Finset.card_image_iff.mpr]
        exact (avoidBlockerLift_injective H x).mono hCombinedSubset
      _ ≤ ((blocker H).filter fun row ↦ x ∈ row).card :=
        Finset.card_le_card hLiftedSubset
      _ = degree (blocker H) x := rfl
  rw [hSelectedCard, hPairCard]
  rw [← Finset.card_union_of_disjoint hDisjoint]
  exact hCombinedCard.trans hDegree

theorem middleFourSemanticSelected_mem_liftSelectionRows {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hBound : (middleFourSemanticSelected H x rowOrder).length +
      (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).length ≤ 4) :
    middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList := by
  classical
  unfold middleFourModelLiftSelectionRows
  apply List.mem_filter.mpr
  constructor
  · unfold middleFourSemanticSelected
    exact middleFourListPowerset_filter_mem _ _
  · exact decide_eq_true hBound

theorem middleFourPoint_not_active_avoidPoint {alpha : Type*}
    [DecidableEq alpha] (H : G413.Hypergraph alpha) (x : alpha) :
    x ∉ fourActiveUniverse (avoidPoint H x) := by
  intro hActive
  obtain ⟨row, hRow, hPoint⟩ := mem_fourActiveUniverse.mp hActive
  exact (mem_avoidPoint.mp hRow).2 hPoint

theorem middleFourBasePoint_center {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) :
    middleFourBasePoint rowOrder x x =
      middleFourModelCenter
        (fourActualSupportMultiplicity rowOrder).toList := by
  simp [middleFourBasePoint, middleFourPoint_not_active_avoidPoint H x]

theorem middleFourSemanticSelected_insert_iff {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    {row : G413.Row alpha} (hRow : row ∈ blocker (avoidPoint H x)) :
    let modelRow := row.image (middleFourBasePoint rowOrder x)
    modelRow.card = 2 ∨
        modelRow ∈ middleFourSemanticSelected H x rowOrder ↔
      x ∈ avoidBlockerLift H x row := by
  classical
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let pointMap := middleFourBasePoint rowOrder x
  let modelRow := row.image pointMap
  have hRowCard := middleFourBlockerRow_basePoint_card
    rowOrder x hLength hRow
  have hRowMapInj := middleFourBlockerRow_basePoint_injOn
    rowOrder x hLength
  have hImageFamily := middleFourActualBlocker_image_basePoint
    rowOrder x hBRows hLength
  change modelRow.card = 2 ∨
      modelRow ∈ middleFourSemanticSelected H x rowOrder ↔
    x ∈ avoidBlockerLift H x row
  constructor
  · intro hInsert
    rcases hInsert with hPair | hSelected
    · have hPairActual : row.card = 2 := by
        rw [← hRowCard]
        exact hPair
      unfold avoidBlockerLift
      split
      · rename_i hTransversal
        exact (false_of_small_transversal hHBlockerRows hTransversal
          (by omega)).elim
      · simp
    · unfold middleFourSemanticSelected at hSelected
      obtain ⟨_hOther, hWitness⟩ := List.mem_filter.mp hSelected
      have hWitnessProp : ∃ other ∈ blocker (avoidPoint H x),
          other.image pointMap = modelRow ∧
            x ∈ avoidBlockerLift H x other := by
        simpa [pointMap, modelRow] using of_decide_eq_true hWitness
      obtain ⟨other, hOther, hOtherImage, hOtherLift⟩ := hWitnessProp
      have hOtherEq : other = row := hRowMapInj hOther hRow hOtherImage
      simpa [hOtherEq] using hOtherLift
  · intro hLift
    by_cases hPair : modelRow.card = 2
    · exact Or.inl hPair
    · right
      have hModelBlocker : modelRow ∈ middleFourModelBlocker values := by
        rw [← hImageFamily]
        exact Finset.mem_image.mpr ⟨row, hRow, by rfl⟩
      unfold middleFourSemanticSelected
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_toFinset.mp
        rw [middleFourModelOtherBlockerRows_toFinset]
        exact Finset.mem_filter.mpr
          ⟨by simpa [values] using hModelBlocker, hPair⟩
      · apply decide_eq_true
        exact ⟨row, hRow, by rfl, hLift⟩

theorem middleFourSemanticLiftBaseRows_toFinset {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset =
    (blocker (avoidPoint H x)).image fun row ↦
      (avoidBlockerLift H x row).image
        (middleFourBasePoint rowOrder x) := by
  classical
  let T := avoidPoint H x
  let values := (fourActualSupportMultiplicity rowOrder).toList
  let pointMap := middleFourBasePoint rowOrder x
  let selected := middleFourSemanticSelected H x rowOrder
  have hImageFamily := middleFourActualBlocker_image_basePoint
    rowOrder x hBRows hLength
  have hLiftModel {row : G413.Row alpha} (hRow : row ∈ blocker T) :
      (avoidBlockerLift H x row).image pointMap =
        if x ∈ avoidBlockerLift H x row then
          insert (middleFourModelCenter values) (row.image pointMap)
        else row.image pointMap := by
    have hAvoid : x ∉ row := by
      simpa [T] using blocker_avoidPoint_avoids H x hRow
    by_cases hLift : x ∈ avoidBlockerLift H x row
    · rw [if_pos hLift]
      have hNotTransversal : ¬IsTransversal H row := by
        intro hTransversal
        have : avoidBlockerLift H x row = row := by
          simp [avoidBlockerLift, hTransversal]
        exact hAvoid (this ▸ hLift)
      simp [avoidBlockerLift, hNotTransversal,
        pointMap, values, middleFourBasePoint_center H x rowOrder]
    · rw [if_neg hLift]
      have hTransversal : IsTransversal H row := by
        by_contra hNotTransversal
        apply hLift
        simp [avoidBlockerLift, hNotTransversal]
      simp [avoidBlockerLift, hTransversal]
  ext candidate
  constructor
  · intro hCandidate
    have hCandidateList := List.mem_toFinset.mp hCandidate
    unfold middleFourModelLiftBaseRows at hCandidateList
    obtain ⟨modelRow, hModelRowList, hCandidateEq⟩ :=
      List.mem_map.mp hCandidateList
    have hModelRowBlocker : modelRow ∈ middleFourModelBlocker values := by
      exact List.mem_toFinset.mpr hModelRowList
    have hModelImage : modelRow ∈
        (blocker T).image fun row ↦ row.image pointMap := by
      rw [hImageFamily]
      simpa [T, values, pointMap] using hModelRowBlocker
    obtain ⟨row, hRow, hRowImage⟩ := Finset.mem_image.mp hModelImage
    subst modelRow
    have hInsertIff := middleFourSemanticSelected_insert_iff
      H x rowOrder hHBlockerRows hBRows hLength hRow
    have hLiftEq := hLiftModel hRow
    apply Finset.mem_image.mpr
    refine ⟨row, hRow, ?_⟩
    by_cases hLift : x ∈ avoidBlockerLift H x row
    · rw [if_pos (hInsertIff.mpr hLift)] at hCandidateEq
      rw [if_pos hLift] at hLiftEq
      exact hLiftEq.trans hCandidateEq
    · have hNoInsert :
          ¬((row.image pointMap).card = 2 ∨
            row.image pointMap ∈ selected) := by
        simpa [selected, pointMap] using mt hInsertIff.mp hLift
      rw [if_neg hNoInsert] at hCandidateEq
      rw [if_neg hLift] at hLiftEq
      exact hLiftEq.trans hCandidateEq
  · intro hCandidate
    obtain ⟨row, hRow, hCandidateEq⟩ := Finset.mem_image.mp hCandidate
    have hModelRowBlocker : row.image pointMap ∈
        middleFourModelBlocker values := by
      rw [← hImageFamily]
      exact Finset.mem_image.mpr ⟨row, by simpa [T] using hRow, rfl⟩
    have hModelRowList : row.image pointMap ∈
        middleFourModelBlockerRows values :=
      List.mem_toFinset.mp hModelRowBlocker
    apply List.mem_toFinset.mpr
    unfold middleFourModelLiftBaseRows
    apply List.mem_map.mpr
    refine ⟨row.image pointMap, hModelRowList, ?_⟩
    have hInsertIff := middleFourSemanticSelected_insert_iff
      H x rowOrder hHBlockerRows hBRows hLength (by simpa [T] using hRow)
    have hLiftEq := hLiftModel (by simpa [T] using hRow)
    by_cases hLift : x ∈ avoidBlockerLift H x row
    · rw [if_pos (hInsertIff.mpr hLift)]
      rw [if_pos hLift] at hLiftEq
      exact hLiftEq.symm.trans hCandidateEq
    · have hNoInsert :
          ¬((row.image pointMap).card = 2 ∨
            row.image pointMap ∈ selected) := by
        simpa [selected, pointMap] using mt hInsertIff.mp hLift
      rw [if_neg hNoInsert]
      rw [if_neg hLift] at hLiftEq
      exact hLiftEq.symm.trans hCandidateEq

theorem middleFourBasePoint_injOn_active_insert {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    Set.InjOn (middleFourBasePoint rowOrder x)
      (↑(insert x (fourActiveUniverse (avoidPoint H x))) : Set alpha) := by
  intro left hLeft right hRight hEq
  change left ∈ insert x (fourActiveUniverse (avoidPoint H x)) at hLeft
  change right ∈ insert x (fourActiveUniverse (avoidPoint H x)) at hRight
  rw [Finset.mem_insert] at hLeft hRight
  rcases hLeft with hLeftEq | hLeftActive
  · subst left
    rcases hRight with hRightEq | hRightActive
    · subst right
      rfl
    · have hVal := congrArg Fin.val hEq
      rw [middleFourBasePoint_center H x rowOrder,
        middleFourBasePoint_active rowOrder x ⟨right, hRightActive⟩,
        middleFourModelCenter_val_eq_activePoints_length _ hLength] at hVal
      have hRightLt :=
        middleFourActualModelPoint_val_lt_activePoints_length
          rowOrder hLength ⟨right, hRightActive⟩
      omega
  · rcases hRight with hRightEq | hRightActive
    · subst right
      have hVal := congrArg Fin.val hEq
      rw [middleFourBasePoint_active rowOrder x ⟨left, hLeftActive⟩,
        middleFourBasePoint_center H x rowOrder,
        middleFourModelCenter_val_eq_activePoints_length _ hLength] at hVal
      have hLeftLt :=
        middleFourActualModelPoint_val_lt_activePoints_length
          rowOrder hLength ⟨left, hLeftActive⟩
      omega
    · exact middleFourBasePoint_injOn_active rowOrder x hLength
        hLeftActive hRightActive hEq

theorem middleFourAvoidBlockerLift_subset_active_insert {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    {row : G413.Row alpha} (hRow : row ∈ blocker (avoidPoint H x)) :
    avoidBlockerLift H x row ⊆
      insert x (fourActiveUniverse (avoidPoint H x)) := by
  intro point hPoint
  unfold avoidBlockerLift at hPoint
  split at hPoint
  · exact Finset.mem_insert_of_mem
      (middleFourBlockerRow_subset_activeUniverse hRow hPoint)
  · simp only [Finset.mem_insert] at hPoint ⊢
    rcases hPoint with rfl | hPoint
    · exact Or.inl rfl
    · exact Or.inr (middleFourBlockerRow_subset_activeUniverse hRow hPoint)

theorem middleFourSemanticLiftRowMap_injOn {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    Set.InjOn (fun row : G413.Row alpha ↦
      (avoidBlockerLift H x row).image
        (middleFourBasePoint rowOrder x))
      (blocker (avoidPoint H x)) := by
  intro left hLeft right hRight hRows
  change (avoidBlockerLift H x left).image
      (middleFourBasePoint rowOrder x) =
    (avoidBlockerLift H x right).image
      (middleFourBasePoint rowOrder x) at hRows
  have hPointInj := middleFourBasePoint_injOn_active_insert
    H x rowOrder hLength
  have hLiftEq : avoidBlockerLift H x left =
      avoidBlockerLift H x right := by
    ext point
    constructor
    · intro hPoint
      have hImagePoint : middleFourBasePoint rowOrder x point ∈
          (avoidBlockerLift H x right).image
            (middleFourBasePoint rowOrder x) := by
        rw [← hRows]
        exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
      obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
      have hPointDomain := middleFourAvoidBlockerLift_subset_active_insert
        H x hLeft hPoint
      have hOtherDomain := middleFourAvoidBlockerLift_subset_active_insert
        H x hRight hOther
      exact (hPointInj hOtherDomain hPointDomain hOtherEq) ▸ hOther
    · intro hPoint
      have hImagePoint : middleFourBasePoint rowOrder x point ∈
          (avoidBlockerLift H x left).image
            (middleFourBasePoint rowOrder x) := by
        rw [hRows]
        exact Finset.mem_image.mpr ⟨point, hPoint, rfl⟩
      obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
      have hPointDomain := middleFourAvoidBlockerLift_subset_active_insert
        H x hRight hPoint
      have hOtherDomain := middleFourAvoidBlockerLift_subset_active_insert
        H x hLeft hOther
      exact (hPointInj hOtherDomain hPointDomain hOtherEq) ▸ hOther
  exact avoidBlockerLift_injective H x hLeft hRight hLiftEq

theorem middleFourSemanticLiftBaseRows_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16) :
    (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset.card =
      (blocker (avoidPoint H x)).card := by
  rw [middleFourSemanticLiftBaseRows_toFinset
    H x rowOrder hHBlockerRows hBRows hLength]
  apply Finset.card_image_iff.mpr
  exact middleFourSemanticLiftRowMap_injOn H x rowOrder hLength

noncomputable def middleFourSemanticLiftFamily {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) :
    G413.Hypergraph alpha :=
  (blocker (avoidPoint H x)).image (avoidBlockerLift H x)

theorem middleFourSemanticLiftFamily_subset_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) :
    middleFourSemanticLiftFamily H x ⊆ blocker H := by
  intro row hRow
  obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hRow
  exact avoidBlockerLift_mem_blocker hSource

theorem middleFourSemanticLiftFamily_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) :
    (middleFourSemanticLiftFamily H x).card =
      (blocker (avoidPoint H x)).card := by
  unfold middleFourSemanticLiftFamily
  rw [Finset.card_image_iff.mpr]
  exact avoidBlockerLift_injective H x

theorem middleFourSemanticLiftFamily_eq_blocker_of_card_eq {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (hCard : (blocker (avoidPoint H x)).card = (blocker H).card) :
    middleFourSemanticLiftFamily H x = blocker H := by
  apply Finset.eq_of_subset_of_card_le
    (middleFourSemanticLiftFamily_subset_blocker H x)
  rw [middleFourSemanticLiftFamily_card, hCard]

theorem middleFourSemanticLiftFamily_exists_extra {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (hLiftCard : (blocker (avoidPoint H x)).card = 7)
    (hBlockerCard : (blocker H).card = 8) :
    ∃ extra ∈ blocker H,
      extra ∉ middleFourSemanticLiftFamily H x ∧
        blocker H = insert extra (middleFourSemanticLiftFamily H x) := by
  have hFamilyCard : (middleFourSemanticLiftFamily H x).card = 7 := by
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

theorem blocker_image_of_injOn_active {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    {H : G413.Hypergraph alpha} {row : G413.Row alpha}
    {pointMap : alpha → beta}
    (hPointMap : Set.InjOn pointMap (H.biUnion id))
    (hRow : row ∈ blocker H) :
    row.image pointMap ∈ blocker (H.image fun source ↦ source.image pointMap) := by
  classical
  apply mem_blocker.mpr
  have hTransversal : IsTransversal
      (H.image fun source ↦ source.image pointMap)
      (row.image pointMap) := by
    intro imageRow hImageRow
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
    obtain ⟨point, hPointRow, hPointSource⟩ :=
      (mem_blocker.mp hRow).prop source hSource
    exact ⟨pointMap point,
      Finset.mem_image.mpr ⟨point, hPointRow, rfl⟩,
      Finset.mem_image.mpr ⟨point, hPointSource, rfl⟩⟩
  apply hTransversal.minimal_of_privateRows
  intro imagePoint hImagePoint
  obtain ⟨point, hPointRow, rfl⟩ := Finset.mem_image.mp hImagePoint
  obtain ⟨source, hPrivate⟩ :=
    (mem_blocker.mp hRow).exists_privateRow hPointRow
  refine ⟨source.image pointMap,
    Finset.mem_image.mpr ⟨source, hPrivate.1, rfl⟩,
    Finset.mem_image.mpr ⟨point, hPointRow, rfl⟩,
    Finset.mem_image.mpr ⟨point, hPrivate.2.2.1, rfl⟩, ?_⟩
  intro imageOther hOtherRow hOtherSource
  obtain ⟨other, hOtherRowActual, rfl⟩ := Finset.mem_image.mp hOtherRow
  obtain ⟨sourcePoint, hSourcePoint, hPointEq⟩ :=
    Finset.mem_image.mp hOtherSource
  have hOtherActive : other ∈ H.biUnion id :=
    blocker_row_subset_biUnion hRow hOtherRowActual
  have hSourceActive : sourcePoint ∈ H.biUnion id :=
    Finset.mem_biUnion.mpr ⟨source, hPrivate.1, hSourcePoint⟩
  have hOtherEq : other = sourcePoint :=
    hPointMap hOtherActive hSourceActive hPointEq.symm
  subst sourcePoint
  have hOtherPoint : other = point :=
    hPrivate.2.2.2 hOtherRowActual hSourcePoint
  exact congrArg pointMap hOtherPoint

theorem blocker_image_eq_of_injOn_active {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    {H : G413.Hypergraph alpha} {pointMap : alpha → beta}
    (hPointMap : Set.InjOn pointMap (H.biUnion id)) :
    blocker (H.image fun source ↦ source.image pointMap) =
      (blocker H).image fun row ↦ row.image pointMap := by
  classical
  ext imageRow
  constructor
  · intro hImageRow
    let sourceRow : G413.Row alpha :=
      (H.biUnion id).filter fun point ↦ pointMap point ∈ imageRow
    have hImageRowRange : imageRow ⊆ (H.biUnion id).image pointMap := by
      intro imagePoint hImagePoint
      obtain ⟨privateImageRow, hPrivate⟩ :=
        (mem_blocker.mp hImageRow).exists_privateRow hImagePoint
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hPrivate.1
      obtain ⟨point, hPointSource, hPointEq⟩ :=
        Finset.mem_image.mp hPrivate.2.2.1
      exact Finset.mem_image.mpr
        ⟨point, Finset.mem_biUnion.mpr ⟨source, hSource, hPointSource⟩,
          hPointEq⟩
    have hSourceImage : sourceRow.image pointMap = imageRow := by
      ext imagePoint
      constructor
      · intro hPoint
        obtain ⟨point, hPointSource, rfl⟩ := Finset.mem_image.mp hPoint
        exact (Finset.mem_filter.mp hPointSource).2
      · intro hPoint
        obtain ⟨point, hPointActive, rfl⟩ :=
          Finset.mem_image.mp (hImageRowRange hPoint)
        exact Finset.mem_image.mpr
          ⟨point, Finset.mem_filter.mpr ⟨hPointActive, hPoint⟩, rfl⟩
    have hSourceRow : sourceRow ∈ blocker H := by
      apply mem_blocker.mpr
      have hTransversal : IsTransversal H sourceRow := by
        intro source hSource
        have hSourceImageMember : source.image pointMap ∈
            H.image fun row ↦ row.image pointMap :=
          Finset.mem_image.mpr ⟨source, hSource, rfl⟩
        obtain ⟨imagePoint, hPointImageRow, hPointSourceImage⟩ :=
          (mem_blocker.mp hImageRow).prop _ hSourceImageMember
        obtain ⟨point, hPointSource, hPointEq⟩ :=
          Finset.mem_image.mp hPointSourceImage
        subst imagePoint
        exact ⟨point, Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨source, hSource, hPointSource⟩,
            hPointImageRow⟩, hPointSource⟩
      apply hTransversal.minimal_of_privateRows
      intro point hPointSourceRow
      have hPointImageRow : pointMap point ∈ imageRow :=
        (Finset.mem_filter.mp hPointSourceRow).2
      obtain ⟨privateImageRow, hPrivate⟩ :=
        (mem_blocker.mp hImageRow).exists_privateRow hPointImageRow
      obtain ⟨source, hSource, hSourceImage⟩ :=
        Finset.mem_image.mp hPrivate.1
      refine ⟨source, hSource, hPointSourceRow, ?_, ?_⟩
      · obtain ⟨other, hOtherSource, hOtherEq⟩ := Finset.mem_image.mp
          (hSourceImage ▸ hPrivate.2.2.1)
        have hPointActive := (Finset.mem_filter.mp hPointSourceRow).1
        have hOtherActive : other ∈ H.biUnion id :=
          Finset.mem_biUnion.mpr ⟨source, hSource, hOtherSource⟩
        exact (hPointMap hPointActive hOtherActive hOtherEq.symm) ▸ hOtherSource
      · intro other hOtherSourceRow hOtherSource
        have hOtherImageRow : pointMap other ∈ imageRow :=
          (Finset.mem_filter.mp hOtherSourceRow).2
        have hOtherPrivate : pointMap other ∈ privateImageRow := by
          rw [← hSourceImage]
          exact Finset.mem_image.mpr ⟨other, hOtherSource, rfl⟩
        have hMapEq : pointMap other = pointMap point :=
          hPrivate.2.2.2 hOtherImageRow hOtherPrivate
        have hOtherActive := (Finset.mem_filter.mp hOtherSourceRow).1
        have hPointActive := (Finset.mem_filter.mp hPointSourceRow).1
        exact hPointMap hOtherActive hPointActive hMapEq
    exact Finset.mem_image.mpr ⟨sourceRow, hSourceRow, hSourceImage⟩
  · intro hImageRow
    obtain ⟨sourceRow, hSourceRow, rfl⟩ := Finset.mem_image.mp hImageRow
    exact blocker_image_of_injOn_active hPointMap hSourceRow

theorem blocker_row_image_injOn_of_injOn_active {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    {H : G413.Hypergraph alpha} {pointMap : alpha → beta}
    (hPointMap : Set.InjOn pointMap (H.biUnion id)) :
    Set.InjOn (fun row : G413.Row alpha ↦ row.image pointMap)
      (blocker H) := by
  intro left hLeft right hRight hRows
  change left.image pointMap = right.image pointMap at hRows
  ext point
  constructor
  · intro hPointLeft
    have hImagePoint : pointMap point ∈ right.image pointMap := by
      rw [← hRows]
      exact Finset.mem_image.mpr ⟨point, hPointLeft, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointActive := blocker_row_subset_biUnion hLeft hPointLeft
    have hOtherActive := blocker_row_subset_biUnion hRight hOther
    exact (hPointMap hOtherActive hPointActive hOtherEq) ▸ hOther
  · intro hPointRight
    have hImagePoint : pointMap point ∈ left.image pointMap := by
      rw [hRows]
      exact Finset.mem_image.mpr ⟨point, hPointRight, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointActive := blocker_row_subset_biUnion hRight hPointRight
    have hOtherActive := blocker_row_subset_biUnion hLeft hOther
    exact (hPointMap hOtherActive hPointActive hOtherEq) ▸ hOther

theorem row_image_injOn_of_injOn {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    {family : G413.Hypergraph alpha} {domain : Finset alpha}
    {pointMap : alpha → beta}
    (hFamilyDomain : family.biUnion id ⊆ domain)
    (hPointMap : Set.InjOn pointMap domain) :
    Set.InjOn (fun row : G413.Row alpha ↦ row.image pointMap) family := by
  intro left hLeft right hRight hRows
  change left.image pointMap = right.image pointMap at hRows
  ext point
  constructor
  · intro hPointLeft
    have hImagePoint : pointMap point ∈ right.image pointMap := by
      rw [← hRows]
      exact Finset.mem_image.mpr ⟨point, hPointLeft, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointDomain := hFamilyDomain
      (Finset.mem_biUnion.mpr ⟨left, hLeft, hPointLeft⟩)
    have hOtherDomain := hFamilyDomain
      (Finset.mem_biUnion.mpr ⟨right, hRight, hOther⟩)
    exact (hPointMap hOtherDomain hPointDomain hOtherEq) ▸ hOther
  · intro hPointRight
    have hImagePoint : pointMap point ∈ left.image pointMap := by
      rw [hRows]
      exact Finset.mem_image.mpr ⟨point, hPointRight, rfl⟩
    obtain ⟨other, hOther, hOtherEq⟩ := Finset.mem_image.mp hImagePoint
    have hPointDomain := hFamilyDomain
      (Finset.mem_biUnion.mpr ⟨right, hRight, hPointRight⟩)
    have hOtherDomain := hFamilyDomain
      (Finset.mem_biUnion.mpr ⟨left, hLeft, hOther⟩)
    exact (hPointMap hOtherDomain hPointDomain hOtherEq) ▸ hOther

theorem degree_image_eq_of_injOn {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    {family : G413.Hypergraph alpha} {domain : Finset alpha}
    {pointMap : alpha → beta} {point : alpha}
    (hPointDomain : point ∈ domain)
    (hFamilyDomain : family.biUnion id ⊆ domain)
    (hPointMap : Set.InjOn pointMap domain) :
    degree (family.image fun row ↦ row.image pointMap) (pointMap point) =
      degree family point := by
  have hFilter :
      (family.image fun row ↦ row.image pointMap).filter
          (fun row ↦ pointMap point ∈ row) =
        (family.filter fun row ↦ point ∈ row).image
          (fun row ↦ row.image pointMap) := by
    ext imageRow
    constructor
    · intro hImageRow
      obtain ⟨hImageFamily, hPointImage⟩ := Finset.mem_filter.mp hImageRow
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageFamily
      obtain ⟨other, hOtherSource, hOtherEq⟩ :=
        Finset.mem_image.mp hPointImage
      have hOtherDomain := hFamilyDomain
        (Finset.mem_biUnion.mpr ⟨source, hSource, hOtherSource⟩)
      have hOtherPoint : other = point :=
        hPointMap hOtherDomain hPointDomain hOtherEq
      subst other
      exact Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨hSource, hOtherSource⟩, rfl⟩
    · intro hImageRow
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
      obtain ⟨hSourceFamily, hPointSource⟩ := Finset.mem_filter.mp hSource
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨source, hSourceFamily, rfl⟩,
          Finset.mem_image.mpr ⟨point, hPointSource, rfl⟩⟩
  unfold degree
  rw [hFilter, Finset.card_image_iff.mpr]
  exact (row_image_injOn_of_injOn hFamilyDomain hPointMap).mono
    (Finset.filter_subset _ _)

theorem middleFourSemanticBase_blocker_card_eight {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 8)
    (hHBlockerCard : (blocker H).card = 8) :
    (blocker (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset).card = 8 := by
  let pointMap := middleFourBasePoint rowOrder x
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hLiftEq : middleFourSemanticLiftFamily H x = blocker H :=
    middleFourSemanticLiftFamily_eq_blocker_of_card_eq H x (by omega)
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
      base.toFinset =
          (blocker (avoidPoint H x)).image (fun row ↦
            (avoidBlockerLift H x row).image pointMap) := by
        simpa [base, pointMap] using
          middleFourSemanticLiftBaseRows_toFinset
            H x rowOrder hHBlockerRows hBRows hLength
      _ = (middleFourSemanticLiftFamily H x).image
          (fun row ↦ row.image pointMap) := by
        rw [middleFourSemanticLiftFamily, Finset.image_image]
        rfl
      _ = (blocker H).image (fun row ↦ row.image pointMap) := by
        rw [hLiftEq]
  have hBlockerImage := blocker_image_eq_of_injOn_active hPointMap
  have hRowMap := blocker_row_image_injOn_of_injOn_active hPointMap
  change (blocker base.toFinset).card = 8
  rw [hBaseSet, hBlockerImage]
  rw [Finset.card_image_iff.mpr hRowMap,
    blocker_involution hHClutter, hHCard]

theorem middleFourSemanticBase_mem_candidateRows_of_card_eight
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hBaseCard : (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset.card = 8) :
    middleFourModelLiftBaseRows
        (fourActualSupportMultiplicity rowOrder).toList
        (middleFourSemanticSelected H x rowOrder) ∈
      middleFourModelCandidateRows
        (fourActualSupportMultiplicity rowOrder).toList := by
  unfold middleFourModelCandidateRows
  apply List.mem_flatMap.mpr
  refine ⟨middleFourSemanticSelected H x rowOrder, hSelection, ?_⟩
  unfold middleFourModelCandidateRowsForSelection
  rw [if_pos hBaseCard]
  simp

theorem middleFourSemanticBase_eight_contradicts_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 8)
    (hHBlockerCard : (blocker H).card = 8)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hCheck : middleFourDegreeFourValuesCheck
      (fourActualSupportMultiplicity rowOrder).toList = true) :
    False := by
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hBaseCard : base.toFinset.card = 8 := by
    calc
      base.toFinset.card = (blocker (avoidPoint H x)).card := by
        simpa [base] using middleFourSemanticLiftBaseRows_card
          H x rowOrder hHBlockerRows hBRows hLength
      _ = 8 := hAvoidBlockerCard
  have hCandidate : base ∈ middleFourModelCandidateRows
      (fourActualSupportMultiplicity rowOrder).toList := by
    simpa [base] using middleFourSemanticBase_mem_candidateRows_of_card_eight
      H x rowOrder hSelection hBaseCard
  have hCheckCandidate :=
    (List.all_eq_true.mp hCheck) base hCandidate
  have hBlockerNe : (fastBlocker base).card ≠ 8 :=
    of_decide_eq_true hCheckCandidate
  rw [fastBlocker_eq_blocker] at hBlockerNe
  apply hBlockerNe
  simpa [base] using middleFourSemanticBase_blocker_card_eight
    x rowOrder hHClutter hHCard hHBlockerRows hBRows hLength
      hAvoidBlockerCard hHBlockerCard

def middleFourExtraActiveDomain {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) : Finset alpha :=
  insert x (fourActiveUniverse (avoidPoint H x))

def middleFourExtraFresh {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) (extra : G413.Row alpha) :
    Finset alpha :=
  extra \ middleFourExtraActiveDomain H x

noncomputable def middleFourExtraPoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16)
    (point : alpha) : MiddleFourModelPoint :=
  if hActive : point ∈ middleFourExtraActiveDomain H x then
    middleFourBasePoint rowOrder x point
  else if hFresh : point ∈ middleFourExtraFresh H x extra then
    ⟨(fourActivePoints
        (fourActualSupportMultiplicity rowOrder)).length + 1 +
        (Finset.equivFin (middleFourExtraFresh H x extra)
          ⟨point, hFresh⟩).val,
      by
        have hIndex := (Finset.equivFin
          (middleFourExtraFresh H x extra) ⟨point, hFresh⟩).isLt
        omega⟩
  else
    middleFourModelCenter (fourActualSupportMultiplicity rowOrder).toList

theorem middleFourExtraPoint_active {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16)
    {point : alpha} (hPoint : point ∈ middleFourExtraActiveDomain H x) :
    middleFourExtraPoint H x rowOrder extra hBound point =
      middleFourBasePoint rowOrder x point := by
  simp [middleFourExtraPoint, hPoint]

theorem middleFourExtraPoint_fresh_val {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16)
    {point : alpha} (hPoint : point ∈ middleFourExtraFresh H x extra) :
    (middleFourExtraPoint H x rowOrder extra hBound point).val =
      (fourActivePoints
        (fourActualSupportMultiplicity rowOrder)).length + 1 +
        (Finset.equivFin (middleFourExtraFresh H x extra)
          ⟨point, hPoint⟩).val := by
  have hNotActive := (Finset.mem_sdiff.mp hPoint).2
  simp [middleFourExtraPoint, hNotActive, hPoint]

theorem middleFourBasePoint_val_le_activePoints_length {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    {point : alpha} (hPoint : point ∈ middleFourExtraActiveDomain H x) :
    (middleFourBasePoint rowOrder x point).val ≤
      (fourActivePoints
        (fourActualSupportMultiplicity rowOrder)).length := by
  rw [middleFourExtraActiveDomain, Finset.mem_insert] at hPoint
  rcases hPoint with hPoint | hPoint
  · subst point
    rw [middleFourBasePoint_center H x rowOrder,
      middleFourModelCenter_val_eq_activePoints_length _ hLength]
  · rw [middleFourBasePoint_active rowOrder x ⟨point, hPoint⟩]
    exact (middleFourActualModelPoint_val_lt_activePoints_length
      rowOrder hLength ⟨point, hPoint⟩).le

theorem middleFourExtraPoint_injOn_active_union_fresh {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16) :
    Set.InjOn (middleFourExtraPoint H x rowOrder extra hBound)
      (↑(middleFourExtraActiveDomain H x ∪
        middleFourExtraFresh H x extra) : Set alpha) := by
  intro left hLeft right hRight hEq
  change left ∈ middleFourExtraActiveDomain H x ∪
    middleFourExtraFresh H x extra at hLeft
  change right ∈ middleFourExtraActiveDomain H x ∪
    middleFourExtraFresh H x extra at hRight
  rw [Finset.mem_union] at hLeft hRight
  rcases hLeft with hLeftActive | hLeftFresh
  · rcases hRight with hRightActive | hRightFresh
    · rw [middleFourExtraPoint_active H x rowOrder extra hBound hLeftActive,
        middleFourExtraPoint_active H x rowOrder extra hBound hRightActive] at hEq
      exact middleFourBasePoint_injOn_active_insert H x rowOrder hLength
        hLeftActive hRightActive hEq
    · have hVal := congrArg Fin.val hEq
      rw [middleFourExtraPoint_active H x rowOrder extra hBound hLeftActive,
        middleFourExtraPoint_fresh_val H x rowOrder extra hBound hRightFresh]
        at hVal
      have hLeftLe := middleFourBasePoint_val_le_activePoints_length
        H x rowOrder hLength hLeftActive
      omega
  · rcases hRight with hRightActive | hRightFresh
    · have hVal := congrArg Fin.val hEq
      rw [middleFourExtraPoint_fresh_val H x rowOrder extra hBound hLeftFresh,
        middleFourExtraPoint_active H x rowOrder extra hBound hRightActive]
        at hVal
      have hRightLe := middleFourBasePoint_val_le_activePoints_length
        H x rowOrder hLength hRightActive
      omega
    · have hVal := congrArg Fin.val hEq
      rw [middleFourExtraPoint_fresh_val H x rowOrder extra hBound hLeftFresh,
        middleFourExtraPoint_fresh_val H x rowOrder extra hBound hRightFresh]
        at hVal
      have hIndexEq :
          Finset.equivFin (middleFourExtraFresh H x extra) ⟨left, hLeftFresh⟩ =
            Finset.equivFin (middleFourExtraFresh H x extra)
              ⟨right, hRightFresh⟩ := by
        apply Fin.ext
        omega
      exact congrArg Subtype.val
        ((Finset.equivFin (middleFourExtraFresh H x extra)).injective hIndexEq)

theorem middleFourBlocker_biUnion_subset_extra_domain {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) (extra : G413.Row alpha)
    (hBlocker : blocker H =
      insert extra (middleFourSemanticLiftFamily H x)) :
    (blocker H).biUnion id ⊆
      middleFourExtraActiveDomain H x ∪ middleFourExtraFresh H x extra := by
  intro point hPoint
  obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
  rw [hBlocker, Finset.mem_insert] at hRow
  rcases hRow with hRow | hRow
  · subst row
    by_cases hActive : point ∈ middleFourExtraActiveDomain H x
    · exact Finset.mem_union_left _ hActive
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hPointRow, hActive⟩)
  · obtain ⟨source, hSource, hSourceEq⟩ := Finset.mem_image.mp hRow
    rw [← hSourceEq] at hPointRow
    exact Finset.mem_union_left _
      (middleFourAvoidBlockerLift_subset_active_insert
        H x hSource hPointRow)

theorem middleFourExtraFresh_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16) :
    (middleFourExtraFresh H x extra).image
        (middleFourExtraPoint H x rowOrder extra hBound) =
      (middleFourModelFreshPointList
        (fourActualSupportMultiplicity rowOrder).toList
        (middleFourExtraFresh H x extra).card).toFinset := by
  let freshModels := middleFourModelFreshPointList
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourExtraFresh H x extra).card
  have hSubset : (middleFourExtraFresh H x extra).image
      (middleFourExtraPoint H x rowOrder extra hBound) ⊆
      freshModels.toFinset := by
    intro modelPoint hModelPoint
    obtain ⟨point, hPointFresh, rfl⟩ :=
      Finset.mem_image.mp hModelPoint
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _, ?_⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true
      rw [middleFourExtraPoint_fresh_val
        H x rowOrder extra hBound hPointFresh,
        middleFourModelSupports_length_eq_activePoints]
      omega
    · apply decide_eq_true
      rw [middleFourExtraPoint_fresh_val
        H x rowOrder extra hBound hPointFresh,
        middleFourModelSupports_length_eq_activePoints]
      have hIndex := (Finset.equivFin
        (middleFourExtraFresh H x extra) ⟨point, hPointFresh⟩).isLt
      omega
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  have hImageCard : ((middleFourExtraFresh H x extra).image
      (middleFourExtraPoint H x rowOrder extra hBound)).card =
      (middleFourExtraFresh H x extra).card := by
    rw [Finset.card_image_iff.mpr]
    exact (middleFourExtraPoint_injOn_active_union_fresh
      H x rowOrder extra hLength hBound).mono
        (fun _ hPoint ↦ Finset.mem_union_right _ hPoint)
  have hFreshModelsCardLe : freshModels.toFinset.card ≤
      (middleFourExtraFresh H x extra).card := by
    calc
      freshModels.toFinset.card ≤
          (Finset.Icc
            ((fourActivePoints
              (fourActualSupportMultiplicity rowOrder)).length + 1)
            ((fourActivePoints
              (fourActualSupportMultiplicity rowOrder)).length +
                (middleFourExtraFresh H x extra).card)).card := by
        apply Finset.card_le_card_of_injOn
          (fun point : MiddleFourModelPoint ↦ point.val)
        · intro modelPoint hModelPoint
          have hModelList := List.mem_toFinset.mp hModelPoint
          obtain ⟨_hRange, hPredicate⟩ := List.mem_filter.mp hModelList
          obtain ⟨hLowerBool, hUpperBool⟩ :=
            Bool.and_eq_true_iff.mp hPredicate
          have hLower := of_decide_eq_true hLowerBool
          have hUpper := of_decide_eq_true hUpperBool
          rw [middleFourModelSupports_length_eq_activePoints] at hLower hUpper
          apply Finset.mem_Icc.mpr
          change (fourActivePoints
              (fourActualSupportMultiplicity rowOrder)).length + 1 ≤
                modelPoint.val ∧
            modelPoint.val ≤ (fourActivePoints
              (fourActualSupportMultiplicity rowOrder)).length +
                (middleFourExtraFresh H x extra).card
          exact ⟨by omega, hUpper⟩
        · intro left _hLeft right _hRight hEq
          exact Fin.ext hEq
      _ = (middleFourExtraFresh H x extra).card := by
        rw [Nat.card_Icc]
        omega
  apply Finset.eq_of_subset_of_card_le hSubset
  rw [hImageCard]
  exact hFreshModelsCardLe

theorem middleFourExtraOldModel_subset_eligible {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hExtraBlocker : extra ∈ blocker H)
    (hExtraNotFamily : extra ∉ middleFourSemanticLiftFamily H x)
    (hBlocker : blocker H =
      insert extra (middleFourSemanticLiftFamily H x))
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hMaxDegree : MaxDegreeAtMost (blocker H) 4) :
    (extra.filter fun point ↦ point ∈ middleFourExtraActiveDomain H x).image
        (middleFourBasePoint rowOrder x) ⊆
      (middleFourModelEligibleOldPointList
        (fourActualSupportMultiplicity rowOrder).toList
        (middleFourModelLiftBaseRows
          (fourActualSupportMultiplicity rowOrder).toList
          (middleFourSemanticSelected H x rowOrder))).toFinset := by
  let family := middleFourSemanticLiftFamily H x
  let pointMap := middleFourBasePoint rowOrder x
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hFamilyDomain : family.biUnion id ⊆
      middleFourExtraActiveDomain H x := by
    intro point hPoint
    obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
    obtain ⟨source, hSource, hSourceEq⟩ := Finset.mem_image.mp hRow
    rw [← hSourceEq] at hPointRow
    exact middleFourAvoidBlockerLift_subset_active_insert
      H x hSource hPointRow
  have hPointMap : Set.InjOn pointMap (middleFourExtraActiveDomain H x) := by
    simpa [pointMap, middleFourExtraActiveDomain] using
      middleFourBasePoint_injOn_active_insert H x rowOrder hLength
  have hBaseSet : base.toFinset =
      family.image fun row ↦ row.image pointMap := by
    calc
      base.toFinset =
          (blocker (avoidPoint H x)).image (fun row ↦
            (avoidBlockerLift H x row).image pointMap) := by
        simpa [base, pointMap] using
          middleFourSemanticLiftBaseRows_toFinset
            H x rowOrder hHBlockerRows hBRows hLength
      _ = family.image (fun row ↦ row.image pointMap) := by
        change (blocker (avoidPoint H x)).image (fun row ↦
            (avoidBlockerLift H x row).image pointMap) =
          (middleFourSemanticLiftFamily H x).image
            (fun row ↦ row.image pointMap)
        rw [middleFourSemanticLiftFamily, Finset.image_image]
        rfl
  intro modelPoint hModelPoint
  obtain ⟨point, hPointOld, rfl⟩ := Finset.mem_image.mp hModelPoint
  obtain ⟨hPointExtra, hPointActive⟩ := Finset.mem_filter.mp hPointOld
  have hBaseDegree : degree base.toFinset (pointMap point) =
      degree family point := by
    rw [hBaseSet]
    exact degree_image_eq_of_injOn hPointActive hFamilyDomain hPointMap
  have hGlobalDegree : degree (blocker H) point =
      degree family point + 1 := by
    have hBlocker' : blocker H = insert extra family := by
      simpa [family] using hBlocker
    have hExtraNotFilter : extra ∉
        family.filter (fun row ↦ point ∈ row) := by
      intro hExtra
      exact hExtraNotFamily (Finset.mem_filter.mp hExtra).1
    unfold degree
    rw [hBlocker', Finset.filter_insert, if_pos hPointExtra,
      Finset.card_insert_of_notMem hExtraNotFilter]
  have hDegreeLt : degree base.toFinset (pointMap point) < 4 := by
    have hUpper := hMaxDegree point
    omega
  apply List.mem_toFinset.mpr
  apply List.mem_filter.mpr
  refine ⟨List.mem_finRange _, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [middleFourModelSupports_length_eq_activePoints]
    exact middleFourBasePoint_val_le_activePoints_length
      H x rowOrder hLength hPointActive
  · exact decide_eq_true hDegreeLt

theorem middleFourExtraOldModel_exists_list {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hExtraBlocker : extra ∈ blocker H)
    (hExtraNotFamily : extra ∉ middleFourSemanticLiftFamily H x)
    (hBlocker : blocker H =
      insert extra (middleFourSemanticLiftFamily H x))
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hMaxDegree : MaxDegreeAtMost (blocker H) 4) :
    ∃ old ∈ middleFourListPowerset
        (middleFourModelEligibleOldPointList
          (fourActualSupportMultiplicity rowOrder).toList
          (middleFourModelLiftBaseRows
            (fourActualSupportMultiplicity rowOrder).toList
            (middleFourSemanticSelected H x rowOrder))),
      old.toFinset =
        (extra.filter fun point ↦ point ∈
          middleFourExtraActiveDomain H x).image
            (middleFourBasePoint rowOrder x) := by
  let eligible := middleFourModelEligibleOldPointList
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
  let oldModel := (extra.filter fun point ↦ point ∈
    middleFourExtraActiveDomain H x).image
      (middleFourBasePoint rowOrder x)
  let old := eligible.filter fun point ↦ point ∈ oldModel
  have hOldSubset : oldModel ⊆ eligible.toFinset := by
    simpa [eligible, oldModel] using middleFourExtraOldModel_subset_eligible
      x rowOrder extra hExtraBlocker hExtraNotFamily hBlocker
        hHBlockerRows hBRows hLength hMaxDegree
  refine ⟨old, ?_, ?_⟩
  · simpa [old] using middleFourListPowerset_filter_mem
      (fun point ↦ point ∈ oldModel) eligible
  · ext modelPoint
    constructor
    · intro hPoint
      have hPointList := List.mem_toFinset.mp hPoint
      exact of_decide_eq_true (List.mem_filter.mp hPointList).2
    · intro hPoint
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      exact ⟨List.mem_toFinset.mp (hOldSubset hPoint), decide_eq_true hPoint⟩

theorem middleFourExtra_image_decompose {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16) :
    extra.image (middleFourExtraPoint H x rowOrder extra hBound) =
      (extra.filter fun point ↦ point ∈
        middleFourExtraActiveDomain H x).image
          (middleFourBasePoint rowOrder x) ∪
        (middleFourExtraFresh H x extra).image
          (middleFourExtraPoint H x rowOrder extra hBound) := by
  ext modelPoint
  constructor
  · intro hModelPoint
    obtain ⟨point, hPointExtra, rfl⟩ := Finset.mem_image.mp hModelPoint
    by_cases hPointActive : point ∈ middleFourExtraActiveDomain H x
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨point, Finset.mem_filter.mpr ⟨hPointExtra, hPointActive⟩, ?_⟩
      exact (middleFourExtraPoint_active
        H x rowOrder extra hBound hPointActive).symm
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨point, Finset.mem_sdiff.mpr ⟨hPointExtra, hPointActive⟩, rfl⟩
  · intro hModelPoint
    rcases Finset.mem_union.mp hModelPoint with hOld | hFresh
    · obtain ⟨point, hPointOld, hPointEq⟩ := Finset.mem_image.mp hOld
      obtain ⟨hPointExtra, hPointActive⟩ := Finset.mem_filter.mp hPointOld
      apply Finset.mem_image.mpr
      refine ⟨point, hPointExtra, ?_⟩
      rw [middleFourExtraPoint_active
        H x rowOrder extra hBound hPointActive]
      exact hPointEq
    · obtain ⟨point, hPointFresh, hPointEq⟩ := Finset.mem_image.mp hFresh
      exact Finset.mem_image.mpr
        ⟨point, (Finset.mem_sdiff.mp hPointFresh).1, hPointEq⟩

theorem middleFourSemanticBase_image_extraPoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (extra : G413.Row alpha)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16) :
    (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset =
        (middleFourSemanticLiftFamily H x).image (fun row ↦
          row.image (middleFourExtraPoint H x rowOrder extra hBound)) := by
  let basePoint := middleFourBasePoint rowOrder x
  let extraPoint := middleFourExtraPoint H x rowOrder extra hBound
  calc
    (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset =
        (blocker (avoidPoint H x)).image (fun row ↦
          (avoidBlockerLift H x row).image basePoint) := by
      simpa [basePoint] using middleFourSemanticLiftBaseRows_toFinset
        H x rowOrder hHBlockerRows hBRows hLength
    _ = (blocker (avoidPoint H x)).image (fun row ↦
          (avoidBlockerLift H x row).image extraPoint) := by
      apply Finset.image_congr
      intro source hSource
      apply Finset.image_congr
      intro point hPoint
      exact (middleFourExtraPoint_active H x rowOrder extra hBound
        (middleFourAvoidBlockerLift_subset_active_insert
          H x hSource hPoint)).symm
    _ = (middleFourSemanticLiftFamily H x).image (fun row ↦
          row.image extraPoint) := by
      rw [middleFourSemanticLiftFamily, Finset.image_image]
      rfl

theorem middleFourSemanticSeven_contradicts_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hHBlockerCard : (blocker H).card = 8)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hLengthLeSeven : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length ≤ 7)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 7)
    (hMaxDegree : MaxDegreeAtMost (blocker H) 4)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hCheck : middleFourDegreeFourValuesCheck
      (fourActualSupportMultiplicity rowOrder).toList = true) :
    False := by
  obtain ⟨extra, hExtraBlocker, hExtraNotFamily, hBlocker⟩ :=
    middleFourSemanticLiftFamily_exists_extra
      H x hAvoidBlockerCard hHBlockerCard
  have hExtraCard : extra.card ≤ 8 := by
    have hUpper := minimalTransversal_card_le_rows
      (mem_blocker.mp hExtraBlocker)
    omega
  have hFreshCard : (middleFourExtraFresh H x extra).card ≤ 8 := by
    exact (Finset.card_le_card (Finset.sdiff_subset)).trans hExtraCard
  have hBound : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length +
        (middleFourExtraFresh H x extra).card < 16 := by omega
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  let extraPoint := middleFourExtraPoint H x rowOrder extra hBound
  let extraModel := extra.image extraPoint
  have hBaseCard : base.toFinset.card = 7 := by
    calc
      base.toFinset.card = (blocker (avoidPoint H x)).card := by
        simpa [base] using middleFourSemanticLiftBaseRows_card
          H x rowOrder hHBlockerRows hBRows hLength
      _ = 7 := hAvoidBlockerCard
  obtain ⟨old, hOldPowerset, hOldSet⟩ :=
    middleFourExtraOldModel_exists_list x rowOrder extra
      hExtraBlocker hExtraNotFamily hBlocker hHBlockerRows hBRows
        hLength hMaxDegree
  have hExtraModelEq : extraModel = old.toFinset ∪
      (middleFourModelFreshPointList
        (fourActualSupportMultiplicity rowOrder).toList
        (middleFourExtraFresh H x extra).card).toFinset := by
    calc
      extraModel =
          (extra.filter fun point ↦ point ∈
            middleFourExtraActiveDomain H x).image
              (middleFourBasePoint rowOrder x) ∪
            (middleFourExtraFresh H x extra).image extraPoint := by
        simpa [extraModel, extraPoint] using
          middleFourExtra_image_decompose
            H x rowOrder extra hBound
      _ = old.toFinset ∪
          (middleFourModelFreshPointList
            (fourActualSupportMultiplicity rowOrder).toList
            (middleFourExtraFresh H x extra).card).toFinset := by
        rw [hOldSet, middleFourExtraFresh_image
          H x rowOrder extra hBound]
  have hExtraEnumerated : extraModel ∈
      middleFourModelExtraRowList
        (fourActualSupportMultiplicity rowOrder).toList base := by
    unfold middleFourModelExtraRowList
    apply List.mem_flatMap.mpr
    refine ⟨old, ?_, ?_⟩
    · simpa [base] using hOldPowerset
    · apply List.mem_map.mpr
      refine ⟨(middleFourExtraFresh H x extra).card,
        List.mem_range.mpr (by omega), ?_⟩
      exact hExtraModelEq.symm
  have hCandidate : extraModel :: base ∈
      middleFourModelCandidateRows
        (fourActualSupportMultiplicity rowOrder).toList := by
    unfold middleFourModelCandidateRows
    apply List.mem_flatMap.mpr
    refine ⟨middleFourSemanticSelected H x rowOrder, hSelection, ?_⟩
    unfold middleFourModelCandidateRowsForSelection
    rw [if_neg (by rw [hBaseCard]; decide), if_pos hBaseCard]
    exact List.mem_map.mpr ⟨extraModel, hExtraEnumerated, rfl⟩
  have hBaseImage : base.toFinset =
      (middleFourSemanticLiftFamily H x).image (fun row ↦
        row.image extraPoint) := by
    simpa [base, extraPoint] using middleFourSemanticBase_image_extraPoint
      H x rowOrder extra hHBlockerRows hBRows hLength hBound
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
          (fun row ↦ row.image extraPoint) := by
        rw [Finset.image_insert]
      _ = (blocker H).image (fun row ↦ row.image extraPoint) := by
        rw [← hBlocker]
  have hSupportSubset : (blocker H).biUnion id ⊆
      middleFourExtraActiveDomain H x ∪ middleFourExtraFresh H x extra :=
    middleFourBlocker_biUnion_subset_extra_domain H x extra hBlocker
  have hPointMap : Set.InjOn extraPoint ((blocker H).biUnion id) :=
    (middleFourExtraPoint_injOn_active_union_fresh
      H x rowOrder extra hLength hBound).mono hSupportSubset
  have hRowMap := blocker_row_image_injOn_of_injOn_active hPointMap
  have hCandidateBlockerCard :
      (blocker (extraModel :: base).toFinset).card = 8 := by
    rw [hCandidateSet, blocker_image_eq_of_injOn_active hPointMap,
      Finset.card_image_iff.mpr hRowMap,
      blocker_involution hHClutter, hHCard]
  have hCheckCandidate :=
    (List.all_eq_true.mp hCheck) (extraModel :: base) hCandidate
  have hBlockerNe : (fastBlocker (extraModel :: base)).card ≠ 8 :=
    of_decide_eq_true hCheckCandidate
  rw [fastBlocker_eq_blocker] at hBlockerNe
  exact hBlockerNe hCandidateBlockerCard

theorem eightRows_degreeFour_impossible {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8)
    {x : alpha} (hDegree : degree H x = 4) :
    False := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 4 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using G419.avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    exact hHRows row (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using G419.blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hKUpper : ∀ row ∈ K, row.card ≤ 8 := by
    intro row hRow
    have hRowH : row ∈ H :=
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
    have hRowDual : row ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hRowH
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hRowDual)).trans_eq hBCard
  have hMaxDegree : MaxDegreeAtMost (blocker H) 4 :=
    (middle_maxDegreesAtMost_four
      hHClutter hHCard hHRows hBRows hBCard).2
  have hPairUpper : (pairRows (blocker K)).card ≤ 4 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          G419.pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 4 := hMaxDegree x
  have hBlockerUpper : (blocker K).card ≤ 8 := by
    have hLift := G419.blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  let rowOrder := fourRowOrder hKCard
  have hCheck := middleFourActualSupportMultiplicity_degreeFour_check
    rowOrder hKClutter hBKRows hKRows hKUpper hBlockerUpper hPairUpper
  have hLength := middleFourActualPoints_length_lt_sixteen
    rowOrder hKClutter hBKRows hKRows hKUpper hBlockerUpper hPairUpper
  have hLengthLeSeven := middleFourActualPoints_length_le_seven
    rowOrder hKClutter hBKRows hKRows hKUpper hBlockerUpper hPairUpper
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hBRows hBKRows hLength (hMaxDegree x)
  have hSelection := middleFourSemanticSelected_mem_liftSelectionRows
    H x rowOrder hSelectionBound
  have hModelCard := middleFourActualModelBlocker_card_seven_or_eight
    rowOrder hKClutter hBKRows hKRows hKUpper hBlockerUpper hPairUpper
  have hModelCardEq := middleFourModelBlocker_card_eq_actual
    rowOrder hBKRows hLength
  rcases hModelCard with hSeven | hEight
  · have hBKCard : (blocker K).card = 7 := by omega
    exact middleFourSemanticSeven_contradicts_check
      x rowOrder hHClutter hHCard hBRows hBCard hBKRows hLength
        hLengthLeSeven (by simpa [K] using hBKCard) hMaxDegree
          hSelection hCheck
  · have hBKCard : (blocker K).card = 8 := by omega
    exact middleFourSemanticBase_eight_contradicts_check
      x rowOrder hHClutter hHCard hBRows hBKRows hLength
        (by simpa [K] using hBKCard) hBCard hSelection hCheck

theorem middle_maxDegreesAtMost_three {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    MaxDegreeAtMost H 3 ∧ MaxDegreeAtMost (blocker H) 3 := by
  have hDegreeFour := middle_maxDegreesAtMost_four
    hHClutter hHCard hHRows hBRows hBCard
  constructor
  · intro x
    have hUpper := hDegreeFour.1 x
    by_contra hNot
    have hDegree : degree H x = 4 := by omega
    exact eightRows_degreeFour_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
  · intro x
    have hUpper := hDegreeFour.2 x
    by_contra hNot
    have hDegree : degree (blocker H) x = 4 := by omega
    have hDualClutter := blocker_isClutter H
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    have hDualCard : (blocker (blocker H)).card = 8 := by
      simpa [blocker_involution hHClutter] using hHCard
    exact eightRows_degreeFour_impossible
      hDualClutter hBCard hBRows hDualRows hDualCard hDegree

end AiMathLab.P0054.G420
