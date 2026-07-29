import AiMathLab.P0054FanoAdjacentEightFiveBasics
import Mathlib.Combinatorics.Colex

/-!
# Excluding the Fano eight-plus-five branch on an arbitrary finite ground

Seven chosen predecessor pairs form a seven-row subfamily.  The eighth row
is either wholly inside the Fano core, where the finite core certificate
applies, or contains an inactive point.  In the latter case its active part
is either empty, giving an isolated-row product bound, or nonempty, in which
case the row is reduced to that active part plus one fresh point and sent to
the eight-point finite certificate.
-/

namespace AiMathLab.P0054.FanoAdjacentEightFiveActual

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.FanoAdjacentSevenSixFinite
open AiMathLab.P0054.FanoAdjacentSevenSixSound
open AiMathLab.P0054.FanoAdjacentEightFiveFinite
open AiMathLab.P0054.FanoAdjacentEightFiveSound
open AiMathLab.P0054.FanoAdjacentEightFiveBasics

private def fanoEightFiveExtraMask
    (extra : G413.Row MiddleFourModelPoint) : Nat :=
  ∑ point ∈ extra, 2 ^ point.val

private theorem mem_fanoEightFiveExtendedActive_iff
    (point : MiddleFourModelPoint) :
    point ∈ fanoEightFiveExtendedActive ↔ point.val ≤ 7 := by
  fin_cases point <;> decide

private theorem fanoEightFiveExtraMask_decode
    (extra : G413.Row MiddleFourModelPoint)
    (hExtra : extra ⊆ fanoEightFiveExtendedActive) :
    fanoEightFiveExtendedActive.filter (fun point ↦
      (fanoEightFiveExtraMask extra).testBit point.val) = extra := by
  have hsum : fanoEightFiveExtraMask extra =
      ∑ value ∈ extra.image Fin.val, 2 ^ value := by
    rw [fanoEightFiveExtraMask, Finset.sum_image]
    exact Fin.val_injective.injOn
  have hbits := Finset.toFinset_bitIndices_sum_two_pow
    (extra.image Fin.val)
  rw [← hsum] at hbits
  ext point
  simp only [Finset.mem_filter, ← Nat.mem_bitIndices,
    ← List.mem_toFinset, hbits, Finset.mem_image]
  constructor
  · rintro ⟨_hPointActive, source, hSource, hValue⟩
    exact Fin.val_injective hValue ▸ hSource
  · intro hPoint
    exact ⟨hExtra hPoint, point, hPoint, rfl⟩

private theorem fanoEightFiveExtraMask_lt_256
    (extra : G413.Row MiddleFourModelPoint)
    (hExtra : extra ⊆ fanoEightFiveExtendedActive) :
    fanoEightFiveExtraMask extra < 256 := by
  have hsum : fanoEightFiveExtraMask extra =
      ∑ value ∈ extra.image Fin.val, 2 ^ value := by
    rw [fanoEightFiveExtraMask, Finset.sum_image]
    exact Fin.val_injective.injOn
  rw [hsum]
  simpa using Nat.geomSum_lt (s := extra.image Fin.val) (m := 2) (n := 8)
    (by omega) (by
      intro value hValue
      obtain ⟨point, hPoint, rfl⟩ := Finset.mem_image.mp hValue
      have hPointActive := hExtra hPoint
      rw [mem_fanoEightFiveExtendedActive_iff] at hPointActive
      omega)

private theorem mem_fanoEightFiveCoreExtras_of_subset
    {extra : G413.Row MiddleFourModelPoint}
    (hExtra : extra ⊆ fanoEightFiveExtendedActive) :
    extra ∈ fanoEightFiveCoreExtras := by
  let mask : Fin 256 :=
    ⟨fanoEightFiveExtraMask extra,
      fanoEightFiveExtraMask_lt_256 extra hExtra⟩
  unfold fanoEightFiveCoreExtras
  apply List.mem_map.mpr
  refine ⟨mask, List.mem_finRange mask, ?_⟩
  simpa only [mask] using fanoEightFiveExtraMask_decode extra hExtra

theorem fano_eight_five_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle small large : G413.Hypergraph alpha}
    {pointMap : alpha → MiddleFourModelPoint}
    (hMiddleCard : middle.card = 7)
    (hMiddleRows : ∀ line ∈ middle, line.card = 3)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hPointMap : Set.InjOn pointMap (middle.biUnion id))
    (hModel : sevenEightFanoBase =
      middle.image (fun row ↦ row.image pointMap))
    (hSmallBlocker : small = blocker large)
    (hLargeBlocker : large = blocker small)
    (hSmallRows : RowsCardAtLeast small 2)
    (hLargeRows : RowsCardAtLeast large 4)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line)
    (hSmallCard : small.card = 8)
    (hLargeCard : large.card = 5) : False := by
  classical
  let predecessor : middle → G413.Row alpha := fun line ↦
    (hPred line.1 line.2).choose
  have hPredecessorMem (line : middle) : predecessor line ∈ small :=
    (hPred line.1 line.2).choose_spec.1
  have hPredecessorSubset (line : middle) :
      predecessor line ⊂ line.1 :=
    (hPred line.1 line.2).choose_spec.2
  have hPredecessorInj : Set.InjOn predecessor
      (↑middle.attach : Set middle) := by
    intro first _hFirst second _hSecond hRowsEq
    apply Subtype.ext
    by_contra hLines
    have hSubset : predecessor first ⊆ first.1 ∩ second.1 := by
      intro point hPoint
      exact Finset.mem_inter.mpr
        ⟨hPredecessorSubset first |>.1 hPoint,
          hPredecessorSubset second |>.1 (hRowsEq ▸ hPoint)⟩
    have hLower := hSmallRows (predecessor first)
      (hPredecessorMem first)
    have hUpper := Finset.card_le_card hSubset
    have hIntersection := hMiddlePairs first.1 first.2
      second.1 second.2 hLines
    omega
  let selected : G413.Hypergraph alpha :=
    middle.attach.image predecessor
  have hSelectedCard : selected.card = 7 := by
    dsimp only [selected]
    rw [Finset.card_image_of_injOn hPredecessorInj,
      Finset.card_attach, hMiddleCard]
  have hSelectedSubset : selected ⊆ small := by
    intro row hRow
    obtain ⟨line, _hLineAttach, rfl⟩ := Finset.mem_image.mp hRow
    exact hPredecessorMem line
  have hSelectedActive : selected.biUnion id ⊆ middle.biUnion id := by
    intro point hPoint
    obtain ⟨row, hRowSelected, hPointRow⟩ :=
      Finset.mem_biUnion.mp hPoint
    obtain ⟨line, _hLineAttach, hRowEq⟩ :=
      Finset.mem_image.mp hRowSelected
    rw [← hRowEq] at hPointRow
    exact Finset.mem_biUnion.mpr
      ⟨line.1, line.2, (hPredecessorSubset line).1 hPointRow⟩
  have hSelectedRowsTwo : ∀ row ∈ selected, row.card = 2 := by
    intro row hRow
    obtain ⟨line, _hLineAttach, hRowEq⟩ := Finset.mem_image.mp hRow
    rw [← hRowEq]
    have hLower := hSmallRows (predecessor line)
      (hPredecessorMem line)
    have hUpper := Finset.card_lt_card (hPredecessorSubset line)
    rw [hMiddleRows line.1 line.2] at hUpper
    omega
  have hDifferenceCard : (small \ selected).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSelectedSubset,
      hSmallCard, hSelectedCard]
  obtain ⟨extra, hDifference⟩ := Finset.card_eq_one.mp hDifferenceCard
  have hExtraSmall : extra ∈ small := by
    have : extra ∈ small \ selected := by simp [hDifference]
    exact (Finset.mem_sdiff.mp this).1
  have hExtraNotSelected : extra ∉ selected := by
    have : extra ∈ small \ selected := by simp [hDifference]
    exact (Finset.mem_sdiff.mp this).2
  have hSmallForm : small = insert extra selected := by
    have hUnion := Finset.sdiff_union_of_subset hSelectedSubset
    rw [hDifference] at hUnion
    simpa using hUnion.symm
  have hSmallClutter : IsClutter small := by
    rw [hSmallBlocker]
    exact blocker_isClutter large
  have hExtraActualCardLower : 2 ≤ extra.card :=
    hSmallRows extra hExtraSmall
  have hExtraActualCardUpper : extra.card ≤ 5 := by
    have hExtraBlocker : extra ∈ blocker large := by
      rw [← hSmallBlocker]
      exact hExtraSmall
    have hPrivateUpper :=
      minimalTransversal_card_le_rows (mem_blocker.mp hExtraBlocker)
    rw [hLargeCard] at hPrivateUpper
    exact hPrivateUpper
  have hPointMapSelected : Set.InjOn pointMap (selected.biUnion id) :=
    hPointMap.mono hSelectedActive
  have hSelectedRowMapInj : Set.InjOn
      (fun row : G413.Row alpha ↦ row.image pointMap) selected :=
    row_image_injOn_of_injOn hSelectedActive hPointMap
  let Q : G413.Hypergraph MiddleFourModelPoint :=
    selected.image (fun row ↦ row.image pointMap)
  have hQCard : Q.card = 7 := by
    dsimp only [Q]
    rw [Finset.card_image_of_injOn hSelectedRowMapInj, hSelectedCard]
  have hEach : ∀ line ∈ sevenEightFanoBase,
      ∃ pair ∈ Q, pair.card = 2 ∧ pair ⊆ line := by
    intro line hLine
    have hLineImage : line ∈
        middle.image (fun row ↦ row.image pointMap) := by
      rw [← hModel]
      exact hLine
    obtain ⟨source, hSourceMiddle, hSourceImage⟩ :=
      Finset.mem_image.mp hLineImage
    let sourceSubtype : middle := ⟨source, hSourceMiddle⟩
    have hSelectedMem : predecessor sourceSubtype ∈ selected := by
      exact Finset.mem_image.mpr ⟨sourceSubtype, by simp, rfl⟩
    have hRowDomain : predecessor sourceSubtype ⊆ middle.biUnion id := by
      intro point hPoint
      exact Finset.mem_biUnion.mpr
        ⟨source, hSourceMiddle,
          (hPredecessorSubset sourceSubtype).1 hPoint⟩
    have hImageCard :
        ((predecessor sourceSubtype).image pointMap).card =
          (predecessor sourceSubtype).card :=
      Finset.card_image_iff.mpr (hPointMap.mono hRowDomain)
    refine ⟨(predecessor sourceSubtype).image pointMap, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨predecessor sourceSubtype, hSelectedMem, rfl⟩
    · rw [hImageCard, hSelectedRowsTwo _ hSelectedMem]
    · intro modelPoint hModelPoint
      obtain ⟨point, hPointRow, rfl⟩ :=
        Finset.mem_image.mp hModelPoint
      rw [← hSourceImage]
      exact Finset.mem_image.mpr
        ⟨point, (hPredecessorSubset sourceSubtype).1 hPointRow, rfl⟩
  have hSelectedImageBlocker :
      blocker Q = (blocker selected).image
        (fun row ↦ row.image pointMap) := by
    dsimp only [Q]
    exact blocker_image_eq_of_injOn_active hPointMapSelected
  have hSelectedBlockerCardEq :
      (blocker Q).card = (blocker selected).card := by
    rw [hSelectedImageBlocker,
      Finset.card_image_of_injOn
        (blocker_row_image_injOn_of_injOn_active hPointMapSelected)]
  have hSelectedBlockerLower : 4 ≤ (blocker selected).card := by
    have hModelLower := fano_selected_pair_family_blocker_card_ge_four
      hQCard hEach
    rwa [hSelectedBlockerCardEq] at hModelLower
  have hMapMiddleActive : ∀ point ∈ middle.biUnion id,
      pointMap point ∈ sevenEightFanoActive := by
    intro point hPoint
    obtain ⟨line, hLineMiddle, hPointLine⟩ :=
      Finset.mem_biUnion.mp hPoint
    have hLineImage : line.image pointMap ∈ sevenEightFanoBase := by
      rw [hModel]
      exact Finset.mem_image.mpr ⟨line, hLineMiddle, rfl⟩
    exact sevenEight_fano_rows_active _ hLineImage
      (Finset.mem_image.mpr ⟨point, hPointLine, rfl⟩)
  by_cases hExtraCore : extra ⊆ middle.biUnion id
  · have hSmallActive : small.biUnion id ⊆ middle.biUnion id := by
      intro point hPoint
      obtain ⟨row, hRowSmall, hPointRow⟩ :=
        Finset.mem_biUnion.mp hPoint
      rw [hSmallForm] at hRowSmall
      rcases Finset.mem_insert.mp hRowSmall with rfl | hRowSelected
      · exact hExtraCore hPointRow
      · exact hSelectedActive
          (Finset.mem_biUnion.mpr ⟨row, hRowSelected, hPointRow⟩)
    have hPointMapSmall : Set.InjOn pointMap (small.biUnion id) :=
      hPointMap.mono hSmallActive
    let extraImage : G413.Row MiddleFourModelPoint := extra.image pointMap
    obtain ⟨rows, hRowsSelection, hRowsEq⟩ :=
      exists_checked_selection_of_one_pair_per_fano_line hQCard hEach
    have hExtraImageSubset : extraImage ⊆ sevenEightFanoActive := by
      intro modelPoint hModelPoint
      obtain ⟨point, hPointExtra, rfl⟩ :=
        Finset.mem_image.mp hModelPoint
      exact hMapMiddleActive point (hExtraCore hPointExtra)
    have hExtraCandidate : extraImage ∈ fanoEightFiveCoreExtras := by
      apply mem_fanoEightFiveCoreExtras_of_subset
      exact hExtraImageSubset.trans
        (Finset.subset_insert fanoEightFiveFresh sevenEightFanoActive)
    have hExtraCardEq : extraImage.card = extra.card :=
      Finset.card_image_iff.mpr (hPointMap.mono hExtraCore)
    have hExtraCardLower : 2 ≤ extraImage.card := by
      rw [hExtraCardEq]
      exact hExtraActualCardLower
    have hExtraCardUpper : extraImage.card ≤ 5 := by
      rw [hExtraCardEq]
      exact hExtraActualCardUpper
    have hMappedSmall :
        small.image (fun row ↦ row.image pointMap) =
          insert extraImage Q := by
      rw [hSmallForm, Finset.image_insert]
    have hMappedClutter : IsClutter (insert extraImage Q) := by
      rw [← hMappedSmall]
      exact isClutter_image_of_injOn_biUnion
        pointMap hSmallClutter hPointMapSmall
    have hMappedBlocker :
        blocker (insert extraImage Q) =
          (blocker small).image (fun row ↦ row.image pointMap) := by
      rw [← hMappedSmall]
      exact blocker_image_eq_of_injOn_active hPointMapSmall
    have hMappedBlockerRows :
        RowsCardAtLeast (blocker (insert extraImage Q)) 4 := by
      intro imageRow hImageRow
      rw [hMappedBlocker] at hImageRow
      obtain ⟨row, hRowBlocker, rfl⟩ :=
        Finset.mem_image.mp hImageRow
      have hRowLarge : row ∈ large := by
        rw [hLargeBlocker]
        exact hRowBlocker
      have hRowDomain : row ⊆ small.biUnion id :=
        blocker_row_subset_biUnion hRowBlocker
      have hImageCard : (row.image pointMap).card = row.card :=
        Finset.card_image_iff.mpr (hPointMapSmall.mono hRowDomain)
      rw [hImageCard]
      exact hLargeRows row hRowLarge
    have hRowsClutter : IsClutter (insert extraImage rows.toFinset) := by
      rw [hRowsEq]
      exact hMappedClutter
    have hRowsBlockerRows :
        RowsCardAtLeast (blocker (insert extraImage rows.toFinset)) 4 := by
      rw [hRowsEq]
      exact hMappedBlockerRows
    have hModelLower :
        6 ≤ (blocker (insert extraImage rows.toFinset)).card :=
      fanoEightFiveCoreSelectionCheck_sound hRowsSelection hExtraCandidate
        hExtraCardLower hExtraCardUpper hRowsClutter hRowsBlockerRows
    have hMappedBlockerCard :
        (blocker (insert extraImage rows.toFinset)).card = large.card := by
      rw [hRowsEq, hMappedBlocker,
        Finset.card_image_of_injOn
          (blocker_row_image_injOn_of_injOn_active hPointMapSmall),
        ← hLargeBlocker]
    rw [hMappedBlockerCard, hLargeCard] at hModelLower
    omega
  · obtain ⟨fresh, hFreshExtra, hFreshNotCore⟩ :=
      Finset.not_subset.mp hExtraCore
    have hFreshInactive : ∀ row ∈ selected, fresh ∉ row := by
      intro row hRowSelected hFreshRow
      exact hFreshNotCore (hSelectedActive
        (Finset.mem_biUnion.mpr ⟨row, hRowSelected, hFreshRow⟩))
    let activePart : G413.Row alpha :=
      extra ∩ middle.biUnion id
    by_cases hActivePart : activePart.Nonempty
    · let reduced : G413.Row alpha := insert fresh activePart
      have hFreshNotActivePart : fresh ∉ activePart := by
        simp only [activePart, Finset.mem_inter, not_and]
        intro _hFreshExtra
        exact hFreshNotCore
      have hReducedFull : reduced ⊆ extra := by
        intro point hPoint
        simp only [reduced, Finset.mem_insert] at hPoint
        rcases hPoint with rfl | hPointActive
        · exact hFreshExtra
        · exact (Finset.mem_inter.mp hPointActive).1
      have hNewInactive : ∀ point ∈ extra \ reduced,
          ∀ row ∈ selected, point ∉ row := by
        intro point hPointNew row hRowSelected hPointRow
        have hPointCore : point ∈ middle.biUnion id :=
          hSelectedActive
            (Finset.mem_biUnion.mpr
              ⟨row, hRowSelected, hPointRow⟩)
        have hPointActivePart : point ∈ activePart :=
          Finset.mem_inter.mpr
            ⟨(Finset.mem_sdiff.mp hPointNew).1, hPointCore⟩
        exact (Finset.mem_sdiff.mp hPointNew).2 (by
          simp [reduced, hPointActivePart])
      have hReducedClutter : IsClutter (insert reduced selected) := by
        apply isClutter_insert_row_reduction
          (full := extra) (fresh := fresh)
        · rw [← hSmallForm]
          exact hSmallClutter
        · exact hReducedFull
        · simp [reduced]
        · exact hFreshInactive
      have hBlockerSubset : blocker (insert reduced selected) ⊆
          blocker (insert extra selected) :=
        blocker_insert_subset_of_row_extension hReducedFull hNewInactive
      have hReducedDualRows : RowsCardAtLeast
          (blocker (insert reduced selected)) 4 := by
        intro row hRowReduced
        have hRowFull : row ∈ blocker (insert extra selected) :=
          hBlockerSubset hRowReduced
        have hRowLarge : row ∈ large := by
          rw [hLargeBlocker, hSmallForm]
          exact hRowFull
        exact hLargeRows row hRowLarge
      have hReducedCardLower : 2 ≤ reduced.card := by
        have hActiveCard : 1 ≤ activePart.card :=
          Finset.one_le_card.mpr hActivePart
        simp [reduced, hFreshNotActivePart]
        omega
      have hReducedCardUpper : reduced.card ≤ 5 :=
        (Finset.card_le_card hReducedFull).trans hExtraActualCardUpper
      let reducedMap : alpha → MiddleFourModelPoint := fun point ↦
        if point ∈ middle.biUnion id then pointMap point
        else fanoEightFiveFresh
      have hFreshModelNotActive :
          fanoEightFiveFresh ∉ sevenEightFanoActive := by
        rw [sevenEight_mem_fano_active_iff]
        decide
      have hReducedMapBaseInj : Set.InjOn reducedMap
          (↑(insert fresh (middle.biUnion id)) : Set alpha) := by
        intro first hFirst second hSecond hEq
        have hFirstMem : first ∈ insert fresh (middle.biUnion id) :=
          hFirst
        have hSecondMem : second ∈ insert fresh (middle.biUnion id) :=
          hSecond
        change (if first ∈ middle.biUnion id then pointMap first
            else fanoEightFiveFresh) =
          (if second ∈ middle.biUnion id then pointMap second
            else fanoEightFiveFresh) at hEq
        by_cases hFirstCore : first ∈ middle.biUnion id <;>
            by_cases hSecondCore : second ∈ middle.biUnion id
        · rw [if_pos hFirstCore, if_pos hSecondCore] at hEq
          exact hPointMap hFirstCore hSecondCore hEq
        · have hFirstImageActive :=
            hMapMiddleActive first hFirstCore
          rw [if_pos hFirstCore, if_neg hSecondCore] at hEq
          have hImageEq : pointMap first = fanoEightFiveFresh := hEq
          rw [hImageEq] at hFirstImageActive
          exact (hFreshModelNotActive hFirstImageActive).elim
        · have hSecondImageActive :=
            hMapMiddleActive second hSecondCore
          rw [if_neg hFirstCore, if_pos hSecondCore] at hEq
          have hImageEq : fanoEightFiveFresh = pointMap second := hEq
          rw [← hImageEq] at hSecondImageActive
          exact (hFreshModelNotActive hSecondImageActive).elim
        · have hFirstFresh : first = fresh := by
            simpa [hFirstCore] using hFirstMem
          have hSecondFresh : second = fresh := by
            simpa [hSecondCore] using hSecondMem
          exact hFirstFresh.trans hSecondFresh.symm
      have hReducedActive :
          (insert reduced selected).biUnion id ⊆
            insert fresh (middle.biUnion id) := by
        intro point hPoint
        obtain ⟨row, hRow, hPointRow⟩ :=
          Finset.mem_biUnion.mp hPoint
        simp only [Finset.mem_insert] at hRow
        rcases hRow with hRowReduced | hRowSelected
        · subst row
          change point ∈ insert fresh activePart at hPointRow
          rw [Finset.mem_insert] at hPointRow
          rcases hPointRow with rfl | hPointActive
          · simp
          · exact Finset.mem_insert_of_mem
              (Finset.mem_inter.mp hPointActive).2
        · exact Finset.mem_insert_of_mem (hSelectedActive
            (Finset.mem_biUnion.mpr
              ⟨row, hRowSelected, hPointRow⟩))
      have hReducedMapInj : Set.InjOn reducedMap
          (↑((insert reduced selected).biUnion id) : Set alpha) :=
        hReducedMapBaseInj.mono hReducedActive
      let coreImage : G413.Row MiddleFourModelPoint :=
        activePart.image pointMap
      let modelExtra : G413.Row MiddleFourModelPoint :=
        insert fanoEightFiveFresh coreImage
      have hCoreImageSubset : coreImage ⊆ sevenEightFanoActive := by
        intro modelPoint hModelPoint
        obtain ⟨point, hPointActivePart, rfl⟩ :=
          Finset.mem_image.mp hModelPoint
        exact hMapMiddleActive point
          (Finset.mem_inter.mp hPointActivePart).2
      have hModelExtraSubset :
          modelExtra ⊆ fanoEightFiveExtendedActive := by
        intro modelPoint hModelPoint
        simp only [modelExtra, Finset.mem_insert] at hModelPoint
        rcases hModelPoint with rfl | hModelPointCore
        · simp [fanoEightFiveExtendedActive]
        · exact Finset.mem_insert_of_mem
            (hCoreImageSubset hModelPointCore)
      have hExtraCandidate : modelExtra ∈ fanoEightFiveCoreExtras := by
        exact mem_fanoEightFiveCoreExtras_of_subset hModelExtraSubset
      have hReducedImage : reduced.image reducedMap = modelExtra := by
        dsimp only [modelExtra]
        rw [show reduced = insert fresh activePart by rfl,
          Finset.image_insert]
        have hFreshMap : reducedMap fresh = fanoEightFiveFresh := by
          change (if fresh ∈ middle.biUnion id then pointMap fresh
            else fanoEightFiveFresh) = fanoEightFiveFresh
          rw [if_neg hFreshNotCore]
        rw [hFreshMap]
        apply congrArg (insert fanoEightFiveFresh)
        dsimp only [coreImage]
        apply Finset.image_congr
        intro point hPointActivePart
        have hPointCore := (Finset.mem_inter.mp hPointActivePart).2
        change (if point ∈ middle.biUnion id then pointMap point
          else fanoEightFiveFresh) = pointMap point
        rw [if_pos hPointCore]
      have hSelectedImage : selected.image
          (fun row ↦ row.image reducedMap) = Q := by
        dsimp only [Q]
        apply Finset.image_congr
        intro row hRowSelected
        apply Finset.image_congr
        intro point hPointRow
        have hPointCore : point ∈ middle.biUnion id :=
          hSelectedActive (Finset.mem_biUnion.mpr
            ⟨row, hRowSelected, hPointRow⟩)
        change (if point ∈ middle.biUnion id then pointMap point
          else fanoEightFiveFresh) = pointMap point
        rw [if_pos hPointCore]
      have hMappedReducedFamily :
          (insert reduced selected).image
              (fun row ↦ row.image reducedMap) =
            insert modelExtra Q := by
        rw [Finset.image_insert, hReducedImage, hSelectedImage]
      have hMappedClutter : IsClutter (insert modelExtra Q) := by
        rw [← hMappedReducedFamily]
        exact isClutter_image_of_injOn_biUnion
          reducedMap hReducedClutter hReducedMapInj
      have hReducedDomain : reduced ⊆
          (insert reduced selected).biUnion id := by
        intro point hPoint
        exact Finset.mem_biUnion.mpr
          ⟨reduced, by simp, hPoint⟩
      have hModelExtraCardEq : modelExtra.card = reduced.card := by
        rw [← hReducedImage]
        exact Finset.card_image_iff.mpr
          (hReducedMapInj.mono hReducedDomain)
      have hMappedBlocker : blocker (insert modelExtra Q) =
          (blocker (insert reduced selected)).image
            (fun row ↦ row.image reducedMap) := by
        rw [← hMappedReducedFamily]
        exact blocker_image_eq_of_injOn_active hReducedMapInj
      have hMappedBlockerRows : RowsCardAtLeast
          (blocker (insert modelExtra Q)) 4 := by
        intro imageRow hImageRow
        rw [hMappedBlocker] at hImageRow
        obtain ⟨row, hRowBlocker, rfl⟩ :=
          Finset.mem_image.mp hImageRow
        have hRowDomain : row ⊆
            (insert reduced selected).biUnion id :=
          blocker_row_subset_biUnion hRowBlocker
        have hImageCard : (row.image reducedMap).card = row.card :=
          Finset.card_image_iff.mpr
            (hReducedMapInj.mono hRowDomain)
        rw [hImageCard]
        exact hReducedDualRows row hRowBlocker
      obtain ⟨rows, hRowsSelection, hRowsEq⟩ :=
        exists_checked_selection_of_one_pair_per_fano_line hQCard hEach
      have hRowsClutter :
          IsClutter (insert modelExtra rows.toFinset) := by
        rw [hRowsEq]
        exact hMappedClutter
      have hRowsBlockerRows : RowsCardAtLeast
          (blocker (insert modelExtra rows.toFinset)) 4 := by
        rw [hRowsEq]
        exact hMappedBlockerRows
      have hModelLower :
          6 ≤ (blocker (insert modelExtra rows.toFinset)).card :=
        fanoEightFiveCoreSelectionCheck_sound hRowsSelection
          hExtraCandidate
          (by rw [hModelExtraCardEq]; exact hReducedCardLower)
          (by rw [hModelExtraCardEq]; exact hReducedCardUpper)
          hRowsClutter hRowsBlockerRows
      have hReducedLower :
          6 ≤ (blocker (insert reduced selected)).card := by
        rw [hRowsEq, hMappedBlocker,
          Finset.card_image_of_injOn
            (blocker_row_image_injOn_of_injOn_active hReducedMapInj)]
          at hModelLower
        exact hModelLower
      have hLargeLower : 6 ≤ large.card := by
        calc
          6 ≤ (blocker (insert reduced selected)).card := hReducedLower
          _ ≤ (blocker (insert extra selected)).card :=
            Finset.card_le_card hBlockerSubset
          _ = large.card := by rw [← hSmallForm, ← hLargeBlocker]
      rw [hLargeCard] at hLargeLower
      omega
    · have hDisjoint : ∀ row ∈ selected, Disjoint extra row := by
        intro row hRowSelected
        rw [Finset.disjoint_left]
        intro point hPointExtra hPointRow
        apply hActivePart
        exact ⟨point, Finset.mem_inter.mpr
          ⟨hPointExtra, hSelectedActive
            (Finset.mem_biUnion.mpr
              ⟨row, hRowSelected, hPointRow⟩)⟩⟩
      have hProduct := isolatedRow_product_le_blocker_card
        hSmallForm hDisjoint
      have hLargeLower : 8 ≤ large.card := by
        calc
          8 = 2 * 4 := by norm_num
          _ ≤ extra.card * (blocker selected).card :=
            Nat.mul_le_mul hExtraActualCardLower hSelectedBlockerLower
          _ ≤ (blocker small).card := hProduct
          _ = large.card := by rw [← hLargeBlocker]
      rw [hLargeCard] at hLargeLower
      omega

end AiMathLab.P0054.FanoAdjacentEightFiveActual
