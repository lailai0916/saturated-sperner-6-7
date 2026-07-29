import AiMathLab.P0054FanoAdjacentSevenSixSound

/-!
# Realizing the Fano seven-plus-six certificate on an arbitrary finite ground

When the predecessor side has exactly seven rows, the seven strict
predecessors selected below the Fano lines exhaust it.  Consequently every
active point on that side lies on a Fano line, so the model point map is
injective on the whole active set.  The finite certificate can then be
transported through blocker and row images.
-/

namespace AiMathLab.P0054.FanoAdjacentSevenSixActual

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.FanoAdjacentBasics
open AiMathLab.P0054.FanoAdjacentSevenSixSound

theorem fano_seven_side_forces_large_card_ge_seven
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
    (hLargeBlocker : large = blocker small)
    (hSmallRows : RowsCardAtLeast small 2)
    (hLargeRows : RowsCardAtLeast large 4)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line)
    (hSmallCard : small.card = 7) :
    7 ≤ large.card := by
  classical
  obtain ⟨predecessor, hPredecessor⟩ :=
    exists_fano_predecessor_equiv hMiddleCard hSmallCard hMiddlePairs
      hSmallRows hPred
  have hSmallActive : small.biUnion id ⊆ middle.biUnion id := by
    intro point hPoint
    obtain ⟨row, hRowSmall, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
    obtain ⟨line, hLineEq⟩ := predecessor.surjective
      (⟨row, hRowSmall⟩ : small)
    have hPointPredecessor : point ∈ (predecessor line).1 := by
      rw [hLineEq]
      exact hPointRow
    exact Finset.mem_biUnion.mpr
      ⟨line.1, line.2, (hPredecessor line).1 hPointPredecessor⟩
  have hPointMapSmall : Set.InjOn pointMap (small.biUnion id) :=
    hPointMap.mono hSmallActive
  have hRowMapInj : Set.InjOn
      (fun row : G413.Row alpha ↦ row.image pointMap) small :=
    row_image_injOn_of_injOn hSmallActive hPointMap
  let Q : G413.Hypergraph MiddleFourModelPoint :=
    small.image (fun row ↦ row.image pointMap)
  have hQCard : Q.card = 7 := by
    dsimp only [Q]
    rw [Finset.card_image_of_injOn hRowMapInj, hSmallCard]
  have hEach : ∀ line ∈ sevenEightFanoBase,
      ∃ pair ∈ Q, pair.card = 2 ∧ pair ⊆ line := by
    intro line hLine
    have hLineImage : line ∈
        middle.image (fun row ↦ row.image pointMap) := by
      rw [← hModel]
      exact hLine
    obtain ⟨source, hSourceMiddle, hSourceImage⟩ :=
      Finset.mem_image.mp hLineImage
    obtain ⟨row, hRowSmall, hRowSource⟩ := hPred source hSourceMiddle
    have hRowCard : row.card = 2 := by
      have hLower := hSmallRows row hRowSmall
      have hUpper := Finset.card_lt_card hRowSource
      rw [hMiddleRows source hSourceMiddle] at hUpper
      omega
    have hRowDomain : row ⊆ middle.biUnion id := by
      intro point hPoint
      exact Finset.mem_biUnion.mpr
        ⟨source, hSourceMiddle, hRowSource.1 hPoint⟩
    have hImageCard : (row.image pointMap).card = row.card :=
      Finset.card_image_iff.mpr (hPointMap.mono hRowDomain)
    refine ⟨row.image pointMap, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨row, hRowSmall, rfl⟩
    · rw [hImageCard, hRowCard]
    · intro modelPoint hModelPoint
      obtain ⟨point, hPointRow, rfl⟩ := Finset.mem_image.mp hModelPoint
      rw [← hSourceImage]
      exact Finset.mem_image.mpr
        ⟨point, hRowSource.1 hPointRow, rfl⟩
  have hImageBlocker :
      blocker Q = (blocker small).image
        (fun row ↦ row.image pointMap) := by
    dsimp only [Q]
    exact blocker_image_eq_of_injOn_active hPointMapSmall
  have hQBlockerRows : RowsCardAtLeast (blocker Q) 4 := by
    intro imageRow hImageRow
    rw [hImageBlocker] at hImageRow
    obtain ⟨row, hRowBlocker, rfl⟩ := Finset.mem_image.mp hImageRow
    have hRowLarge : row ∈ large := by
      rw [hLargeBlocker]
      exact hRowBlocker
    have hRowDomain : row ⊆ small.biUnion id :=
      blocker_row_subset_biUnion hRowBlocker
    have hImageCard : (row.image pointMap).card = row.card :=
      Finset.card_image_iff.mpr (hPointMapSmall.mono hRowDomain)
    rw [hImageCard]
    exact hLargeRows row hRowLarge
  have hQBlockerLower : 7 ≤ (blocker Q).card :=
    fano_selected_pair_family_blocker_card_ge_seven
      hQCard hEach hQBlockerRows
  have hQBlockerCard : (blocker Q).card = large.card := by
    rw [hImageBlocker,
      Finset.card_image_of_injOn
        (blocker_row_image_injOn_of_injOn_active hPointMapSmall),
      ← hLargeBlocker]
  rwa [hQBlockerCard] at hQBlockerLower

theorem fano_seven_six_impossible
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
    (hLargeBlocker : large = blocker small)
    (hSmallRows : RowsCardAtLeast small 2)
    (hLargeRows : RowsCardAtLeast large 4)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line)
    (hSmallCard : small.card = 7)
    (hTotal : small.card + large.card ≤ 13) : False := by
  have hLargeLower := fano_seven_side_forces_large_card_ge_seven
    hMiddleCard hMiddleRows hMiddlePairs hPointMap hModel hLargeBlocker
      hSmallRows hLargeRows hPred hSmallCard
  omega

end AiMathLab.P0054.FanoAdjacentSevenSixActual
