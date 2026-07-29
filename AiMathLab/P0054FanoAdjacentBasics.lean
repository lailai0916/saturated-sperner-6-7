import AiMathLab.P0054AdjacentExact
import AiMathLab.P0054FanoAdjacentBridge

/-!
# Structural basics for a Fano-adjacent blocker pair

Seven Fano lines force seven distinct two-point predecessor rows.  Together
with the exact adjacent lower bound, this leaves only five cardinal splits at
total at most thirteen.  Strict Fano successors also make all large rows
pairwise intersecting.
-/

namespace AiMathLab.P0054.FanoAdjacentBasics

open AiMathLab.P0054.G413

theorem fano_predecessors_card_ge_seven
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle small : G413.Hypergraph alpha}
    (hMiddleCard : middle.card = 7)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hSmallRows : RowsCardAtLeast small 2)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line) :
    7 ≤ small.card := by
  classical
  let predecessor : middle → Row alpha := fun line ↦
    (hPred line line.property).choose
  have hPredecessorMem (line : middle) : predecessor line ∈ small :=
    (hPred line line.property).choose_spec.1
  have hPredecessorSubset (line : middle) :
      predecessor line ⊂ line :=
    (hPred line line.property).choose_spec.2
  let embed : middle → small := fun line ↦
    ⟨predecessor line, hPredecessorMem line⟩
  have hEmbedInjective : Function.Injective embed := by
    intro first second hImage
    apply Subtype.ext
    by_contra hLines
    have hRowEq := congrArg Subtype.val hImage
    change predecessor first = predecessor second at hRowEq
    have hSubset : predecessor first ⊆ first.1 ∩ second.1 := by
      intro point hPoint
      exact Finset.mem_inter.mpr
        ⟨hPredecessorSubset first |>.1 hPoint,
          hPredecessorSubset second |>.1 (hRowEq ▸ hPoint)⟩
    have hLower := hSmallRows (predecessor first) (hPredecessorMem first)
    have hUpper := Finset.card_le_card hSubset
    have hIntersection := hMiddlePairs first.1 first.2 second.1 second.2 hLines
    omega
  have hCard := Fintype.card_le_of_injective embed hEmbedInjective
  simpa [hMiddleCard] using hCard

theorem exists_fano_predecessor_equiv
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle small : G413.Hypergraph alpha}
    (hMiddleCard : middle.card = 7)
    (hSmallCard : small.card = 7)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hSmallRows : RowsCardAtLeast small 2)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line) :
    ∃ predecessor : middle ≃ small,
      ∀ line, (predecessor line).1 ⊂ line.1 := by
  classical
  let predecessorRow : middle → Row alpha := fun line ↦
    (hPred line line.property).choose
  have hPredecessorMem (line : middle) : predecessorRow line ∈ small :=
    (hPred line line.property).choose_spec.1
  have hPredecessorSubset (line : middle) :
      predecessorRow line ⊂ line :=
    (hPred line line.property).choose_spec.2
  let predecessorFn : middle → small := fun line ↦
    ⟨predecessorRow line, hPredecessorMem line⟩
  have hInjective : Function.Injective predecessorFn := by
    intro first second hImage
    apply Subtype.ext
    by_contra hLines
    have hRowEq := congrArg Subtype.val hImage
    change predecessorRow first = predecessorRow second at hRowEq
    have hSubset : predecessorRow first ⊆ first.1 ∩ second.1 := by
      intro point hPoint
      exact Finset.mem_inter.mpr
        ⟨hPredecessorSubset first |>.1 hPoint,
          hPredecessorSubset second |>.1 (hRowEq ▸ hPoint)⟩
    have hLower := hSmallRows (predecessorRow first) (hPredecessorMem first)
    have hUpper := Finset.card_le_card hSubset
    have hIntersection := hMiddlePairs first.1 first.2 second.1 second.2 hLines
    omega
  have hCardEq : Fintype.card middle = Fintype.card small := by
    simpa [hMiddleCard, hSmallCard]
  have hBijective : Function.Bijective predecessorFn :=
    (Fintype.bijective_iff_injective_and_card predecessorFn).2
      ⟨hInjective, hCardEq⟩
  let predecessor : middle ≃ small :=
    Equiv.ofBijective predecessorFn hBijective
  refine ⟨predecessor, ?_⟩
  intro line
  change predecessorRow line ⊂ line.1
  exact hPredecessorSubset line

theorem fano_successors_pairwise_intersecting
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle large : G413.Hypergraph alpha}
    (hMiddleRows : ∀ line ∈ middle, line.card = 3)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hSucc : ∀ row ∈ large, ∃ line ∈ middle, line ⊂ row) :
    ∀ first ∈ large, ∀ second ∈ large, first ≠ second →
      (first ∩ second).Nonempty := by
  classical
  intro first hFirst second hSecond _hRows
  obtain ⟨firstLine, hFirstLine, hFirstSubset⟩ := hSucc first hFirst
  obtain ⟨secondLine, hSecondLine, hSecondSubset⟩ := hSucc second hSecond
  by_cases hLines : firstLine = secondLine
  · subst secondLine
    obtain ⟨point, hPointLine⟩ := Finset.card_pos.mp (by
      rw [hMiddleRows firstLine hFirstLine]
      omega)
    exact ⟨point, Finset.mem_inter.mpr
      ⟨hFirstSubset.1 hPointLine, hSecondSubset.1 hPointLine⟩⟩
  · obtain ⟨point, hPointLines⟩ := Finset.card_pos.mp (by
      rw [hMiddlePairs firstLine hFirstLine secondLine hSecondLine hLines]
      omega)
    exact ⟨point, Finset.mem_inter.mpr
      ⟨hFirstSubset.1 (Finset.mem_inter.mp hPointLines).1,
        hSecondSubset.1 (Finset.mem_inter.mp hPointLines).2⟩⟩

theorem fano_adjacent_cardinal_splits
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle small large : G413.Hypergraph alpha}
    (hMiddleCard : middle.card = 7)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hSmallBlocker : small = blocker large)
    (hLargeBlocker : large = blocker small)
    (hSmallRows : RowsCardAtLeast small 2)
    (hLargeRows : RowsCardAtLeast large 4)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line)
    (hTotal : small.card + large.card ≤ 13) :
    (small.card = 8 ∧ large.card = 4) ∨
      (small.card = 9 ∧ large.card = 4) ∨
      (small.card = 7 ∧ large.card = 5) ∨
      (small.card = 8 ∧ large.card = 5) ∨
      (small.card = 7 ∧ large.card = 6) := by
  classical
  have hSmallLower : 7 ≤ small.card :=
    fano_predecessors_card_ge_seven hMiddleCard hMiddlePairs
      hSmallRows hPred
  have hSmallClutter : IsClutter small := by
    rw [hSmallBlocker]
    exact blocker_isClutter large
  have hLargeClutter : IsClutter large := by
    rw [hLargeBlocker]
    exact blocker_isClutter small
  have hDoubleRows : RowsCardAtLeast (blocker small) 4 := by
    rw [← hLargeBlocker]
    exact hLargeRows
  have hTotalLower : 12 ≤ small.card + large.card := by
    have h :=
      AiMathLab.P0054.AdjacentExact.mutual_blocker_total_card_ge_twelve
        hSmallClutter hSmallRows hDoubleRows
    rwa [← hLargeBlocker] at h
  have hLargeLower : 2 ≤ large.card := by
    obtain ⟨line, hLine⟩ : middle.Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨row, hRowSmall, _hRowLine⟩ := hPred line hLine
    have hRowBlocker : row ∈ blocker large := by
      rw [← hSmallBlocker]
      exact hRowSmall
    exact (hSmallRows row hRowSmall).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hRowBlocker))
  have hLargeUpper : large.card ≤ 6 := by omega
  interval_cases hLargeCard : large.card
  · have hSixteen : 16 ≤ (blocker large).card :=
      AiMathLab.P0054.AdjacentLower.blocker_card_ge_sixteen_of_card_eq_two
        hLargeCard hLargeRows (by
          rw [← hSmallBlocker]
          exact hSmallRows)
    rw [← hSmallBlocker] at hSixteen
    omega
  · have hTwelve : 12 ≤ (blocker large).card :=
      AiMathLab.P0054.AdjacentLower.blocker_card_ge_twelve_of_card_eq_three
        hLargeCard hLargeRows (by
          rw [← hSmallBlocker]
          exact hSmallRows)
    rw [← hSmallBlocker] at hTwelve
    omega
  · have hEight : 8 ≤ (blocker large).card :=
      AiMathLab.P0054.AdjacentFour.four_set_blocker_card_ge_eight
        hLargeClutter hLargeCard hLargeRows (by
          rw [← hSmallBlocker]
          exact hSmallRows)
    rw [← hSmallBlocker] at hEight
    omega
  · omega
  · omega

theorem fano_adjacent_impossible_of_cardinal_bounds
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {middle small large : G413.Hypergraph alpha}
    (hMiddleCard : middle.card = 7)
    (hMiddlePairs : ∀ first ∈ middle, ∀ second ∈ middle,
      first ≠ second → (first ∩ second).card = 1)
    (hSmallBlocker : small = blocker large)
    (hLargeBlocker : large = blocker small)
    (hSmallRows : RowsCardAtLeast small 2)
    (hLargeRows : RowsCardAtLeast large 4)
    (hPred : ∀ line ∈ middle, ∃ row ∈ small, row ⊂ line)
    (hTotal : small.card + large.card ≤ 13)
    (hSeven : small.card = 7 → 7 ≤ large.card)
    (hEight : small.card = 8 → 6 ≤ large.card)
    (hFour : large.card = 4 → 10 ≤ small.card) : False := by
  rcases fano_adjacent_cardinal_splits hMiddleCard hMiddlePairs
      hSmallBlocker hLargeBlocker hSmallRows hLargeRows hPred hTotal with
    hEightFour | hNineFour | hSevenFive | hEightFive | hSevenSix
  · have := hFour hEightFour.2
    omega
  · have := hFour hNineFour.2
    omega
  · have := hSeven hSevenFive.1
    omega
  · have := hEight hEightFive.1
    omega
  · have := hSeven hSevenSix.1
    omega

end AiMathLab.P0054.FanoAdjacentBasics
