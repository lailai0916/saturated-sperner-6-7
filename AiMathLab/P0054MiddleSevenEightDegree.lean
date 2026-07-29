import AiMathLab.P0054MiddleSevenEightBasics
import AiMathLab.P0054MiddleSevenEightFinite
import AiMathLab.P0054G420.MiddleFourDegreeFourExclusion

/-!
# The degree-four exclusion for the seven-plus-eight split

The four rows avoiding a degree-four point have the unique `K₄`
multiplicity profile.  Because the opposite seven-row side has maximum
degree three, no optional lifted blocker row is selected.  The resulting
seven lifted rows form the Fano plane, whose blocker has seven rather than
eight rows.  Injecting the original eight-row family into this model gives
the contradiction.
-/

namespace AiMathLab.P0054.MiddleSevenEightDegree

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightBasics
open AiMathLab.P0054.MiddleSevenEightFinite

theorem semanticLiftBase_blocker_card_eq_family {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (x : α)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBRows : RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16)
    (hCard : (blocker (avoidPoint H x)).card = (blocker H).card) :
    (blocker (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)).toFinset).card = H.card := by
  let pointMap := middleFourBasePoint rowOrder x
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hLiftEq : middleFourSemanticLiftFamily H x = blocker H :=
    middleFourSemanticLiftFamily_eq_blocker_of_card_eq H x hCard
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
  change (blocker base.toFinset).card = H.card
  rw [hBaseSet, hBlockerImage, Finset.card_image_iff.mpr hRowMap,
    blocker_involution hHClutter]

theorem eightRows_degreeFour_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 3)
    {x : α} (hDegree : degree H x = 4) :
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
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hRowDual)
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
  have hSameCard : (blocker (avoidPoint H x)).card = (blocker H).card := by
    simpa [K, hBKCard, hBCard]
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hBaseEq : base = sevenEightZeroBase sevenEightK4Values := by
    simp [base, sevenEightZeroBase, hValues, hSelectionEmpty]
  have hBaseBlockerCard : (blocker base.toFinset).card = 8 := by
    simpa [base, hHCard] using semanticLiftBase_blocker_card_eq_family
      x rowOrder hHClutter hBRows hBKRows hLength hSameCard
  have hBaseNe :
      (fastBlocker (sevenEightZeroBase sevenEightK4Values)).card ≠ 8 :=
    of_decide_eq_true sevenEight_k4_base_check
  rw [fastBlocker_eq_blocker, ← hBaseEq] at hBaseNe
  exact hBaseNe hBaseBlockerCard

theorem eightRows_maxDegreeAtMost_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    MaxDegreeAtMost H 3 := by
  have hBMaxDegree : MaxDegreeAtMost (blocker H) 3 := by
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    exact sevenRows_maxDegreeAtMost_three (blocker_isClutter H) hBCard
      hBRows hDualRows (by simpa [blocker_involution hHClutter] using hHCard)
  have hUpper := MiddleSevenEightBasics.eightRows_maxDegreeAtMost_four
    hHClutter hHCard hHRows hBRows hBCard
  intro x
  have hxUpper := hUpper x
  by_contra hNot
  have hDegree : degree H x = 4 := by omega
  exact eightRows_degreeFour_impossible hHClutter hHCard hHRows hBRows
    hBCard hBMaxDegree hDegree

end AiMathLab.P0054.MiddleSevenEightDegree
