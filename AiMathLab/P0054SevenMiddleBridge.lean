import AiMathLab.P0054SevenExactBridge
import AiMathLab.P0054MiddleFifteen
import AiMathLab.P0054MiddleSixteenBridge

/-!
# Aggregating the remaining middle-layer exclusions

The total-fifteen theorem is unconditional.  The total-sixteen theorem needs
only the seven-plus-nine endpoint.  Total fourteen remains an adjacent-layer
statement about the actual canonical family and is therefore kept as a
separate explicit input.
-/

universe u

namespace AiMathLab.P0054.SevenMiddleBridge

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413
open AiMathLab.P0054.CanonicalBlocker
open AiMathLab.P0054.CanonicalProfiles

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem canonical_middle_interval_excluded
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hFourteen :
      F.card ≤ 54 →
      (canonicalLayers 7 F (3 : Fin 7)).card = 14 → False)
    (hSevenNine : ∀ {K : G413.Hypergraph α},
      IsClutter K →
      K.card = 7 →
      RowsCardAtLeast K 3 →
      RowsCardAtLeast (blocker K) 3 →
      (blocker K).card = 9 → False)
    (hFamilyCard : F.card ≤ 54)
    (hLower : 14 ≤ (canonicalLayers 7 F (3 : Fin 7)).card)
    (hUpper : (canonicalLayers 7 F (3 : Fin 7)).card ≤ 16) : False := by
  classical
  rcases exists_homogeneousAtom_of_signature_bound F hground with ⟨H, hH⟩
  have hsaturated := canonicalLayers_saturated_of_homogeneousAtom
    (by decide : 0 < 7) F H hsat hH
  let S : G413.Hypergraph α :=
    smallTrace (canonicalLayers 7 F (3 : Fin 7)) H
  let C : G413.Hypergraph α :=
    largeComplementTrace (canonicalLayers 7 F (3 : Fin 7)) H
  have hTrace :
      S.card + C.card = (canonicalLayers 7 F (3 : Fin 7)).card := by
    exact canonicalLayer_trace_card_sum hH (3 : Fin 7)
  have hSRows : RowsCardAtLeast S 3 := by
    exact smallTrace_rows_cardAtLeast (F := F) (H := H) (3 : Fin 7)
  have hCRows : RowsCardAtLeast C 3 := by
    simpa [C] using largeComplementTrace_rows_cardAtLeast
      (k := 7) (F := F) (H := H) (by decide : 0 < 7) hsat hH
        (3 : Fin 7)
  have hSClutter : IsClutter S := by
    exact smallTrace_isClutter (H := H) (hsaturated (3 : Fin 7)).1
  have hMutual : S = blocker C ∧ C = blocker S := by
    exact canonicalLayer_mutual_blockers (k := 7) (F := F) (H := H)
      (by decide : 0 < 7) hsat hH (3 : Fin 7) (by decide) (by decide)
  have hBRows : RowsCardAtLeast (blocker S) 3 := by
    rw [← hMutual.2]
    exact hCRows
  have hCases :
      (canonicalLayers 7 F (3 : Fin 7)).card = 14 ∨
      (canonicalLayers 7 F (3 : Fin 7)).card = 15 ∨
      (canonicalLayers 7 F (3 : Fin 7)).card = 16 := by
    omega
  rcases hCases with hCard | hCard | hCard
  · exact hFourteen hFamilyCard hCard
  · have hTotal : S.card + (blocker S).card = 15 := by
      rw [← hMutual.2, hTrace, hCard]
    exact AiMathLab.P0054.MiddleFifteen.middle_fifteen_impossible
      hSClutter hTotal hSRows hBRows
  · have hTotal : S.card + (blocker S).card = 16 := by
      rw [← hMutual.2, hTrace, hCard]
    exact
      AiMathLab.P0054.MiddleSixteenBridge.middle_sixteen_impossible_of_seven_nine
        hSevenNine hSClutter hTotal hSRows hBRows

theorem family_card_lower_of_fourteen_and_seven_nine_exclusions
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α)
    (hFourteen :
      F.card ≤ 54 →
      (canonicalLayers 7 F (3 : Fin 7)).card = 14 → False)
    (hSevenNine : ∀ {K : G413.Hypergraph α},
      IsClutter K →
      K.card = 7 →
      RowsCardAtLeast K 3 →
      RowsCardAtLeast (blocker K) 3 →
      (blocker K).card = 9 → False) :
    55 ≤ F.card := by
  apply
    AiMathLab.P0054.SevenExactBridge.family_card_lower_of_middle_interval_exclusion
      hsat hground hexternal
  exact canonical_middle_interval_excluded hsat hground hFourteen hSevenNine

end AiMathLab.P0054.SevenMiddleBridge
