import AiMathLab.P0054SevenBaseline

/-!
# Global arithmetic bridge for the exact seven-Sperner lower bound

After the componentwise canonical profile is known, a family of size at most
fifty-four has a middle canonical layer of size between fourteen and sixteen.
Thus all remaining combinatorics can be exposed through one local theorem
excluding precisely that interval for the actual canonical layer.
-/

universe u

namespace AiMathLab.P0054.SevenExactBridge

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.CanonicalProfiles
open AiMathLab.P0054.SevenBaseline

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem middle_layer_card_le_sixteen_of_family_card_le_fifty_four
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α)
    (hcard : F.card ≤ 54) :
    (canonicalLayers 7 F (3 : Fin 7)).card ≤ 16 := by
  have hprofile := canonical_profile_lower hsat hground hexternal
  have h0 := hprofile (0 : Fin 7)
  have h1 := hprofile (1 : Fin 7)
  have h2 := hprofile (2 : Fin 7)
  have h4 := hprofile (4 : Fin 7)
  have h5 := hprofile (5 : Fin 7)
  have h6 := hprofile (6 : Fin 7)
  have hsum := sum_canonicalLayer_cards_eq hsat.1
  change 1 ≤ (canonicalLayers 7 F (0 : Fin 7)).card at h0
  change 1 ≤ (canonicalLayers 7 F (6 : Fin 7)).card at h6
  simp [baselineProfile, Fin.sum_univ_succ] at h1 h2 h4 h5 hsum
  omega

/-- The complete global lower bound follows once the actual middle layer is
excluded throughout the only interval compatible with a low total. -/
theorem family_card_lower_of_middle_interval_exclusion
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α)
    (hmiddle : F.card ≤ 54 →
      14 ≤ (canonicalLayers 7 F (3 : Fin 7)).card →
      (canonicalLayers 7 F (3 : Fin 7)).card ≤ 16 → False) :
    55 ≤ F.card := by
  by_contra hnot
  have hcard : F.card ≤ 54 := by omega
  have hmiddleLower :=
    canonical_profile_lower hsat hground hexternal (3 : Fin 7)
  have hmiddleUpper :=
    middle_layer_card_le_sixteen_of_family_card_le_fifty_four
      hsat hground hexternal hcard
  exact hmiddle hcard (by simpa [baselineProfile] using hmiddleLower) hmiddleUpper

end AiMathLab.P0054.SevenExactBridge
