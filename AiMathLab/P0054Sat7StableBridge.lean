import AiMathLab.P0054Parameterized55
import AiMathLab.SaturatedSperner.StableSaturation

/-!
# The final stable-number bridge for seven-Sperner families

This module isolates the routine final step from the difficult canonical
lower bound.  The explicit parameterized family supplies attainment.  A
finite-ground lower theorem with the homogeneous-atom and external-set
hypotheses supplies optimality past one explicit threshold.
-/

namespace AiMathLab.P0054.Sat7StableBridge

open AiMathLab.SaturatedSperner
open AiMathLab.SaturatedSperner.ParameterizedAtom

/-- A threshold large enough both for the signature pigeonhole argument and
for realizing the eight-point template with a nontrivial atom. -/
def threshold : Nat := 3 * 2 ^ 55

noncomputable def constructionEquiv
    {n : Nat} (hn : threshold ≤ n) :
    AiMathLab.SaturatedSperner.ParameterizedAtom.Ground 8 (Fin (n - 8)) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by
    simp only [AiMathLab.SaturatedSperner.ParameterizedAtom.Ground,
      Fintype.card_sum, Fintype.card_fin]
    unfold threshold at hn
    omega)

noncomputable def construction
    {n : Nat} (hn : threshold ≤ n) :
      AiMathLab.SaturatedSperner.Family (Fin n) :=
  mapFamily (constructionEquiv hn)
    (Parameterized55.family (Fin (n - 8)))

theorem construction_certificate
    {n : Nat} (hn : threshold ≤ n) :
    IsSaturatedKSperner 7 (construction hn) ∧
      (construction hn).card = 55 := by
  have hAtom : 2 < n - 8 := by
    unfold threshold at hn
    omega
  have hAtomCard : 2 < Fintype.card (Fin (n - 8)) := by
    simpa using hAtom
  constructor
  · exact (isSaturatedKSperner_mapFamily_iff
      (constructionEquiv hn) 7
      (Parameterized55.family (Fin (n - 8)))).mpr
        (Parameterized55.family_saturated hAtomCard)
  · simp [construction, Parameterized55.family_card hAtomCard]

/-- Convert a canonical lower theorem on finite labelled grounds into the
unconditional lower bound needed in the stable range. -/
theorem lower_at_of_canonical_lower
    (hcanonical : ∀ {n : Nat}
      (F : AiMathLab.SaturatedSperner.Family (Fin n)),
      IsSaturatedKSperner 7 F →
      3 * 2 ^ F.card ≤ n →
      F.card < 2 ^ n →
      55 ≤ F.card)
    {n : Nat} (hn : threshold ≤ n)
    (F : AiMathLab.SaturatedSperner.Family (Fin n))
    (hsat : IsSaturatedKSperner 7 F) :
    55 ≤ F.card := by
  by_cases hsmall : F.card ≤ 55
  · apply hcanonical F hsat
    · have hp : 2 ^ F.card ≤ 2 ^ 55 :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
      exact (Nat.mul_le_mul_left 3 hp).trans hn
    · have h55n : 55 < n := by
        unfold threshold at hn
        omega
      exact lt_of_le_of_lt hsmall (h55n.trans n.lt_two_pow_self)
  · omega

/-- Once the canonical finite-ground lower theorem is available, the exact
eventual value follows without any further combinatorial assumptions. -/
theorem stable_of_canonical_lower
    (hcanonical : ∀ {n : Nat}
      (F : AiMathLab.SaturatedSperner.Family (Fin n)),
      IsSaturatedKSperner 7 F →
      3 * 2 ^ F.card ≤ n →
      F.card < 2 ^ n →
      55 ≤ F.card) :
    IsStableSaturationNumber 7 55 := by
  refine ⟨threshold, fun n hn => ?_⟩
  exact ⟨⟨construction hn, (construction_certificate hn).1,
    (construction_certificate hn).2⟩,
    lower_at_of_canonical_lower hcanonical hn⟩

end AiMathLab.P0054.Sat7StableBridge
