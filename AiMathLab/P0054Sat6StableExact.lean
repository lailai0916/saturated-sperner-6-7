import AiMathLab.P0054Sat6Exact
import AiMathLab.SaturatedSperner.StableSaturation

/-!
# The stable saturation number for six-Sperner families

The parameterized thirty-member construction is transported to every
sufficiently large labelled ground.  On the same range, the homogeneous-atom
lower bound applies to every saturated family of size at most thirty.
-/

namespace AiMathLab.P0054.Sat6StableExact

open AiMathLab.SaturatedSperner
open AiMathLab.SaturatedSperner.ParameterizedAtom

/-- A threshold that simultaneously supplies the homogeneous atom and enough
room for the parameterized construction. -/
def threshold : Nat := 3 * 2 ^ 30

noncomputable def constructionEquiv
    {n : Nat} (hn : threshold ≤ n) :
    Ground 6 (Fin (n - 6)) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by
    simp only [Ground, Fintype.card_sum, Fintype.card_fin]
    unfold threshold at hn
    omega)

noncomputable def construction
    {n : Nat} (hn : threshold ≤ n) : Family (Fin n) :=
  mapFamily (constructionEquiv hn)
    (Sat6Parameterized30.family (Fin (n - 6)))

theorem construction_certificate
    {n : Nat} (hn : threshold ≤ n) :
    IsSaturatedKSperner 6 (construction hn) ∧
      (construction hn).card = 30 := by
  have hAtom : 2 < n - 6 := by
    unfold threshold at hn
    omega
  have hAtomCard : 2 < Fintype.card (Fin (n - 6)) := by
    simpa using hAtom
  constructor
  · exact (isSaturatedKSperner_mapFamily_iff
      (constructionEquiv hn) 6
      (Sat6Parameterized30.family (Fin (n - 6)))).mpr
        (Sat6Parameterized30.family_saturated hAtomCard)
  · simp [construction, Sat6Parameterized30.family_card hAtomCard]

theorem lower_at
    {n : Nat} (hn : threshold ≤ n)
    (F : Family (Fin n)) (hsat : IsSaturatedKSperner 6 F) :
    30 ≤ F.card := by
  by_cases hsmall : F.card ≤ 30
  · apply Sat6Exact.family_card_lower hsat
    · simp only [Fintype.card_fin]
      have hp : 2 ^ F.card ≤ 2 ^ 30 :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
      exact (Nat.mul_le_mul_left 3 hp).trans hn
    · simp only [Fintype.card_fin]
      have h30n : 30 < n := by
        unfold threshold at hn
        omega
      exact lt_of_le_of_lt hsmall (h30n.trans n.lt_two_pow_self)
  · omega

/-- The exact eventual value, with attainment and optimality on every ground
past one explicit threshold. -/
theorem sat_six_eq_thirty : IsStableSaturationNumber 6 30 := by
  refine ⟨threshold, fun n hn => ?_⟩
  exact ⟨⟨construction hn, (construction_certificate hn).1,
    (construction_certificate hn).2⟩, lower_at hn⟩

end AiMathLab.P0054.Sat6StableExact
