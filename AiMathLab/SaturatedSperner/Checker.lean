import AiMathLab.SaturatedSperner.ChainWitness

/-!
# Executable checkers for strict chains and saturation

All local checkers operate only on their finite input family or witness.  The
ground type is required to be finite only for the final checker that enumerates
every finite subset.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [DecidableEq α]

/-- Boolean checker for one explicit ascending strict chain. -/
def isStrictChainInChecker (F : Family α) : List (Finset α) → Bool
  | [] => true
  | [A] => decide (A ∈ F)
  | A :: B :: tail =>
      decide (A ∈ F) && decide (A ⊂ B) &&
        isStrictChainInChecker F (B :: tail)

theorem isStrictChainInChecker_eq_true
    (F : Family α) (c : List (Finset α)) :
    isStrictChainInChecker F c = true ↔ IsStrictChainIn F c := by
  induction c with
  | nil => simp [isStrictChainInChecker, IsStrictChainIn]
  | cons A tail ih =>
      cases tail with
      | nil => simp [isStrictChainInChecker, IsStrictChainIn]
      | cons B rest =>
          simp [isStrictChainInChecker, IsStrictChainIn, ih, and_assoc]

theorem isStrictChainInChecker_sound
    {F : Family α} {c : List (Finset α)}
    (h : isStrictChainInChecker F c = true) :
    IsStrictChainIn F c :=
  (isStrictChainInChecker_eq_true F c).mp h

theorem isStrictChainInChecker_complete
    {F : Family α} {c : List (Finset α)}
    (h : IsStrictChainIn F c) :
    isStrictChainInChecker F c = true :=
  (isStrictChainInChecker_eq_true F c).mpr h

/-- Boolean checker for a length-`r` chain through `S`. -/
def strictChainWitnessChecker
    (r : Nat) (F : Family α) (S : Finset α)
    (c : List (Finset α)) : Bool :=
  decide (c.length = r) && isStrictChainInChecker F c &&
    decide (S ∈ c)

theorem strictChainWitnessChecker_eq_true
    (r : Nat) (F : Family α) (S : Finset α)
    (c : List (Finset α)) :
    strictChainWitnessChecker r F S c = true ↔
      IsStrictChainWitness r F S c := by
  simp [strictChainWitnessChecker, IsStrictChainWitness,
    isStrictChainInChecker_eq_true, and_assoc]

theorem strictChainWitnessChecker_sound
    {r : Nat} {F : Family α} {S : Finset α}
    {c : List (Finset α)}
    (h : strictChainWitnessChecker r F S c = true) :
    IsStrictChainWitness r F S c :=
  (strictChainWitnessChecker_eq_true r F S c).mp h

theorem strictChainWitnessChecker_complete
    {r : Nat} {F : Family α} {S : Finset α}
    {c : List (Finset α)}
    (h : IsStrictChainWitness r F S c) :
    strictChainWitnessChecker r F S c = true :=
  (strictChainWitnessChecker_eq_true r F S c).mpr h

theorem hasStrictChainThrough_iff_exists_checked_witness
    (r : Nat) (F : Family α) (S : Finset α) :
    HasStrictChainThrough r F S ↔
      ∃ c : List (Finset α),
        strictChainWitnessChecker r F S c = true := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, strictChainWitnessChecker_complete hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, strictChainWitnessChecker_sound hc⟩

/-- Dynamic-programming endpoints: `chainEnds d F` contains exactly the
possible endpoints of chains of length `d + 1`. -/
def chainEnds : Nat → Family α → Family α
  | 0, F => F
  | d + 1, F =>
      F.filter fun B => ∃ A ∈ chainEnds d F, A ⊂ B

theorem mem_chainEnds_iff
    (d : Nat) (F : Family α) (B : Finset α) :
    B ∈ chainEnds d F ↔ HasStrictChainEndingAt d F B := by
  induction d generalizing B with
  | zero => simp [chainEnds, HasStrictChainEndingAt]
  | succ d ih =>
      simp only [chainEnds, Finset.mem_filter, HasStrictChainEndingAt]
      constructor
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mp hA, hAB⟩
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mpr hA, hAB⟩

/-- Dynamic-programming checker for a chain of exactly `r` members. -/
def hasStrictChainChecker : Nat → Family α → Bool
  | 0, _ => true
  | d + 1, F => decide (chainEnds d F).Nonempty

theorem hasStrictChainChecker_eq_true
    (r : Nat) (F : Family α) :
    hasStrictChainChecker r F = true ↔ HasStrictChainLength r F := by
  cases r with
  | zero => simp [hasStrictChainChecker, HasStrictChainLength]
  | succ d =>
      simp only [hasStrictChainChecker, decide_eq_true_eq,
        HasStrictChainLength]
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, (mem_chainEnds_iff d F B).mp hB⟩
      · rintro ⟨B, hB⟩
        exact ⟨B, (mem_chainEnds_iff d F B).mpr hB⟩

theorem hasStrictChainChecker_sound
    {r : Nat} {F : Family α}
    (h : hasStrictChainChecker r F = true) :
    HasStrictChainLength r F :=
  (hasStrictChainChecker_eq_true r F).mp h

theorem hasStrictChainChecker_complete
    {r : Nat} {F : Family α}
    (h : HasStrictChainLength r F) :
    hasStrictChainChecker r F = true :=
  (hasStrictChainChecker_eq_true r F).mpr h

/-- Checker for the `k`-Sperner condition. -/
def isKSpernerChecker (k : Nat) (F : Family α) : Bool :=
  !(hasStrictChainChecker (k + 1) F)

theorem isKSpernerChecker_eq_true
    (k : Nat) (F : Family α) :
    isKSpernerChecker k F = true ↔ IsKSperner k F := by
  unfold isKSpernerChecker IsKSperner
  have hiff := hasStrictChainChecker_eq_true (k + 1) F
  rw [Bool.not_eq_true_eq_eq_false]
  constructor
  · intro hfalse hchain
    have htrue := hiff.mpr hchain
    rw [hfalse] at htrue
    contradiction
  · intro hno
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    exact hno (hiff.mp htrue)

theorem isKSpernerChecker_sound
    {k : Nat} {F : Family α}
    (h : isKSpernerChecker k F = true) : IsKSperner k F :=
  (isKSpernerChecker_eq_true k F).mp h

theorem isKSpernerChecker_complete
    {k : Nat} {F : Family α}
    (h : IsKSperner k F) : isKSpernerChecker k F = true :=
  (isKSpernerChecker_eq_true k F).mpr h

/-- Local saturation obligation at one supplied subset. -/
def saturationAtChecker
    (k : Nat) (F : Family α) (S : Finset α) : Bool :=
  decide (S ∈ F) ||
    hasStrictChainChecker (k + 1) (insert S F)

theorem saturationAtChecker_eq_true
    (k : Nat) (F : Family α) (S : Finset α) :
    saturationAtChecker k F S = true ↔
      S ∈ F ∨ HasStrictChainLength (k + 1) (insert S F) := by
  simp [saturationAtChecker, hasStrictChainChecker_eq_true]

theorem saturationAtChecker_sound
    {k : Nat} {F : Family α} {S : Finset α}
    (h : saturationAtChecker k F S = true) :
    S ∈ F ∨ HasStrictChainLength (k + 1) (insert S F) :=
  (saturationAtChecker_eq_true k F S).mp h

theorem saturationAtChecker_complete
    {k : Nat} {F : Family α} {S : Finset α}
    (h : S ∈ F ∨ HasStrictChainLength (k + 1) (insert S F)) :
    saturationAtChecker k F S = true :=
  (saturationAtChecker_eq_true k F S).mpr h

/-- Full saturation checker.  This is the only generic definition that needs
`[Fintype α]`, because it enumerates every `Finset α`. -/
def isSaturatedKSpernerChecker [Fintype α]
    (k : Nat) (F : Family α) : Bool :=
  isKSpernerChecker k F &&
    decide (∀ S : Finset α,
      S ∈ F ∨
        hasStrictChainChecker (k + 1) (insert S F) = true)

theorem isSaturatedKSpernerChecker_eq_true [Fintype α]
    (k : Nat) (F : Family α) :
    isSaturatedKSpernerChecker k F = true ↔
      IsSaturatedKSperner k F := by
  rw [isSaturatedKSpernerChecker, Bool.and_eq_true]
  rw [isKSpernerChecker_eq_true]
  simp only [decide_eq_true_eq, hasStrictChainChecker_eq_true]
  constructor
  · rintro ⟨hk, hall⟩
    refine ⟨hk, ?_⟩
    intro S hSF
    rcases hall S with hmem | hchain
    · exact False.elim (hSF hmem)
    · exact hchain
  · rintro ⟨hk, hsaturated⟩
    refine ⟨hk, ?_⟩
    intro S
    by_cases hSF : S ∈ F
    · exact Or.inl hSF
    · exact Or.inr (hsaturated S hSF)

theorem isSaturatedKSpernerChecker_sound [Fintype α]
    {k : Nat} {F : Family α}
    (h : isSaturatedKSpernerChecker k F = true) :
    IsSaturatedKSperner k F :=
  (isSaturatedKSpernerChecker_eq_true k F).mp h

theorem isSaturatedKSpernerChecker_complete [Fintype α]
    {k : Nat} {F : Family α}
    (h : IsSaturatedKSperner k F) :
    isSaturatedKSpernerChecker k F = true :=
  (isSaturatedKSpernerChecker_eq_true k F).mpr h

end AiMathLab.SaturatedSperner
