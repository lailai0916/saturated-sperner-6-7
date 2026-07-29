import AiMathLab.SaturatedSperner
import AiMathLab.P0053Sat7

/-!
# Compatibility between the generic library and the frozen P0053 certificate

The legacy `HasStrictChainThrough` name denotes the erase-critical predicate,
not the generic explicit-witness predicate.  The published corollary below
only transports the already frozen saturation theorem.
-/

namespace AiMathLab.P0053

theorem p0053_hasStrictChainEndingAt_iff_generic
    (d : Nat) (F : Family) (B : GroundSubset) :
    HasStrictChainEndingAt d F B ↔
      AiMathLab.SaturatedSperner.HasStrictChainEndingAt d F B := by
  induction d generalizing B with
  | zero => rfl
  | succ d ih =>
      constructor
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mp hA, hAB⟩
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mpr hA, hAB⟩

theorem p0053_hasStrictChainLength_iff_generic
    (r : Nat) (F : Family) :
    HasStrictChainLength r F ↔
      AiMathLab.SaturatedSperner.HasStrictChainLength r F := by
  cases r with
  | zero => rfl
  | succ d =>
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, (p0053_hasStrictChainEndingAt_iff_generic d F B).mp hB⟩
      · rintro ⟨B, hB⟩
        exact ⟨B, (p0053_hasStrictChainEndingAt_iff_generic d F B).mpr hB⟩

theorem p0053_isKSperner_iff_generic
    (k : Nat) (F : Family) :
    IsKSperner k F ↔
      AiMathLab.SaturatedSperner.IsKSperner k F := by
  exact not_congr (p0053_hasStrictChainLength_iff_generic (k + 1) F)

theorem p0053_hasStrictChainThrough_iff_eraseCritical
    (r : Nat) (G : Family) (S : GroundSubset) :
    HasStrictChainThrough r G S ↔
      AiMathLab.SaturatedSperner.HasEraseCriticalStrictChain r G S := by
  exact and_congr
    (p0053_hasStrictChainLength_iff_generic r G)
    (not_congr (p0053_hasStrictChainLength_iff_generic r (G.erase S)))

theorem p0053_isSaturatedKSperner_iff_generic
    (k : Nat) (F : Family) :
    IsSaturatedKSperner k F ↔
      AiMathLab.SaturatedSperner.IsSaturatedKSperner k F := by
  constructor
  · rintro ⟨hk, hsaturated⟩
    refine ⟨(p0053_isKSperner_iff_generic k F).mp hk, ?_⟩
    intro S hSF
    exact (p0053_hasStrictChainLength_iff_generic (k + 1) (insert S F)).mp
      (hsaturated S hSF).1
  · rintro ⟨hk, hsaturated⟩
    have hkOld : IsKSperner k F :=
      (p0053_isKSperner_iff_generic k F).mpr hk
    refine ⟨hkOld, ?_⟩
    intro S hSF
    refine ⟨?_, ?_⟩
    · exact (p0053_hasStrictChainLength_iff_generic (k + 1) (insert S F)).mpr
        (hsaturated S hSF)
    · simpa [AiMathLab.P0053.IsKSperner, Finset.erase_insert, hSF] using hkOld

/-- The frozen published theorem, transported through the compatibility iff.
No concrete reflection block is unfolded or repeated here. -/
theorem published56_saturated_generic :
    AiMathLab.SaturatedSperner.IsSaturatedKSperner 7 published56 :=
  (p0053_isSaturatedKSperner_iff_generic 7 published56).mp
    published56_saturated

end AiMathLab.P0053
