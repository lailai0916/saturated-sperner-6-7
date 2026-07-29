import AiMathLab.P0053Parameterized56
import AiMathLab.P0053GenericCompatibility

/-!
# Compatibility with the frozen P0053 `Fin 10` certificate

This is the only parameterized-construction module importing the frozen F1
side.  It identifies the `H = Fin 3` realization with the published family
and then transports the two saturation predicates.
-/

namespace AiMathLab.P0053Parameterized56

open AiMathLab.SaturatedSperner

/-- Source-label equivalence: the seven core values stay at `0,...,6`, and
the three atom values become `7,8,9`. -/
def fin7SumFin3EquivFin10 : Fin 7 ⊕ Fin 3 ≃ Fin 10 :=
  finSumFinEquiv

@[simp] theorem fin7SumFin3EquivFin10_inl (i : Fin 7) :
    fin7SumFin3EquivFin10 (Sum.inl i) = ⟨i.val, by omega⟩ := by
  rfl

@[simp] theorem fin7SumFin3EquivFin10_inr (h : Fin 3) :
    fin7SumFin3EquivFin10 (Sum.inr h) = ⟨7 + h.val, by omega⟩ := by
  rfl

/-- Exact family equality, not merely equality of cardinalities or masks.
This is a closed finite compatibility regression. -/
theorem parameterized56_fin3_map_eq_published56 :
    mapFamily fin7SumFin3EquivFin10 (parameterized56 (Fin 3)) =
      AiMathLab.P0053.published56 := by
  set_option maxRecDepth 100000 in
    decide

/-- The generic parameterized predicate at `H = Fin 3` is equivalent to the
legacy frozen F1 predicate on the published family. -/
theorem parameterized56_fin3_saturation_iff_frozen :
    IsSaturatedKSperner 7 (parameterized56 (Fin 3)) ↔
      AiMathLab.P0053.IsSaturatedKSperner 7
        AiMathLab.P0053.published56 := by
  constructor
  · intro hParameterized
    have hMapped :
        IsSaturatedKSperner 7
          (mapFamily fin7SumFin3EquivFin10
            (parameterized56 (Fin 3))) :=
      (isSaturatedKSperner_mapFamily_iff
        fin7SumFin3EquivFin10 7 (parameterized56 (Fin 3))).mpr
          hParameterized
    rw [parameterized56_fin3_map_eq_published56] at hMapped
    exact (AiMathLab.P0053.p0053_isSaturatedKSperner_iff_generic
      7 AiMathLab.P0053.published56).mpr hMapped
  · intro hFrozen
    have hMapped :
        IsSaturatedKSperner 7 AiMathLab.P0053.published56 :=
      (AiMathLab.P0053.p0053_isSaturatedKSperner_iff_generic
        7 AiMathLab.P0053.published56).mp hFrozen
    rw [← parameterized56_fin3_map_eq_published56] at hMapped
    exact (isSaturatedKSperner_mapFamily_iff
      fin7SumFin3EquivFin10 7 (parameterized56 (Fin 3))).mp hMapped

/-- Compatibility-only recovery of the parameterized theorem from the frozen
F1 saturation certificate. -/
theorem parameterized56_fin3_from_frozen_f1 :
    IsSaturatedKSperner 7 (parameterized56 (Fin 3)) :=
  parameterized56_fin3_saturation_iff_frozen.mpr
    AiMathLab.P0053.published56_saturated

/-- Compatibility-only recovery of the frozen statement from the generic
parameterized theorem. -/
theorem frozen_f1_from_parameterized56 :
    AiMathLab.P0053.IsSaturatedKSperner 7
      AiMathLab.P0053.published56 :=
  parameterized56_fin3_saturation_iff_frozen.mp
    (parameterized56_saturated (H := Fin 3) (by decide))

end AiMathLab.P0053Parameterized56
