/-
Copyright (c) 2026 AI Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Math Lab
-/
import Mathlib

/-! # Calibration theorems

Small known results used to verify that the local Lean and Mathlib toolchain works.
-/

namespace AiMathLab

/-- Calibration theorem used to verify that Mathlib is available. -/
theorem sum_first_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

end AiMathLab
