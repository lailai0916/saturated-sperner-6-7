import AiMathLab.P0054G413.PairEndpoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace AiMathLab.P0054.G413

theorem sum_indicator_eq_degree {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) :
    Finset.sum H (fun E ↦ if x ∈ E then 1 else 0) = degree H x := by
  classical
  exact Finset.sum_boole (R := Nat) (fun E : Row α ↦ x ∈ E) H

theorem triangle_row_incidence {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {T : Row α} {a b c : α}
    (hT : IsTransversal H T)
    (hAB : ({a, b} : Row α) ∈ H)
    (hBC : ({b, c} : Row α) ∈ H)
    (hCA : ({c, a} : Row α) ∈ H) :
    2 ≤ (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) +
      (if c ∈ T then 1 else 0) := by
  obtain ⟨x, hxT, hx⟩ := hT {a, b} hAB
  have hab : a ∈ T ∨ b ∈ T := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxT
    · exact Or.inr hxT
  obtain ⟨x, hxT, hx⟩ := hT {b, c} hBC
  have hbc : b ∈ T ∨ c ∈ T := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxT
    · exact Or.inr hxT
  obtain ⟨x, hxT, hx⟩ := hT {c, a} hCA
  have hca : c ∈ T ∨ a ∈ T := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxT
    · exact Or.inr hxT
  split <;> split <;> split <;> simp_all

theorem triangle_transversal_family_not_maxDegreeThree {α : Type*} [DecidableEq α]
    {H K : Hypergraph α} {a b c : α}
    (htrans : ∀ T ∈ K, IsTransversal H T)
    (hAB : ({a, b} : Row α) ∈ H)
    (hBC : ({b, c} : Row α) ∈ H)
    (hCA : ({c, a} : Row α) ∈ H)
    (hKcard : K.card = 5) :
    ¬ MaxDegreeAtMost K 3 := by
  intro hdegree
  have hsum :
      2 * K.card ≤
        Finset.sum K (fun T ↦
          (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) +
            (if c ∈ T then 1 else 0)) := by
    calc
      2 * K.card = Finset.sum K (fun _T ↦ 2) := by simp [Nat.mul_comm]
      _ ≤ Finset.sum K (fun T ↦
          (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) +
            (if c ∈ T then 1 else 0)) := by
        exact Finset.sum_le_sum fun T hT ↦ triangle_row_incidence (htrans T hT) hAB hBC hCA
  simp only [Finset.sum_add_distrib, sum_indicator_eq_degree] at hsum
  have ha := hdegree a
  have hb := hdegree b
  have hc := hdegree c
  omega

theorem triangle_blocker_not_maxDegreeThree {α : Type*}
    [Fintype α] [DecidableEq α] {H : Hypergraph α} {a b c : α}
    (hAB : ({a, b} : Row α) ∈ H)
    (hBC : ({b, c} : Row α) ∈ H)
    (hCA : ({c, a} : Row α) ∈ H)
    (hcard : (blocker H).card = 5) :
    ¬ MaxDegreeAtMost (blocker H) 3 := by
  apply triangle_transversal_family_not_maxDegreeThree
  · intro T hT
    exact (mem_blocker.mp hT).prop
  · exact hAB
  · exact hBC
  · exact hCA
  · exact hcard

theorem star_branch_impossible_of_residualLemma2 {α : Type*}
    [Fintype α] [DecidableEq α] {H : Hypergraph α} {x : α}
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hCenterDegree : degree H x = 3)
    (hAvoidLarge : ∀ E ∈ H, x ∉ E → 3 ≤ E.card)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hResidualLemma2 : ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    False := by
  let R := residual (blocker H) x
  have hBlockerR : blocker R = avoidPoint H x := by
    have h := blocker_residual (blocker H) x
    rw [blocker_involution hH] at h
    exact h
  have hAvoidCard : (avoidPoint H x).card = 5 := by
    have hpartition := card_avoidPoint_add_degree H x
    omega
  have hBlockerCard : (blocker R).card = 5 := by
    rw [hBlockerR, hAvoidCard]
  have hBlockerRows : RowsCardAtLeast (blocker R) 3 := by
    intro E hE
    rw [hBlockerR] at hE
    obtain ⟨hEH, hxE⟩ := mem_avoidPoint.mp hE
    exact hAvoidLarge E hEH hxE
  have hRcardUpper : R.card ≤ 5 := by
    have hle := residual_card_le (blocker H) x
    simpa [R, hDualCard] using hle
  have hRrows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hDualRows x
  have hRpairs : (pairRows R).card ≤ 3 := by
    have hle := pairRows_residual_card_le_degree hDualRows x
    exact hle.trans (hDualDegree x)
  have hRcardLower : 3 ≤ R.card := by
    have hpositive : 0 < (blocker R).card := by omega
    obtain ⟨T, hT⟩ := Finset.card_pos.mp hpositive
    have hTcard : 3 ≤ T.card := hBlockerRows T hT
    have hTle : T.card ≤ R.card :=
      minimalTransversal_card_le_rows (mem_blocker.mp hT)
    omega
  have hsix : 6 ≤ (blocker R).card :=
    hResidualLemma2 R (residual_isClutter _ _) hRcardLower hRcardUpper
      hRrows hRpairs hBlockerRows
  omega

theorem star_branch_impossible {α : Type*}
    [Fintype α] [DecidableEq α] {H : Hypergraph α} {x : α}
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hCenterDegree : degree H x = 3)
    (hAvoidLarge : ∀ E ∈ H, x ∉ E → 3 ≤ E.card)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3) :
    False := by
  exact star_branch_impossible_of_residualLemma2 hH hHcard hCenterDegree
    hAvoidLarge hDualCard hDualRows hDualDegree residualLemma2

end AiMathLab.P0054.G413
