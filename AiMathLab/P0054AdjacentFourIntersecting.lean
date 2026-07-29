import AiMathLab.P0054AdjacentFour

/-!
# Four pairwise-intersecting rows

The blockers meeting a smallest row `E` in exactly one point are supplied by
`AdjacentFour.localImage`.  This file adds the blockers contained in `E`,
obtained from the four traces on `E`.  The two classes are disjoint, and the
small omission cases give the sharp lower bound ten.
-/

namespace AiMathLab.P0054.AdjacentFourIntersecting

open AiMathLab.P0054.G413
open AiMathLab.P0054
open AiMathLab.P0054.AdjacentLower
open AiMathLab.P0054.AdjacentFour

noncomputable def fourTrace {alpha : Type*} [DecidableEq alpha]
    (E A B C : G413.Row alpha) : G413.Hypergraph alpha :=
  {E, E ∩ A, E ∩ B, E ∩ C}

theorem fourTrace_rows_subset_base {alpha : Type*} [DecidableEq alpha]
    (E A B C : G413.Row alpha) :
    ∀ R ∈ fourTrace E A B C, R ⊆ E := by
  classical
  intro R hR
  simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hR
  rcases hR with rfl | rfl | rfl | rfl
  · exact Finset.Subset.rfl
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left

theorem fourTrace_blocker_subset_base {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E A B C T : G413.Row alpha}
    (hT : T ∈ blocker (fourTrace E A B C)) : T ⊆ E := by
  intro x hxT
  by_contra hxE
  have hInactive : ∀ R ∈ fourTrace E A B C, x ∉ R := by
    intro R hR hxR
    exact hxE (fourTrace_rows_subset_base E A B C R hR hxR)
  exact (blocker_rows_avoid_inactive hInactive T hT) hxT

theorem fourTrace_blocker_subset_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C}) :
    blocker (fourTrace E A B C) ⊆ blocker H := by
  classical
  intro T hT
  have hTMin := mem_blocker.mp hT
  have hTSubsetE : T ⊆ E := fourTrace_blocker_subset_base hT
  apply mem_blocker.mpr
  refine ⟨?_, ?_⟩
  · intro R hRH
    have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
      simpa [hH] using hRH
    rcases hCases with hRE | hRA | hRB | hRC
    · subst R
      exact hTMin.prop E (by simp [fourTrace])
    · subst R
      obtain ⟨x, hxT, hxEA⟩ := hTMin.prop (E ∩ A) (by simp [fourTrace])
      exact ⟨x, hxT, (Finset.mem_inter.mp hxEA).2⟩
    · subst R
      obtain ⟨x, hxT, hxEB⟩ := hTMin.prop (E ∩ B) (by simp [fourTrace])
      exact ⟨x, hxT, (Finset.mem_inter.mp hxEB).2⟩
    · subst R
      obtain ⟨x, hxT, hxEC⟩ := hTMin.prop (E ∩ C) (by simp [fourTrace])
      exact ⟨x, hxT, (Finset.mem_inter.mp hxEC).2⟩
  · intro S hSTransversal hST
    apply hTMin.le_of_le ?_ hST
    intro R hRTrace
    simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hRTrace
    rcases hRTrace with hRE | hRA | hRB | hRC
    · subst R
      exact hSTransversal E (by simp [hH])
    · subst R
      obtain ⟨x, hxS, hxA⟩ := hSTransversal A (by simp [hH])
      have hxE : x ∈ E := hTSubsetE (hST hxS)
      exact ⟨x, hxS, Finset.mem_inter.mpr ⟨hxE, hxA⟩⟩
    · subst R
      obtain ⟨x, hxS, hxB⟩ := hSTransversal B (by simp [hH])
      have hxE : x ∈ E := hTSubsetE (hST hxS)
      exact ⟨x, hxS, Finset.mem_inter.mpr ⟨hxE, hxB⟩⟩
    · subst R
      obtain ⟨x, hxS, hxC⟩ := hSTransversal C (by simp [hH])
      have hxE : x ∈ E := hTSubsetE (hST hxS)
      exact ⟨x, hxS, Finset.mem_inter.mpr ⟨hxE, hxC⟩⟩

theorem fourTrace_blocker_rows_cardAtLeast_two {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    RowsCardAtLeast (blocker (fourTrace E A B C)) 2 := by
  intro T hT
  exact hBRows T (fourTrace_blocker_subset_blocker hH hT)

theorem fourTrace_rows_nonempty {alpha : Type*} [DecidableEq alpha]
    {E A B C : G413.Row alpha}
    (hE : E.Nonempty)
    (hEA : (E ∩ A).Nonempty)
    (hEB : (E ∩ B).Nonempty)
    (hEC : (E ∩ C).Nonempty) :
    RowsNonempty (fourTrace E A B C) := by
  intro R hR
  simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hR
  rcases hR with rfl | rfl | rfl | rfl
  · exact hE
  · exact hEA
  · exact hEB
  · exact hEC

theorem fourTrace_blocker_card_pos {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E A B C : G413.Row alpha}
    (hE : E.Nonempty)
    (hEA : (E ∩ A).Nonempty)
    (hEB : (E ∩ B).Nonempty)
    (hEC : (E ∩ C).Nonempty) :
    0 < (blocker (fourTrace E A B C)).card := by
  exact Finset.card_pos.mpr
    (blocker_nonempty (fourTrace_rows_nonempty hE hEA hEB hEC))

theorem localChoices_add_traceBlocker_le_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hTraceRows : RowsCardAtLeast (blocker (fourTrace E A B C)) 2) :
    (localChoices E A B C).card +
        (blocker (fourTrace E A B C)).card ≤ (blocker H).card := by
  classical
  have hDisjoint : Disjoint (localImage E A B C)
      (blocker (fourTrace E A B C)) := by
    apply Finset.disjoint_left.mpr
    intro T hTLocal hTTrace
    obtain ⟨q, hq, hqT⟩ := Finset.mem_image.mp hTLocal
    have hInter := localLift_inter_base hq
    rw [hqT] at hInter
    have hOne : (T ∩ E).card = 1 := by
      rw [hInter]
      simp
    have hTSubsetE := fourTrace_blocker_subset_base hTTrace
    have hInterEq : T ∩ E = T := Finset.inter_eq_left.mpr hTSubsetE
    rw [hInterEq] at hOne
    have hTwo := hTraceRows T hTTrace
    omega
  have hUnionSubset : localImage E A B C ∪ blocker (fourTrace E A B C) ⊆
      blocker H := Finset.union_subset (localImage_subset_blocker hH)
        (fourTrace_blocker_subset_blocker hH)
  calc
    (localChoices E A B C).card + (blocker (fourTrace E A B C)).card =
        (localImage E A B C).card + (blocker (fourTrace E A B C)).card := by
          rw [localImage_card]
    _ = (localImage E A B C ∪ blocker (fourTrace E A B C)).card :=
      (Finset.card_union_of_disjoint hDisjoint).symm
    _ ≤ (blocker H).card := Finset.card_le_card hUnionSubset

theorem trace_inter_proper_of_clutter {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A : G413.Row alpha}
    (hClutter : IsClutter H) (hEH : E ∈ H) (hAH : A ∈ H)
    (hEA : E ≠ A) : E ∩ A ≠ E := by
  intro hEq
  have hSubset : E ⊆ A := Finset.inter_eq_left.mp hEq
  exact hEA (hClutter hEH hAH hSubset)

theorem fourTrace_minimize_subset_proper {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H) (hH : H = {E, A, B, C})
    (hEA : E ≠ A) :
    minimize (fourTrace E A B C) ⊆ {E ∩ A, E ∩ B, E ∩ C} := by
  classical
  have hEH : E ∈ H := by simp [hH]
  have hAH : A ∈ H := by simp [hH]
  have hProper : E ∩ A ≠ E :=
    trace_inter_proper_of_clutter hClutter hEH hAH hEA
  intro R hR
  have hSource := minimize_subset (fourTrace E A B C) hR
  simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hSource
  rcases hSource with hRE | hRA | hRB | hRC
  · subst R
    have hReverse : E ⊆ E ∩ A :=
      (mem_minimize.mp hR).2 (E ∩ A) (by simp [fourTrace])
        Finset.inter_subset_left
    have hEq : E ∩ A = E :=
      Finset.Subset.antisymm Finset.inter_subset_left hReverse
    exact (hProper hEq).elim
  · subst R
    simp
  · subst R
    simp
  · subst R
    simp

theorem fourTrace_minimize_card_le_three {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H) (hH : H = {E, A, B, C})
    (hEA : E ≠ A) :
    (minimize (fourTrace E A B C)).card ≤ 3 := by
  exact (Finset.card_le_card
    (fourTrace_minimize_subset_proper hClutter hH hEA)).trans
      Finset.card_le_three

theorem fourTrace_minimize_nonempty {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (E A B C : G413.Row alpha) :
    (minimize (fourTrace E A B C)).Nonempty := by
  obtain ⟨M, hM, -⟩ := exists_minimize_subset
    (show E ∩ A ∈ fourTrace E A B C by simp [fourTrace])
  exact ⟨M, hM⟩

theorem fourTrace_minimize_rows_cardAtLeast_two {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H) (hH : H = {E, A, B, C})
    (hEA : E ≠ A) (hECard : E.card = 4)
    (hOA : (E \ A).card ≤ 2)
    (hOB : (E \ B).card ≤ 2)
    (hOC : (E \ C).card ≤ 2) :
    RowsCardAtLeast (minimize (fourTrace E A B C)) 2 := by
  have hACard : 2 ≤ (E ∩ A).card := by
    have hPart := Finset.card_sdiff_add_card_inter E A
    omega
  have hBCard : 2 ≤ (E ∩ B).card := by
    have hPart := Finset.card_sdiff_add_card_inter E B
    omega
  have hCCard : 2 ≤ (E ∩ C).card := by
    have hPart := Finset.card_sdiff_add_card_inter E C
    omega
  intro R hR
  have hSource := fourTrace_minimize_subset_proper hClutter hH hEA hR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hSource
  rcases hSource with rfl | rfl | rfl
  · exact hACard
  · exact hBCard
  · exact hCCard

theorem fourTrace_blocker_card_ge_three_of_omissions_le_two
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H) (hH : H = {E, A, B, C})
    (hEA : E ≠ A) (hECard : E.card = 4)
    (hOA : (E \ A).card ≤ 2)
    (hOB : (E \ B).card ≤ 2)
    (hOC : (E \ C).card ≤ 2)
    (hTraceRows : RowsCardAtLeast (blocker (fourTrace E A B C)) 2) :
    3 ≤ (blocker (fourTrace E A B C)).card := by
  classical
  let T := fourTrace E A B C
  let M := minimize T
  have hBlockerEq : blocker M = blocker T := by
    simpa [M] using blocker_minimize T
  have hMClutter : IsClutter M := by
    simpa [M] using minimize_isClutter T
  have hMNonempty : M.Nonempty := by
    simpa [M, T] using fourTrace_minimize_nonempty E A B C
  have hMPositive : 0 < M.card := Finset.card_pos.mpr hMNonempty
  have hMCardUpper : M.card ≤ 3 := by
    simpa [M, T] using fourTrace_minimize_card_le_three hClutter hH hEA
  have hMRows : RowsCardAtLeast M 2 := by
    simpa [M, T] using fourTrace_minimize_rows_cardAtLeast_two
      hClutter hH hEA hECard hOA hOB hOC
  have hBMRows : RowsCardAtLeast (blocker M) 2 := by
    intro Q hQ
    apply hTraceRows Q
    change Q ∈ blocker T
    rw [← hBlockerEq]
    exact hQ
  by_contra hNot
  have hBUpper : (blocker M).card ≤ 2 := by
    rw [hBlockerEq]
    simpa [T] using (show (blocker (fourTrace E A B C)).card ≤ 2 by omega)
  have hMCases : M.card = 1 ∨ M.card = 2 ∨ M.card = 3 := by omega
  rcases hMCases with hMCard | hMCard | hMCard
  · obtain ⟨R, hM⟩ := Finset.card_eq_one.mp hMCard
    have hRM : R ∈ M := by simp [hM]
    have hRPositive : 0 < R.card := by have := hMRows R hRM; omega
    obtain ⟨x, hxR⟩ := Finset.card_pos.mp hRPositive
    have hSingleton : ({x} : G413.Row alpha) ∈ blocker M := by
      rw [hM, blocker_singletonFamily]
      exact mem_singletonRows.mpr ⟨x, hxR, rfl⟩
    have hLarge := hBMRows {x} hSingleton
    simp at hLarge
  · obtain ⟨R, S, hRS, hM⟩ := Finset.card_eq_two.mp hMCard
    have hRCard : 2 ≤ R.card := hMRows R (by simp [hM])
    have hSCard : 2 ≤ S.card := hMRows S (by simp [hM])
    have hProduct : R.card * S.card ≤ (blocker M).card := by
      rw [hM]
      exact twoRow_blocker_card_ge_product (by simpa [hM] using hBMRows)
    have hProductLower : 4 ≤ R.card * S.card := by
      calc
        4 = 2 * 2 := rfl
        _ ≤ R.card * S.card := Nat.mul_le_mul hRCard hSCard
    omega
  · have hThree := threeRow_blocker_card_ge_three
      hMClutter hMCard hMRows hBMRows
    omega

theorem second_omission_card_ge_three_of_trace_blocker_card_eq_one
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H) (hH : H = {E, A, B, C})
    (hEA : E ≠ A) (hECard : E.card = 4)
    (hOrderAB : (E \ A).card ≤ (E \ B).card)
    (hOrderBC : (E \ B).card ≤ (E \ C).card)
    (hTraceRows : RowsCardAtLeast (blocker (fourTrace E A B C)) 2)
    (hTraceCard : (blocker (fourTrace E A B C)).card = 1) :
    3 ≤ (E \ B).card := by
  classical
  let T := fourTrace E A B C
  let M := minimize T
  have hBlockerEq : blocker M = blocker T := by
    simpa [M] using blocker_minimize T
  have hBMRows : RowsCardAtLeast (blocker M) 2 := by
    intro Q hQ
    apply hTraceRows Q
    change Q ∈ blocker T
    rw [← hBlockerEq]
    exact hQ
  have hBMCard : (blocker M).card = 1 := by
    rw [hBlockerEq]
    simpa [T] using hTraceCard
  obtain ⟨Q, hBQ⟩ := Finset.card_eq_one.mp hBMCard
  have hQB : Q ∈ blocker M := by simp [hBQ]
  have hQCard : 2 ≤ Q.card := hBMRows Q hQB
  obtain ⟨q, hqQ, r, hrQ, hqr⟩ := Finset.one_lt_card.mp hQCard
  have hMForm : M = singletonRows Q :=
    family_eq_singletonRows_of_blocker_eq_singleton
      (by simpa [M] using minimize_isClutter T) hBQ
  have singleton_source (z : alpha) (hzQ : z ∈ Q) :
      ((E ∩ A).card = 1 ∧ ({z} : G413.Row alpha) = E ∩ A) ∨
      ((E ∩ B).card = 1 ∧ ({z} : G413.Row alpha) = E ∩ B) ∨
      ((E ∩ C).card = 1 ∧ ({z} : G413.Row alpha) = E ∩ C) := by
    have hzM : ({z} : G413.Row alpha) ∈ M := by
      rw [hMForm]
      exact mem_singletonRows.mpr ⟨z, hzQ, rfl⟩
    change ({z} : G413.Row alpha) ∈ minimize T at hzM
    have hSource := minimize_subset T hzM
    simp only [T, fourTrace, Finset.mem_insert, Finset.mem_singleton] at hSource
    rcases hSource with hE | hA | hB | hC
    · have hCards : 1 = E.card := by
        simpa only [Finset.card_singleton] using congrArg Finset.card hE
      omega
    · exact Or.inl ⟨by rw [← hA]; simp, hA⟩
    · exact Or.inr (Or.inl ⟨by rw [← hB]; simp, hB⟩)
    · exact Or.inr (Or.inr ⟨by rw [← hC]; simp, hC⟩)
  have omission_three (D : G413.Row alpha) (hInter : (E ∩ D).card = 1) :
      (E \ D).card = 3 := by
    have hPart := Finset.card_sdiff_add_card_inter E D
    omega
  rcases singleton_source q hqQ with hqA | hqB | hqC <;>
    rcases singleton_source r hrQ with hrA | hrB | hrC
  · exact (hqr (Finset.singleton_inj.mp (hqA.2.trans hrA.2.symm))).elim
  · have := omission_three B hrB.1
    omega
  · have := omission_three A hqA.1
    omega
  · have := omission_three B hqB.1
    omega
  · exact (hqr (Finset.singleton_inj.mp (hqB.2.trans hrB.2.symm))).elim
  · have := omission_three B hqB.1
    omega
  · have := omission_three A hrA.1
    omega
  · have := omission_three B hrB.1
    omega
  · exact (hqr (Finset.singleton_inj.mp (hqC.2.trans hrC.2.symm))).elim

theorem fourTrace_blocker_card_ge_four_of_six_case
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hO1Card : (E \ A).card = 1)
    (hO2Card : (E \ B).card = 1)
    (hO3Card : (E \ C).card = 2)
    (hX2Card : ((E \ B) \ (E \ A)).card = 1)
    (hX3Card : (E \ ((E \ A) ∪ (E \ B))).card = 2) :
    4 ≤ (blocker (fourTrace E A B C)).card := by
  classical
  let O1 := E \ A
  let O2 := E \ B
  let O3 := E \ C
  let X2 := O2 \ O1
  let X3 := E \ (O1 ∪ O2)
  have hTraceRows : RowsCardAtLeast (blocker (fourTrace E A B C)) 2 :=
    fourTrace_blocker_rows_cardAtLeast_two hH hBRows
  have hX3SubsetO3 : X3 ⊆ O3 := by
    exact remaining_base_subset_third_omission hH hBRows
  have hX2EqO2 : X2 = O2 :=
    Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by
      have hLeft : X2.card = 1 := by simpa [X2] using hX2Card
      have hRight : O2.card = 1 := by simpa [O2] using hO2Card
      omega)
  have hX3EqO3 : X3 = O3 :=
    Finset.eq_of_subset_of_card_le hX3SubsetO3 (by
      have hLeft : X3.card = 2 := by simpa [X3] using hX3Card
      have hRight : O3.card = 2 := by simpa [O3] using hO3Card
      omega)
  obtain ⟨p, hpO1⟩ := Finset.card_pos.mp (by
    change 0 < (E \ A).card
    omega)
  obtain ⟨q, hqX2⟩ := Finset.card_pos.mp (by
    change 0 < ((E \ B) \ (E \ A)).card
    omega)
  have hpE : p ∈ E := (Finset.mem_sdiff.mp hpO1).1
  have hqO2 : q ∈ O2 := (Finset.mem_sdiff.mp hqX2).1
  have hqE : q ∈ E := (Finset.mem_sdiff.mp hqO2).1
  have hqNotO1 : q ∉ O1 := (Finset.mem_sdiff.mp hqX2).2
  have hpNotX2 : p ∉ X2 := fun hpX2 ↦ (Finset.mem_sdiff.mp hpX2).2 hpO1
  have hpNotO2 : p ∉ O2 := by rw [← hX2EqO2]; exact hpNotX2
  have hpq : p ≠ q := fun hpq ↦ hqNotO1 (hpq ▸ hpO1)
  have hPCard : ({p, q} : G413.Row alpha).card = 2 := by simp [hpq]
  have hPX3 : Disjoint ({p, q} : G413.Row alpha) X3 := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxX3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
    rcases hxP with rfl | rfl
    · exact (Finset.mem_sdiff.mp hxX3).2 (Finset.mem_union_left _ hpO1)
    · exact (Finset.mem_sdiff.mp hxX3).2 (Finset.mem_union_right _ hqO2)
  have hqA : q ∈ A := by
    by_contra hqA
    exact hqNotO1 (Finset.mem_sdiff.mpr ⟨hqE, hqA⟩)
  have hpB : p ∈ B := by
    by_contra hpB
    exact hpNotO2 (Finset.mem_sdiff.mpr ⟨hpE, hpB⟩)
  have hpC : p ∈ C := by
    by_contra hpC
    have hpO3 : p ∈ O3 := Finset.mem_sdiff.mpr ⟨hpE, hpC⟩
    rw [← hX3EqO3] at hpO3
    exact Finset.disjoint_left.mp hPX3 (by simp) hpO3
  have hqC : q ∈ C := by
    by_contra hqC
    have hqO3 : q ∈ O3 := Finset.mem_sdiff.mpr ⟨hqE, hqC⟩
    rw [← hX3EqO3] at hqO3
    exact Finset.disjoint_left.mp hPX3 (by simp) hqO3
  have hCrossSubset : crossPairRows ({p, q} : G413.Row alpha) X3 ⊆
      blocker (fourTrace E A B C) := by
    intro P hP
    obtain ⟨a, haPQ, b, hbX3, rfl⟩ := mem_crossPairRows.mp hP
    have hbE : b ∈ E := (Finset.mem_sdiff.mp hbX3).1
    have hbNotUnion := (Finset.mem_sdiff.mp hbX3).2
    have hbA : b ∈ A := by
      by_contra hbA
      exact hbNotUnion (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hbE, hbA⟩))
    have hbB : b ∈ B := by
      by_contra hbB
      exact hbNotUnion (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hbE, hbB⟩))
    have hTransversal : IsTransversal (fourTrace E A B C) {a, b} := by
      intro R hR
      simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨b, by simp, hbE⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at haPQ
        rcases haPQ with hap | haq
        · subst a
          exact ⟨b, by simp, Finset.mem_inter.mpr ⟨hbE, hbA⟩⟩
        · subst a
          exact ⟨q, by simp, Finset.mem_inter.mpr ⟨hqE, hqA⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at haPQ
        rcases haPQ with hap | haq
        · subst a
          exact ⟨p, by simp, Finset.mem_inter.mpr ⟨hpE, hpB⟩⟩
        · subst a
          exact ⟨b, by simp, Finset.mem_inter.mpr ⟨hbE, hbB⟩⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at haPQ
        rcases haPQ with hap | haq
        · subst a
          exact ⟨p, by simp, Finset.mem_inter.mpr ⟨hpE, hpC⟩⟩
        · subst a
          exact ⟨q, by simp, Finset.mem_inter.mpr ⟨hqE, hqC⟩⟩
    exact mem_blocker_of_transversal_card_le hTraceRows hTransversal Finset.card_le_two
  have hPairTransversal : IsTransversal (fourTrace E A B C) {p, q} := by
    intro R hR
    simp only [fourTrace, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact ⟨p, by simp, hpE⟩
    · exact ⟨q, by simp, Finset.mem_inter.mpr ⟨hqE, hqA⟩⟩
    · exact ⟨p, by simp, Finset.mem_inter.mpr ⟨hpE, hpB⟩⟩
    · exact ⟨p, by simp, Finset.mem_inter.mpr ⟨hpE, hpC⟩⟩
  have hPairBlocker : ({p, q} : G413.Row alpha) ∈
      blocker (fourTrace E A B C) :=
    mem_blocker_of_transversal_card_le hTraceRows hPairTransversal (by omega)
  have hPairNotCross : ({p, q} : G413.Row alpha) ∉
      crossPairRows ({p, q} : G413.Row alpha) X3 := by
    intro hPair
    obtain ⟨a, haPair, b, hbX3, hEq⟩ := mem_crossPairRows.mp hPair
    have hbPair : b ∈ ({p, q} : G413.Row alpha) := by
      rw [← hEq]
      simp
    exact Finset.disjoint_left.mp hPX3 hbPair hbX3
  have hFiveSubset : insert ({p, q} : G413.Row alpha)
      (crossPairRows ({p, q} : G413.Row alpha) X3) ⊆
      blocker (fourTrace E A B C) := by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hPairBlocker
    · exact hCrossSubset hP
  have hCrossLower : 4 ≤
      (crossPairRows ({p, q} : G413.Row alpha) X3).card := by
    have hX3CardLocal : X3.card = 2 := by simpa [X3] using hX3Card
    calc
      4 = 2 * 2 := rfl
      _ = ({p, q} : G413.Row alpha).card * X3.card := by
        rw [hPCard, hX3CardLocal]
      _ ≤ (crossPairRows ({p, q} : G413.Row alpha) X3).card :=
        card_mul_le_crossPairRows_card_of_disjoint hPX3
  have hCard := Finset.card_le_card hFiveSubset
  rw [Finset.card_insert_of_notMem hPairNotCross] at hCard
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Only the three partition sizes are enumerated; the theorem is the
-- three-variable square bound at the threshold needed below.
theorem three_part_square_threshold_finite :
    ∀ a t u : Fin 9,
      5 ≤ a.val + t.val + u.val →
      9 ≤ a.val * a.val + t.val * t.val + u.val * u.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- These 5^5 bounded tuples isolate the three sharp four-point cases.
theorem four_omission_low_cases_finite :
    ∀ a b c t u : Fin 5,
      1 ≤ a.val → a.val ≤ b.val → b.val ≤ c.val → c.val ≤ 3 →
      4 = a.val + t.val + u.val → t.val ≤ b.val → u.val ≤ c.val →
      let w := a.val * a.val + t.val * b.val + u.val * c.val
      6 ≤ w ∧
        (w ≤ 6 →
          a.val = 1 ∧ b.val = 1 ∧ c.val = 2 ∧ t.val = 1 ∧ u.val = 2) ∧
        (w ≤ 7 → c.val ≤ 2) ∧
        (b.val = 3 → 10 ≤ w) := by
  decide

theorem ordered_four_pairwise_intersecting_blocker_card_ge_ten
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H)
    (hH : H = {E, A, B, C})
    (hEA : E ≠ A) (hEB : E ≠ B) (hEC : E ≠ C)
    (hECard : 4 ≤ E.card)
    (hEMinA : E.card ≤ A.card)
    (hEMinB : E.card ≤ B.card)
    (hEMinC : E.card ≤ C.card)
    (hOrderAB : (E \ A).card ≤ (E \ B).card)
    (hOrderBC : (E \ B).card ≤ (E \ C).card)
    (hEAInter : (E ∩ A).Nonempty)
    (hEBInter : (E ∩ B).Nonempty)
    (hECInter : (E ∩ C).Nonempty)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    10 ≤ (blocker H).card := by
  classical
  let O1 := E \ A
  let O2 := E \ B
  let O3 := E \ C
  let X2 := O2 \ O1
  let X3 := E \ (O1 ∪ O2)
  let a := O1.card
  let b := O2.card
  let c := O3.card
  let t := X2.card
  let u := X3.card
  let w := a * a + t * b + u * c
  have hO1Subset : O1 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO2Subset : O2 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO3Subset : O3 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO1Positive : 0 < a := by
    apply Finset.card_pos.mpr
    by_contra hEmpty
    have hSubset : E ⊆ A := by
      intro x hxE
      by_contra hxA
      exact hEmpty ⟨x, Finset.mem_sdiff.mpr ⟨hxE, hxA⟩⟩
    exact hEA (hClutter (by simp [hH]) (by simp [hH]) hSubset)
  have hResidualA : a ≤ (A \ E).card := card_base_sdiff_le_residual hEMinA
  have hResidualB : b ≤ (B \ E).card := card_base_sdiff_le_residual hEMinB
  have hResidualC : c ≤ (C \ E).card := card_base_sdiff_le_residual hEMinC
  have hPointFirst (x : alpha) (hx : x ∈ O1) :
      a ≤ (blocker (localResidual E A B C x)).card := by
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH (hO1Subset hx) hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact hResidualA
    · exact hOrderAB.trans hResidualB
    · exact hOrderAB.trans (hOrderBC.trans hResidualC)
  have hPointSecond (x : alpha) (hx : x ∈ X2) :
      b ≤ (blocker (localResidual E A B C x)).card := by
    have hxO2 := (Finset.mem_sdiff.mp hx).1
    have hxE := hO2Subset hxO2
    have hxNotO1 := (Finset.mem_sdiff.mp hx).2
    have hxA : x ∈ A := by
      by_contra hxA
      exact hxNotO1 (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩)
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH hxE hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact (hxQ hxA).elim
    · exact hResidualB
    · exact hOrderBC.trans hResidualC
  have hPointThird (x : alpha) (hx : x ∈ X3) :
      c ≤ (blocker (localResidual E A B C x)).card := by
    have hxE := (Finset.mem_sdiff.mp hx).1
    have hxNotUnion := (Finset.mem_sdiff.mp hx).2
    have hxNotO1 : x ∉ O1 := fun hxO1 ↦ hxNotUnion (Finset.mem_union_left _ hxO1)
    have hxNotO2 : x ∉ O2 := fun hxO2 ↦ hxNotUnion (Finset.mem_union_right _ hxO2)
    have hxA : x ∈ A := by
      by_contra hxA
      exact hxNotO1 (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩)
    have hxB : x ∈ B := by
      by_contra hxB
      exact hxNotO2 (Finset.mem_sdiff.mpr ⟨hxE, hxB⟩)
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH hxE hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact (hxQ hxA).elim
    · exact (hxQ hxB).elim
    · exact hResidualC
  have hX3SubsetO3 : X3 ⊆ O3 := remaining_base_subset_third_omission hH hBRows
  have hFirstSum : a * a ≤ ∑ x ∈ O1,
      (blocker (localResidual E A B C x)).card := by
    calc
      a * a = ∑ _x ∈ O1, a := by simp [a]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointFirst x hx
  have hSecondSum : t * b ≤ ∑ x ∈ X2,
      (blocker (localResidual E A B C x)).card := by
    calc
      t * b = ∑ _x ∈ X2, b := by simp [t]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointSecond x hx
  have hThirdSum : u * c ≤ ∑ x ∈ X3,
      (blocker (localResidual E A B C x)).card := by
    calc
      u * c = ∑ _x ∈ X3, c := by simp [u]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointThird x hx
  have hDisjoint12 : Disjoint O1 X2 := Finset.disjoint_sdiff
  have hUnion12 : O1 ∪ X2 = O1 ∪ O2 := by ext x; simp [X2]
  have hDisjoint123 : Disjoint (O1 ∪ X2) X3 := by
    rw [hUnion12]
    exact Finset.disjoint_sdiff
  have hPartition : (O1 ∪ X2) ∪ X3 = E := by
    rw [hUnion12]
    exact Finset.union_sdiff_of_subset (Finset.union_subset hO1Subset hO2Subset)
  have hSumPartition :
      (∑ x ∈ E, (blocker (localResidual E A B C x)).card) =
        (∑ x ∈ O1, (blocker (localResidual E A B C x)).card) +
        (∑ x ∈ X2, (blocker (localResidual E A B C x)).card) +
        (∑ x ∈ X3, (blocker (localResidual E A B C x)).card) := by
    rw [← hPartition, Finset.sum_union hDisjoint123, Finset.sum_union hDisjoint12]
  have hGeneratedLower : w ≤ (localChoices E A B C).card := by
    change a * a + t * b + u * c ≤ _
    rw [localChoices, Finset.card_sigma, hSumPartition]
    omega
  have hNPartition : E.card = a + t + u := by
    have hCardPartition := congrArg Finset.card hPartition
    rw [Finset.card_union_of_disjoint hDisjoint123,
      Finset.card_union_of_disjoint hDisjoint12] at hCardPartition
    simpa [a, t, u, Nat.add_assoc] using hCardPartition.symm
  have htB : t ≤ b := Finset.card_le_card Finset.sdiff_subset
  have huC : u ≤ c := Finset.card_le_card hX3SubsetO3
  have hTraceRows : RowsCardAtLeast (blocker (fourTrace E A B C)) 2 :=
    fourTrace_blocker_rows_cardAtLeast_two hH hBRows
  have hCombined := localChoices_add_traceBlocker_le_blocker hH hTraceRows
  have hEPositive : E.Nonempty := Finset.card_pos.mp (by omega)
  have hTracePositive := fourTrace_blocker_card_pos
    hEPositive hEAInter hEBInter hECInter
  by_cases hWLarge : 9 ≤ w
  · omega
  have hWUpper : w ≤ 8 := by omega
  by_cases hEFour : E.card = 4
  · have ha4 : a ≤ 4 := by
      exact (Finset.card_le_card hO1Subset).trans_eq hEFour
    have hb4 : b ≤ 4 := by
      exact (Finset.card_le_card hO2Subset).trans_eq hEFour
    have hc4 : c ≤ 4 := by
      exact (Finset.card_le_card hO3Subset).trans_eq hEFour
    have ht4 : t ≤ 4 := by
      exact (Finset.card_le_card (Finset.sdiff_subset.trans hO2Subset)).trans_eq hEFour
    have hu4 : u ≤ 4 := by
      exact (Finset.card_le_card (show X3 ⊆ E from Finset.sdiff_subset)).trans_eq hEFour
    have hc3 : c ≤ 3 := by
      have hPart := Finset.card_sdiff_add_card_inter E C
      have hInterPositive : 0 < (E ∩ C).card := Finset.card_pos.mpr hECInter
      rw [hEFour] at hPart
      change (E \ C).card ≤ 3
      omega
    have hArithmetic := four_omission_low_cases_finite
      ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
      ⟨t, by omega⟩ ⟨u, by omega⟩
      hO1Positive hOrderAB hOrderBC hc3
      (by simpa [hEFour] using hNPartition)
      htB huC
    have hArithmetic' :
        6 ≤ w ∧
        (w ≤ 6 → a = 1 ∧ b = 1 ∧ c = 2 ∧ t = 1 ∧ u = 2) ∧
        (w ≤ 7 → c ≤ 2) ∧
        (b = 3 → 10 ≤ w) := by
      simpa [w] using hArithmetic
    rcases hArithmetic' with ⟨hSix, hSixCase, hSevenCase, hThreeCase⟩
    have hWCases : w = 6 ∨ w = 7 ∨ w = 8 := by omega
    rcases hWCases with hW | hW | hW
    · have hExact := hSixCase (by omega)
      rcases hExact with ⟨ha, hb, hc, ht, hu⟩
      have hTraceFour := fourTrace_blocker_card_ge_four_of_six_case
        hH hBRows
        (by simpa [O1, a] using ha)
        (by simpa [O2, b] using hb)
        (by simpa [O3, c] using hc)
        (by simpa [X2, t] using ht)
        (by simpa [X3, u] using hu)
      omega
    · have hc2 : c ≤ 2 := hSevenCase (by omega)
      have hTraceThree := fourTrace_blocker_card_ge_three_of_omissions_le_two
        hClutter hH hEA hEFour
        (by simpa [O1, a] using hOrderAB.trans (hOrderBC.trans hc2))
        (by simpa [O2, b] using hOrderBC.trans hc2)
        (by simpa [O3, c] using hc2)
        hTraceRows
      omega
    · have hTraceTwo : 2 ≤ (blocker (fourTrace E A B C)).card := by
        by_contra hNot
        have hTraceOne : (blocker (fourTrace E A B C)).card = 1 := by omega
        have hb3 := second_omission_card_ge_three_of_trace_blocker_card_eq_one
          hClutter hH hEA hEFour hOrderAB hOrderBC hTraceRows hTraceOne
        have hbEq : b = 3 := by
          have hbLe : b ≤ 3 := hOrderBC.trans hc3
          have hbLower : 3 ≤ b := by simpa [b, O2] using hb3
          exact Nat.le_antisymm hbLe hbLower
        have hTen := hThreeCase hbEq
        omega
      omega
  · have hEFive : 5 ≤ E.card := by omega
    have haW : a ≤ w := by
      have hSelf : a ≤ a * a := Nat.le_mul_of_pos_right a hO1Positive
      omega
    have hbPositive : 0 < b := hO1Positive.trans_le hOrderAB
    have hcPositive : 0 < c := hbPositive.trans_le hOrderBC
    have htW : t ≤ w := by
      have hSelf : t ≤ t * b := Nat.le_mul_of_pos_right t hbPositive
      omega
    have huW : u ≤ w := by
      have hSelf : u ≤ u * c := Nat.le_mul_of_pos_right u hcPositive
      omega
    have hSquare := three_part_square_threshold_finite
      ⟨a, by omega⟩ ⟨t, by omega⟩ ⟨u, by omega⟩
      (by simpa [hNPartition] using hEFive)
    have hSquare' : 9 ≤ a * a + t * t + u * u := by simpa using hSquare
    have httb : t * t ≤ t * b := Nat.mul_le_mul_left t htB
    have huuc : u * u ≤ u * c := Nat.mul_le_mul_left u huC
    change a * a + t * b + u * c ≤ 8 at hWUpper
    omega

theorem four_pairwise_intersecting_blocker_card_ge_ten
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hClutter : IsClutter H)
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 4)
    (hPairwise : ∀ R ∈ H, ∀ S ∈ H, R ≠ S → (R ∩ S).Nonempty)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    10 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, D, hABne, hACne, hADne, hBCne, hBDne, hCDne, hH⟩ :=
    Finset.card_eq_four.mp hHCard
  have ordered (E P Q R : G413.Row alpha)
      (hFamily : H = {E, P, Q, R})
      (hEP : E ≠ P) (hEQ : E ≠ Q) (hER : E ≠ R)
      (hECard : 4 ≤ E.card)
      (hEMinP : E.card ≤ P.card)
      (hEMinQ : E.card ≤ Q.card)
      (hEMinR : E.card ≤ R.card) :
      10 ≤ (blocker H).card := by
    have hEH : E ∈ H := by simp [hFamily]
    have hPH : P ∈ H := by simp [hFamily]
    have hQH : Q ∈ H := by simp [hFamily]
    have hRH : R ∈ H := by simp [hFamily]
    have hEPInter := hPairwise E hEH P hPH hEP
    have hEQInter := hPairwise E hEH Q hQH hEQ
    have hERInter := hPairwise E hEH R hRH hER
    have hSort :
        ((E \ P).card ≤ (E \ Q).card ∧ (E \ Q).card ≤ (E \ R).card) ∨
        ((E \ P).card ≤ (E \ R).card ∧ (E \ R).card ≤ (E \ Q).card) ∨
        ((E \ Q).card ≤ (E \ P).card ∧ (E \ P).card ≤ (E \ R).card) ∨
        ((E \ Q).card ≤ (E \ R).card ∧ (E \ R).card ≤ (E \ P).card) ∨
        ((E \ R).card ≤ (E \ P).card ∧ (E \ P).card ≤ (E \ Q).card) ∨
        ((E \ R).card ≤ (E \ Q).card ∧ (E \ Q).card ≤ (E \ P).card) := by
      omega
    rcases hSort with hPQR | hPRQ | hQPR | hQRP | hRPQ | hRQP
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        hClutter hFamily hEP hEQ hER hECard hEMinP hEMinQ hEMinR
        hPQR.1 hPQR.2 hEPInter hEQInter hERInter hBRows
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        (E := E) (A := P) (B := R) (C := Q) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEP hER hEQ hECard hEMinP hEMinR hEMinQ hPRQ.1 hPRQ.2
        hEPInter hERInter hEQInter hBRows
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        (E := E) (A := Q) (B := P) (C := R) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEQ hEP hER hECard hEMinQ hEMinP hEMinR hQPR.1 hQPR.2
        hEQInter hEPInter hERInter hBRows
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        (E := E) (A := Q) (B := R) (C := P) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEQ hER hEP hECard hEMinQ hEMinR hEMinP hQRP.1 hQRP.2
        hEQInter hERInter hEPInter hBRows
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        (E := E) (A := R) (B := P) (C := Q) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hER hEP hEQ hECard hEMinR hEMinP hEMinQ hRPQ.1 hRPQ.2
        hERInter hEPInter hEQInter hBRows
    · exact ordered_four_pairwise_intersecting_blocker_card_ge_ten
        (E := E) (A := R) (B := Q) (C := P) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hER hEQ hEP hECard hEMinR hEMinQ hEMinP hRQP.1 hRQP.2
        hERInter hEQInter hEPInter hBRows
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hACard := hHRows A hAH
  have hBCard := hHRows B hBH
  have hCCard := hHRows C hCH
  have hDCard := hHRows D hDH
  have hMinimum :
      (A.card ≤ B.card ∧ A.card ≤ C.card ∧ A.card ≤ D.card) ∨
      (B.card ≤ A.card ∧ B.card ≤ C.card ∧ B.card ≤ D.card) ∨
      (C.card ≤ A.card ∧ C.card ≤ B.card ∧ C.card ≤ D.card) ∨
      (D.card ≤ A.card ∧ D.card ≤ B.card ∧ D.card ≤ C.card) := by
    omega
  rcases hMinimum with hAmin | hBmin | hCmin | hDmin
  · exact ordered A B C D hH hABne hACne hADne hACard
      hAmin.1 hAmin.2.1 hAmin.2.2
  · exact ordered B A C D
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hABne.symm hBCne hBDne hBCard hBmin.1 hBmin.2.1 hBmin.2.2
  · exact ordered C A B D
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hACne.symm hBCne.symm hCDne hCCard hCmin.1 hCmin.2.1 hCmin.2.2
  · exact ordered D A B C
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hADne.symm hBDne.symm hCDne.symm hDCard hDmin.1 hDmin.2.1 hDmin.2.2

end AiMathLab.P0054.AdjacentFourIntersecting
