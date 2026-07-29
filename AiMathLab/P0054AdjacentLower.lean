import AiMathLab.P0054MiddleLower

/-!
# The exact adjacent local bound

This file proves the arbitrary-finite blocker inequality `m(2,4) ≥ 12`
used by the two adjacent canonical layers.  The first lemmas isolate the
small-cardinality branches of the product argument.
-/

namespace AiMathLab.P0054.AdjacentLower

open AiMathLab.P0054.G413
open AiMathLab.P0054

def fourCap (n : Nat) : Fin 5 :=
  ⟨min n 4, by omega⟩

theorem fourCap_le (n : Nat) : (fourCap n).val ≤ n := by
  exact min_le_left _ _

theorem fourCap_sum_four (a b c : Nat) (h : 4 ≤ a + b + c) :
    4 ≤ (fourCap a).val + (fourCap b).val + (fourCap c).val := by
  change 4 ≤ min a 4 + min b 4 + min c 4
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Kernel evaluation checks all 15625 capped incidence vectors.
theorem twelve_le_threePart_generated_count_finite :
    ∀ p q r x y z : Fin 5,
      4 ≤ p.val + x.val + y.val →
      4 ≤ q.val + x.val + z.val →
      4 ≤ r.val + y.val + z.val →
      12 ≤ x.val * y.val + x.val * z.val + y.val * z.val +
        x.val * r.val + y.val * q.val + z.val * p.val +
          p.val * q.val * r.val := by
  decide

theorem twelve_le_threePart_generated_count
    (p q r x y z : Nat)
    (hA : 4 ≤ p + x + y)
    (hB : 4 ≤ q + x + z)
    (hC : 4 ≤ r + y + z) :
    12 ≤ x * y + x * z + y * z + x * r + y * q + z * p + p * q * r := by
  have hFinite := twelve_le_threePart_generated_count_finite
    (fourCap p) (fourCap q) (fourCap r)
    (fourCap x) (fourCap y) (fourCap z)
    (fourCap_sum_four p x y hA)
    (fourCap_sum_four q x z hB)
    (fourCap_sum_four r y z hC)
  apply hFinite.trans
  gcongr <;> exact fourCap_le _

theorem blocker_card_ge_sixteen_of_card_eq_two {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHCard : H.card = 2)
    (hHRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    16 ≤ (blocker H).card := by
  obtain ⟨A, B, hAB, hH⟩ := Finset.card_eq_two.mp hHCard
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hProduct : A.card * B.card ≤ (blocker H).card := by
    rw [hH]
    exact twoRow_blocker_card_ge_product (by simpa [hH] using hBRows)
  calc
    16 = 4 * 4 := rfl
    _ ≤ A.card * B.card := Nat.mul_le_mul (hHRows A hAH) (hHRows B hBH)
    _ ≤ (blocker H).card := hProduct

theorem blocker_card_ge_twelve_of_card_eq_three {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHCard : H.card = 3)
    (hHRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    12 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hH⟩ := Finset.card_eq_three.mp hHCard
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hH hBRows
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hACard := hHRows A hAH
  have hBCard := hHRows B hBH
  have hCCard := hHRows C hCH
  rw [G419.threePart_union_card hNoCommon] at hACard
  rw [G419.threePart_union_card_second hNoCommon] at hBCard
  rw [G419.threePart_union_card_third hNoCommon] at hCCard
  have hTwelve := twelve_le_threePart_generated_count
    (privatePart A B C).card
    (privatePart B A C).card
    (privatePart C A B).card
    (sharedPart A B C).card
    (sharedPart A C B).card
    (sharedPart B C A).card
    hACard hBCard hCCard
  exact hTwelve.trans (G419.threeGeneratedRows_card_le_blocker hH hAB hAC hBC)

theorem fourRow_product_le_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {A B C D : G413.Row alpha}
    (hH : H = {A, B, C, D})
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    A.card * B.card * C.card * D.card ≤ (blocker H).card := by
  let K : G413.Hypergraph alpha := {B, C, D}
  have hHK : H = insert A K := by simp [hH, K]
  have hAK : ∀ E ∈ K, Disjoint A E := by
    intro E hE
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hAD
  have hThree : B.card * C.card * D.card ≤ (blocker K).card :=
    card_mul_mul_le_threeRow_blocker_card_of_pairwise_disjoint
      (by rfl) hBC hBD hCD
  have hLift := isolatedRow_product_le_blocker_card hHK hAK
  calc
    A.card * B.card * C.card * D.card = A.card * (B.card * C.card * D.card) := by
      simp [Nat.mul_assoc]
    _ ≤ A.card * (blocker K).card := Nat.mul_le_mul_left A.card hThree
    _ ≤ (blocker H).card := hLift

theorem first_two_disjoint_of_four_rows {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {A B C D : G413.Row alpha}
    (hH : H = {A, B, C, D})
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    Disjoint A B := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hCPositive : 0 < C.card := by
    have hCAtLeast := hHRows C hCH
    omega
  have hDPositive : 0 < D.card := by
    have hDAtLeast := hHRows D hDH
    omega
  obtain ⟨c, hcC⟩ := Finset.card_pos.mp hCPositive
  obtain ⟨d, hdD⟩ := Finset.card_pos.mp hDPositive
  have hTransversal : IsTransversal H {x, c, d} := by
    intro E hEH
    have hCases : E = A ∨ E = B ∨ E = C ∨ E = D := by
      simpa [hH] using hEH
    rcases hCases with hEA | hEB | hEC | hED
    · exact ⟨x, by simp, hEA ▸ (Finset.mem_inter.mp hx).1⟩
    · exact ⟨x, by simp, hEB ▸ (Finset.mem_inter.mp hx).2⟩
    · exact ⟨c, by simp, hEC ▸ hcC⟩
    · exact ⟨d, by simp, hED ▸ hdD⟩
  exact (false_of_small_transversal hBRows hTransversal
    (Finset.card_le_three.trans_lt (by omega))).elim

theorem blocker_card_ge_sixteen_of_card_eq_four {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    16 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, D, hABne, hACne, hADne, hBCne, hBDne, hCDne, hH⟩ :=
    Finset.card_eq_four.mp hHCard
  have hAB := first_two_disjoint_of_four_rows hH hHRows hBRows
  have hAC := first_two_disjoint_of_four_rows
    (A := A) (B := C) (C := B) (D := D)
    (by rw [hH]; ext E; simp [or_comm, or_left_comm]) hHRows hBRows
  have hAD := first_two_disjoint_of_four_rows
    (A := A) (B := D) (C := B) (D := C)
    (by rw [hH]; ext E; simp [or_comm, or_left_comm]) hHRows hBRows
  have hBC := first_two_disjoint_of_four_rows
    (A := B) (B := C) (C := A) (D := D)
    (by rw [hH]; ext E; simp [or_comm, or_left_comm]) hHRows hBRows
  have hBD := first_two_disjoint_of_four_rows
    (A := B) (B := D) (C := A) (D := C)
    (by rw [hH]; ext E; simp [or_comm, or_left_comm]) hHRows hBRows
  have hCD := first_two_disjoint_of_four_rows
    (A := C) (B := D) (C := A) (D := B)
    (by rw [hH]; ext E; simp [or_comm, or_left_comm]) hHRows hBRows
  have hProduct := fourRow_product_le_blocker hH hAB hAC hAD hBC hBD hCD
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  calc
    16 = 2 * 2 * 2 * 2 := rfl
    _ ≤ A.card * B.card * C.card * D.card :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (hHRows A hAH) (hHRows B hBH))
          (hHRows C hCH))
        (hHRows D hDH)
    _ ≤ (blocker H).card := hProduct

theorem mem_blocker_of_transversal_card_le {alpha : Type*}
    [Fintype alpha]
    {H : G413.Hypergraph alpha} {T : G413.Row alpha} {n : Nat}
    (hBRows : RowsCardAtLeast (blocker H) n)
    (hT : IsTransversal H T) (hTCard : T.card ≤ n) :
    T ∈ blocker H := by
  obtain ⟨M, hMT, hMMinimal⟩ := exists_minimalTransversal_subset hT
  have hMLower := hBRows M (mem_blocker.mpr hMMinimal)
  have hEq : M = T := Finset.eq_of_subset_of_card_le hMT (by omega)
  exact hEq ▸ mem_blocker.mpr hMMinimal

theorem fiveRows_intersecting_pair_blocker_card_ge_eight {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {A B C D E : G413.Row alpha}
    (hH : H = {A, B, C, D, E})
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4)
    (hAB : (A ∩ B).Nonempty) :
    8 ≤ (blocker H).card := by
  classical
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hEH : E ∈ H := by simp [hH]
  have hCPositive : 0 < C.card := by have := hHRows C hCH; omega
  have hDPositive : 0 < D.card := by have := hHRows D hDH; omega
  have hEPositive : 0 < E.card := by have := hHRows E hEH; omega
  have hCNonempty := Finset.card_pos.mp hCPositive
  have hDNonempty := Finset.card_pos.mp hDPositive
  have hENonempty := Finset.card_pos.mp hEPositive
  have hCD : Disjoint C D :=
    fiveRows_opposite_rows_disjoint hH hBRows hAB hENonempty
  have hCE : Disjoint C E :=
    fiveRows_opposite_rows_disjoint
      (A := A) (B := B) (C := C) (D := E) (E := D)
      (by rw [hH]; ext R; simp [or_comm]) hBRows hAB hDNonempty
  have hDE : Disjoint D E :=
    fiveRows_opposite_rows_disjoint
      (A := A) (B := B) (C := D) (D := E) (E := C)
      (by rw [hH]; ext R; simp [or_comm, or_left_comm]) hBRows hAB hCNonempty
  obtain ⟨z, hzAB⟩ := hAB
  have hzA := (Finset.mem_inter.mp hzAB).1
  have hzB := (Finset.mem_inter.mp hzAB).2
  have hzC : z ∉ C := by
    intro hzC
    obtain ⟨d, hdD⟩ := hDNonempty
    obtain ⟨e, heE⟩ := hENonempty
    have hSmall : IsTransversal H {z, d, e} := by
      intro R hRH
      have hCases : R = A ∨ R = B ∨ R = C ∨ R = D ∨ R = E := by
        simpa [hH] using hRH
      rcases hCases with hRA | hRB | hRC | hRD | hRE
      · exact ⟨z, by simp, hRA ▸ hzA⟩
      · exact ⟨z, by simp, hRB ▸ hzB⟩
      · exact ⟨z, by simp, hRC ▸ hzC⟩
      · exact ⟨d, by simp, hRD ▸ hdD⟩
      · exact ⟨e, by simp, hRE ▸ heE⟩
    exact false_of_small_transversal hBRows hSmall
      (Finset.card_le_three.trans_lt (by omega))
  have hzD : z ∉ D := by
    intro hzD
    obtain ⟨c, hcC⟩ := hCNonempty
    obtain ⟨e, heE⟩ := hENonempty
    have hSmall : IsTransversal H {z, c, e} := by
      intro R hRH
      have hCases : R = A ∨ R = B ∨ R = C ∨ R = D ∨ R = E := by
        simpa [hH] using hRH
      rcases hCases with hRA | hRB | hRC | hRD | hRE
      · exact ⟨z, by simp, hRA ▸ hzA⟩
      · exact ⟨z, by simp, hRB ▸ hzB⟩
      · exact ⟨c, by simp, hRC ▸ hcC⟩
      · exact ⟨z, by simp, hRD ▸ hzD⟩
      · exact ⟨e, by simp, hRE ▸ heE⟩
    exact false_of_small_transversal hBRows hSmall
      (Finset.card_le_three.trans_lt (by omega))
  have hzE : z ∉ E := by
    intro hzE
    obtain ⟨c, hcC⟩ := hCNonempty
    obtain ⟨d, hdD⟩ := hDNonempty
    have hSmall : IsTransversal H {z, c, d} := by
      intro R hRH
      have hCases : R = A ∨ R = B ∨ R = C ∨ R = D ∨ R = E := by
        simpa [hH] using hRH
      rcases hCases with hRA | hRB | hRC | hRD | hRE
      · exact ⟨z, by simp, hRA ▸ hzA⟩
      · exact ⟨z, by simp, hRB ▸ hzB⟩
      · exact ⟨c, by simp, hRC ▸ hcC⟩
      · exact ⟨d, by simp, hRD ▸ hdD⟩
      · exact ⟨z, by simp, hRE ▸ hzE⟩
    exact false_of_small_transversal hBRows hSmall
      (Finset.card_le_three.trans_lt (by omega))
  let triples := G413.tripleChoiceRows C D E
  let lift : G413.Row alpha → G413.Row alpha := fun T ↦ insert z T
  have hAvoidsZ : ∀ T ∈ triples, z ∉ T := by
    intro T hT hzT
    obtain ⟨c, hcC, d, hdD, e, heE, hRow⟩ :=
      G413.mem_tripleChoiceRows.mp hT
    rw [← hRow] at hzT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzT
    rcases hzT with rfl | rfl | rfl
    · exact hzC hcC
    · exact hzD hdD
    · exact hzE heE
  have hLiftInjective : Set.InjOn lift (↑triples : Set (G413.Row alpha)) := by
    intro T hT U hU hEq
    have hzT := hAvoidsZ T hT
    have hzU := hAvoidsZ U hU
    simpa [lift, hzT, hzU] using congrArg (Finset.erase · z) hEq
  have hImageSubset : triples.image lift ⊆ blocker H := by
    intro T hT
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨c, hcC, d, hdD, e, heE, hRow⟩ :=
      G413.mem_tripleChoiceRows.mp hR
    have hTransversal : IsTransversal H (lift R) := by
      intro Q hQH
      have hCases : Q = A ∨ Q = B ∨ Q = C ∨ Q = D ∨ Q = E := by
        simpa [hH] using hQH
      rcases hCases with hQA | hQB | hQC | hQD | hQE
      · exact ⟨z, by simp [lift], hQA ▸ hzA⟩
      · exact ⟨z, by simp [lift], hQB ▸ hzB⟩
      · exact ⟨c, by simp [lift, ← hRow], hQC ▸ hcC⟩
      · exact ⟨d, by simp [lift, ← hRow], hQD ▸ hdD⟩
      · exact ⟨e, by simp [lift, ← hRow], hQE ▸ heE⟩
    have hRCard : R.card ≤ 3 := by
      rw [← hRow]
      exact Finset.card_le_three
    exact mem_blocker_of_transversal_card_le hBRows hTransversal
      ((Finset.card_insert_le z R).trans (by omega))
  have hTripleCard : triples.card = C.card * D.card * E.card := by
    exact G413.tripleChoiceRows_card hCD hCE hDE
  calc
    8 = 2 * 2 * 2 := rfl
    _ ≤ C.card * D.card * E.card :=
      Nat.mul_le_mul (Nat.mul_le_mul (hHRows C hCH) (hHRows D hDH)) (hHRows E hEH)
    _ = triples.card := hTripleCard.symm
    _ = (triples.image lift).card := (Finset.card_image_iff.mpr hLiftInjective).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem fiveRow_pairwise_disjoint_product_le_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {A B C D E : G413.Row alpha}
    (hH : H = {A, B, C, D, E})
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hAE : Disjoint A E) (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hBE : Disjoint B E) (hCD : Disjoint C D) (hCE : Disjoint C E)
    (hDE : Disjoint D E) :
    A.card * B.card * C.card * D.card * E.card ≤ (blocker H).card := by
  let K : G413.Hypergraph alpha := {B, C, D, E}
  have hHK : H = insert A K := by simp [hH, K]
  have hAK : ∀ R ∈ K, Disjoint A R := by
    intro R hR
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hAD
    · exact hAE
  have hFour : B.card * C.card * D.card * E.card ≤ (blocker K).card :=
    fourRow_product_le_blocker (by rfl) hBC hBD hBE hCD hCE hDE
  have hLift := isolatedRow_product_le_blocker_card hHK hAK
  calc
    A.card * B.card * C.card * D.card * E.card =
        A.card * (B.card * C.card * D.card * E.card) := by simp [Nat.mul_assoc]
    _ ≤ A.card * (blocker K).card := Nat.mul_le_mul_left A.card hFour
    _ ≤ (blocker H).card := hLift

theorem blocker_card_ge_eight_of_card_eq_five {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHCard : H.card = 5)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    8 ≤ (blocker H).card := by
  classical
  by_cases hIntersect : ∃ A ∈ H, ∃ B ∈ H, A ≠ B ∧ (A ∩ B).Nonempty
  · obtain ⟨A, hAH, B, hBH, hABne, hAB⟩ := hIntersect
    let K := (H.erase A).erase B
    have hBErase : B ∈ H.erase A := Finset.mem_erase.mpr ⟨hABne.symm, hBH⟩
    have hEraseCard : (H.erase A).card = 4 := by
      rw [Finset.card_erase_of_mem hAH, hHCard]
    have hKCard : K.card = 3 := by
      dsimp [K]
      rw [Finset.card_erase_of_mem hBErase, hEraseCard]
    obtain ⟨C, D, E, -, -, -, hK⟩ := Finset.card_eq_three.mp hKCard
    have hCH : C ∈ H := by
      have hCK : C ∈ K := by simp [hK]
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hCK)
    have hDH : D ∈ H := by
      have hDK : D ∈ K := by simp [hK]
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hDK)
    have hEH : E ∈ H := by
      have hEK : E ∈ K := by simp [hK]
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hEK)
    have hForm : H = {A, B, C, D, E} := by
      ext R
      constructor
      · intro hRH
        by_cases hRA : R = A
        · simp [hRA]
        by_cases hRB : R = B
        · simp [hRB]
        have hRK : R ∈ K := by simp [K, hRH, hRA, hRB]
        have : R = C ∨ R = D ∨ R = E := by simpa [hK] using hRK
        rcases this with rfl | rfl | rfl <;> simp
      · intro hR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hR
        rcases hR with rfl | rfl | rfl | rfl | rfl
        · exact hAH
        · exact hBH
        · exact hCH
        · exact hDH
        · exact hEH
    exact fiveRows_intersecting_pair_blocker_card_ge_eight hForm hHRows hBRows hAB
  · obtain ⟨A, B, C, D, E, hForm,
      hABne, hACne, hADne, hAEne, hBCne, hBDne, hBEne, hCDne, hCEne, hDEne⟩ :=
      exists_five_distinct_rows_of_card_eq_five hHCard
    have hAH : A ∈ H := by simp [hForm]
    have hBH : B ∈ H := by simp [hForm]
    have hCH : C ∈ H := by simp [hForm]
    have hDH : D ∈ H := by simp [hForm]
    have hEH : E ∈ H := by simp [hForm]
    have pairDisjoint {X Y : G413.Row alpha}
        (hX : X ∈ H) (hY : Y ∈ H) (hXY : X ≠ Y) : Disjoint X Y :=
      disjoint_of_inter_not_nonempty
        (fun hMeet ↦ hIntersect ⟨X, hX, Y, hY, hXY, hMeet⟩)
    have hProduct := fiveRow_pairwise_disjoint_product_le_blocker hForm
      (pairDisjoint hAH hBH hABne)
      (pairDisjoint hAH hCH hACne)
      (pairDisjoint hAH hDH hADne)
      (pairDisjoint hAH hEH hAEne)
      (pairDisjoint hBH hCH hBCne)
      (pairDisjoint hBH hDH hBDne)
      (pairDisjoint hBH hEH hBEne)
      (pairDisjoint hCH hDH hCDne)
      (pairDisjoint hCH hEH hCEne)
      (pairDisjoint hDH hEH hDEne)
    calc
      8 ≤ 2 * 2 * 2 * 2 * 2 := by decide
      _ ≤ A.card * B.card * C.card * D.card * E.card :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul (hHRows A hAH) (hHRows B hBH))
              (hHRows C hCH))
            (hHRows D hDH))
          (hHRows E hEH)
      _ ≤ (blocker H).card := hProduct

end AiMathLab.P0054.AdjacentLower
