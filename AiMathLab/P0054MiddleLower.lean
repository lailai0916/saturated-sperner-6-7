import AiMathLab.P0054G417
import AiMathLab.P0054G418
import AiMathLab.P0054G416
import AiMathLab.P0054G419.BlockerDegree
import AiMathLab.P0054G419.ThreeRowSeven

/-!
# The exact middle local bound

This file proves the arbitrary-finite blocker inequality `m(3,3) ≥ 14` used
by the middle canonical layer.  The proof combines the already certified
five- and six-row low-degree bounds with short residual arguments.
-/

namespace AiMathLab.P0054.MiddleLower

open AiMathLab.P0054.G413
open AiMathLab.P0054

theorem degree_ge_two_of_two_rows {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} {R S : G413.Row α} {x : α}
    (hR : R ∈ H) (hS : S ∈ H) (hRS : R ≠ S)
    (hxR : x ∈ R) (hxS : x ∈ S) :
    2 ≤ degree H x := by
  have hSubset : ({R, S} : G413.Hypergraph α) ⊆
      H.filter fun T ↦ x ∈ T := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hR, hxR⟩
    · exact Finset.mem_filter.mpr ⟨hS, hxS⟩
  have hCard : ({R, S} : G413.Hypergraph α).card = 2 := by simp [hRS]
  simpa [degree, hCard] using Finset.card_le_card hSubset

theorem avoid_blocker_card_ge_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHNonempty : H.Nonempty)
    (hHRows : RowsCardAtLeast H 3) (x : α) :
    2 ≤ (avoidPoint (blocker H) x).card := by
  classical
  let R := residual H x
  obtain ⟨E, hEH⟩ := hHNonempty
  have hEDelete : E.erase x ∈ deletePoint H x :=
    Finset.mem_image.mpr ⟨E, hEH, rfl⟩
  obtain ⟨M, hM, -⟩ := exists_minimize_subset hEDelete
  have hRNonempty : R.Nonempty := ⟨M, by
    simpa only [R, G413.residual] using hM⟩
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hHRows x
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter H x
  have hLower := blocker_card_ge_two_of_rows_cardAtLeast_two
    hRClutter hRNonempty hRRows
  simpa [R, blocker_residual] using hLower

theorem fourRow_maxDegreeAtMost_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    MaxDegreeAtMost H 2 := by
  classical
  intro x
  by_contra hDegree
  have hDegreeLower : 3 ≤ degree H x := by omega
  have hAvoidUpper : (avoidPoint H x).card ≤ 1 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  interval_cases hAvoidCard : (avoidPoint H x).card
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hPositive : 0 < (avoidPoint H x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoid⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoid]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    have hEPositive : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoid] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_two.trans_lt (by omega))

theorem sixRow_maxDegreeAtMost_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    MaxDegreeAtMost H 4 := by
  classical
  intro x
  by_contra hDegree
  have hDegreeLower : 5 ≤ degree H x := by omega
  have hAvoidUpper : (avoidPoint H x).card ≤ 1 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  interval_cases hAvoidCard : (avoidPoint H x).card
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hPositive : 0 < (avoidPoint H x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoid⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoid]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    have hEPositive : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoid] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_two.trans_lt (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks all 4096 capped incidence vectors.
theorem nine_le_threePart_generated_count_finite :
    ∀ p q r x y z : Fin 4,
      3 ≤ p.val + x.val + y.val →
      3 ≤ q.val + x.val + z.val →
      3 ≤ r.val + y.val + z.val →
      2 ≤ p.val * q.val * r.val →
      9 ≤ x.val * y.val + x.val * z.val + y.val * z.val +
        x.val * r.val + y.val * q.val + z.val * p.val +
          p.val * q.val * r.val := by
  decide

theorem threeCap_pos {n : Nat} (hn : 0 < n) :
    0 < (G419.threeCap n).val := by
  change 0 < min n 3
  exact lt_min hn (by decide)

theorem two_le_threeCap_product {p q r : Nat} (h : 2 ≤ p * q * r) :
    2 ≤ (G419.threeCap p).val * (G419.threeCap q).val *
      (G419.threeCap r).val := by
  have hp : 0 < p := by
    by_contra hp
    have : p = 0 := Nat.eq_zero_of_not_pos hp
    simp [this] at h
  have hq : 0 < q := by
    by_contra hq
    have : q = 0 := Nat.eq_zero_of_not_pos hq
    simp [this] at h
  have hr : 0 < r := by
    by_contra hr
    have : r = 0 := Nat.eq_zero_of_not_pos hr
    simp [this] at h
  have hpCap := threeCap_pos hp
  have hqCap := threeCap_pos hq
  have hrCap := threeCap_pos hr
  have hLarge : 2 ≤ p ∨ 2 ≤ q ∨ 2 ≤ r := by
    by_contra hSmall
    push Not at hSmall
    have hpOne : p = 1 := by omega
    have hqOne : q = 1 := by omega
    have hrOne : r = 1 := by omega
    simp [hpOne, hqOne, hrOne] at h
  rcases hLarge with hpLarge | hqLarge | hrLarge
  · have hpCapLarge : 2 ≤ (G419.threeCap p).val := by
      change 2 ≤ min p 3
      exact le_min hpLarge (by decide)
    calc
      2 = 2 * 1 * 1 := rfl
      _ ≤ (G419.threeCap p).val * (G419.threeCap q).val *
          (G419.threeCap r).val :=
        Nat.mul_le_mul (Nat.mul_le_mul hpCapLarge hqCap) hrCap
  · have hqCapLarge : 2 ≤ (G419.threeCap q).val := by
      change 2 ≤ min q 3
      exact le_min hqLarge (by decide)
    calc
      2 = 1 * 2 * 1 := rfl
      _ ≤ (G419.threeCap p).val * (G419.threeCap q).val *
          (G419.threeCap r).val :=
        Nat.mul_le_mul (Nat.mul_le_mul hpCap hqCapLarge) hrCap
  · have hrCapLarge : 2 ≤ (G419.threeCap r).val := by
      change 2 ≤ min r 3
      exact le_min hrLarge (by decide)
    calc
      2 = 1 * 1 * 2 := rfl
      _ ≤ (G419.threeCap p).val * (G419.threeCap q).val *
          (G419.threeCap r).val :=
        Nat.mul_le_mul (Nat.mul_le_mul hpCap hqCap) hrCapLarge

theorem nine_le_threePart_generated_count
    (p q r x y z : Nat)
    (hA : 3 ≤ p + x + y)
    (hB : 3 ≤ q + x + z)
    (hC : 3 ≤ r + y + z)
    (hProduct : 2 ≤ p * q * r) :
    9 ≤ x * y + x * z + y * z + x * r + y * q + z * p + p * q * r := by
  have hFinite := nine_le_threePart_generated_count_finite
    (G419.threeCap p) (G419.threeCap q) (G419.threeCap r)
    (G419.threeCap x) (G419.threeCap y) (G419.threeCap z)
    (G419.threeCap_sum_three p x y hA)
    (G419.threeCap_sum_three q x z hB)
    (G419.threeCap_sum_three r y z hC)
    (two_le_threeCap_product hProduct)
  apply hFinite.trans
  gcongr <;> exact G419.threeCap_le _

theorem threeRow_seven_tripleRows_card_le_one {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α}
    (hKCard : K.card = 3)
    (hKRows : RowsCardAtLeast K 3)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hBKCard : (blocker K).card = 7) :
    (G413.rowsCardExactly (blocker K) 3).card ≤ 1 := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBKRows
  have hAK : A ∈ K := by simp [hK]
  have hBK : B ∈ K := by simp [hK]
  have hCK : C ∈ K := by simp [hK]
  have hACard := hKRows A hAK
  have hBCard := hKRows B hBK
  have hCCard := hKRows C hCK
  rw [G419.threePart_union_card hNoCommon] at hACard
  rw [G419.threePart_union_card_second hNoCommon] at hBCard
  rw [G419.threePart_union_card_third hNoCommon] at hCCard
  by_contra hTriple
  have hProduct :
      2 ≤ (G413.privatePart A B C).card *
        (G413.privatePart B A C).card *
        (G413.privatePart C A B).card := by
    have hExact := G413.threeRow_triple_blockers_card hK hAB hAC hBC
    omega
  have hNine := nine_le_threePart_generated_count
    (G413.privatePart A B C).card
    (G413.privatePart B A C).card
    (G413.privatePart C A B).card
    (G413.sharedPart A B C).card
    (G413.sharedPart A C B).card
    (G413.sharedPart B C A).card
    hACard hBCard hCCard hProduct
  have hGenerated := G419.threeGeneratedRows_card_le_blocker hK hAB hAC hBC
  omega

theorem threeRow_blocker_card_ge_twentySeven {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 3)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    27 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hH⟩ := Finset.card_eq_three.mp hHCard
  have hRowsTwo : RowsCardAtLeast H 2 := by
    intro E hE
    exact (by have := hHRows E hE; omega)
  obtain ⟨hABDisjoint, hACDisjoint, hBCDisjoint⟩ :=
    threeRows_pairwise_disjoint_of_blocker_rows_cardAtLeast_three
      hH hRowsTwo hBRows
  have hProduct := card_mul_mul_le_threeRow_blocker_card_of_pairwise_disjoint
    hH hABDisjoint hACDisjoint hBCDisjoint
  have hA : 3 ≤ A.card := hHRows A (by simp [hH])
  have hB : 3 ≤ B.card := hHRows B (by simp [hH])
  have hC : 3 ≤ C.card := hHRows C (by simp [hH])
  calc
    27 = 3 * 3 * 3 := rfl
    _ ≤ A.card * B.card * C.card := by gcongr
    _ ≤ (blocker H).card := hProduct

theorem fourRow_blocker_card_ge_ten {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    10 ≤ (blocker H).card := by
  classical
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hDegreeUpper := fourRow_maxDegreeAtMost_two hHCard hHRows hBRows
  by_cases hLow : MaxDegreeAtMost H 1
  · obtain ⟨E, hEH⟩ := hHNonempty
    have hEPositive : 0 < E.card := by have := hHRows E hEH; omega
    obtain ⟨x, hxE⟩ := Finset.card_pos.mp hEPositive
    have hDegreePositive : 0 < degree H x := by
      rw [degree]
      exact Finset.card_pos.mpr ⟨E, Finset.mem_filter.mpr ⟨hEH, hxE⟩⟩
    have hDegree : degree H x = 1 := by have := hLow x; omega
    let K := avoidPoint H x
    have hKCard : K.card = 3 := by
      have hPartition := card_avoidPoint_add_degree H x
      simpa [K, hHCard, hDegree] using hPartition
    obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
    have hAKAvoid : A ∈ K := by simp [hK]
    have hBKAvoid : B ∈ K := by simp [hK]
    have hCKAvoid : C ∈ K := by simp [hK]
    have hAK : A ∈ H := (mem_avoidPoint.mp (by simpa [K] using hAKAvoid)).1
    have hBK : B ∈ H := (mem_avoidPoint.mp (by simpa [K] using hBKAvoid)).1
    have hCK : C ∈ H := (mem_avoidPoint.mp (by simpa [K] using hCKAvoid)).1
    have hABDisjoint : Disjoint A B := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hTwo := degree_ge_two_of_two_rows hAK hBK hAB
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      have := hLow y
      omega
    have hACDisjoint : Disjoint A C := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hTwo := degree_ge_two_of_two_rows hAK hCK hAC
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      have := hLow y
      omega
    have hBCDisjoint : Disjoint B C := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hTwo := degree_ge_two_of_two_rows hBK hCK hBC
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      have := hLow y
      omega
    have hProduct := card_mul_mul_le_threeRow_blocker_card_of_pairwise_disjoint
      hK hABDisjoint hACDisjoint hBCDisjoint
    have hA : 3 ≤ A.card := hHRows A hAK
    have hB : 3 ≤ B.card := hHRows B hBK
    have hC : 3 ≤ C.card := hHRows C hCK
    have hKLower : 27 ≤ (blocker K).card := by
      calc
        27 = 3 * 3 * 3 := rfl
        _ ≤ A.card * B.card * C.card := by gcongr
        _ ≤ (blocker K).card := hProduct
    have hLift : (blocker K).card ≤ (blocker H).card := by
      simpa [K] using G419.blocker_avoidPoint_card_le_blocker H x
    omega
  · unfold MaxDegreeAtMost at hLow
    push Not at hLow
    obtain ⟨x, hx⟩ := hLow
    have hDegree : degree H x = 2 := by
      have := hDegreeUpper x
      omega
    have hAvoidCard : (avoidPoint H x).card = 2 := by
      have hPartition := card_avoidPoint_add_degree H x
      omega
    have hContaining : 9 ≤ degree (blocker H) x :=
      G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hAvoiding := avoid_blocker_card_ge_two hHNonempty hHRows x
    have hPartition := card_avoidPoint_add_degree (blocker H) x
    omega

theorem fiveRow_blocker_card_ge_nine {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    9 ≤ (blocker H).card := by
  have hDegreeUpper := fiveRow_maxDegreeAtMost_three hHCard hHRows hBRows
  by_cases hLow : MaxDegreeAtMost H 2
  · exact (AiMathLab.P0054.G416.fiveRow_lowDegree_blocker_card_ge_fifteen
      hHCard hHRows hLow).trans' (by omega)
  · unfold MaxDegreeAtMost at hLow
    push Not at hLow
    obtain ⟨x, hx⟩ := hLow
    have hDegree : degree H x = 3 := by
      have := hDegreeUpper x
      omega
    have hContaining := G415.degreeThree_blockers_containing_card_ge_nine
      hHCard hHRows hBRows hDegree
    exact hContaining.trans (Finset.card_filter_le _ _)

theorem sixRow_blocker_card_ge_eight {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    8 ≤ (blocker H).card := by
  classical
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hDegreeUpper := sixRow_maxDegreeAtMost_four hHCard hHRows hBRows
  by_cases hAtMostThree : MaxDegreeAtMost H 3
  · by_cases hLow : MaxDegreeAtMost H 2
    · exact (G417.sixRow_lowDegree_blocker_card_ge_fifteen
        hHCard hHRows hLow).trans' (by omega)
    · unfold MaxDegreeAtMost at hLow
      push Not at hLow
      obtain ⟨x, hx⟩ := hLow
      have hDegree : degree H x = 3 := by
        have := hAtMostThree x
        omega
      let K := avoidPoint H x
      have hKCard : K.card = 3 := by
        have hPartition := card_avoidPoint_add_degree H x
        simpa [K, hHCard, hDegree] using hPartition
      have hKClutter : IsClutter K := by
        simpa [K] using G419.avoidPoint_isClutter hHClutter x
      have hKRows : RowsCardAtLeast K 3 := by
        intro E hE
        exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hE)).1
      have hBKRows : RowsCardAtLeast (blocker K) 2 := by
        simpa [K] using G419.blocker_avoidPoint_rows_cardAtLeast_two hBRows x
      have hSeven : 7 ≤ (blocker K).card :=
        G419.threeRow_blocker_card_ge_seven hKClutter hKCard hKRows hBKRows
      have hLiftCard : (blocker K).card ≤ (blocker H).card := by
        simpa [K] using G419.blocker_avoidPoint_card_le_blocker H x
      by_cases hEight : 8 ≤ (blocker K).card
      · omega
      · have hBKCard : (blocker K).card = 7 := by omega
        have hTriple := threeRow_seven_tripleRows_card_le_one
          hKCard hKRows hBKRows hBKCard
        let lifts := (blocker K).image (G419.avoidBlockerLift H x)
        have hLiftsCard : lifts.card = 7 := by
          calc
            lifts.card = (blocker K).card :=
              Finset.card_image_iff.mpr (G419.avoidBlockerLift_injective H x)
            _ = 7 := hBKCard
        have hLiftsSubset : lifts ⊆ blocker H := by
          intro T hT
          obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
          exact G419.avoidBlockerLift_mem_blocker hU
        let A := avoidPoint (blocker H) x
        have hACard : 2 ≤ A.card := by
          simpa [A] using avoid_blocker_card_ge_two hHNonempty hHRows x
        have hNotSubset : ¬A ⊆ lifts := by
          intro hSubset
          have hExactSubset : A ⊆ G413.rowsCardExactly (blocker K) 3 := by
            intro E hEA
            have hELifts := hSubset hEA
            obtain ⟨T, hTK, hLift⟩ := Finset.mem_image.mp hELifts
            have hEAMem : E ∈ avoidPoint (blocker H) x := by
              simpa only [A] using hEA
            have hxE : x ∉ E := (mem_avoidPoint.mp hEAMem).2
            have hTE : T = E := by
              calc
                T = (G419.avoidBlockerLift H x T).erase x :=
                  (G419.avoidBlockerLift_erase H x hTK).symm
                _ = E.erase x := by rw [hLift]
                _ = E := Finset.erase_eq_of_notMem hxE
            subst T
            have hEBlocker : E ∈ blocker H := (mem_avoidPoint.mp hEAMem).1
            have hLower := hBRows E hEBlocker
            have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hTK)
            exact G413.mem_rowsCardExactly.mpr ⟨hTK, by omega⟩
          have hCardLe := Finset.card_le_card hExactSubset
          omega
        obtain ⟨E, hEA, hENot⟩ := Finset.not_subset.mp hNotSubset
        have hEAMem : E ∈ avoidPoint (blocker H) x := by
          simpa only [A] using hEA
        have hEBlocker : E ∈ blocker H := (mem_avoidPoint.mp hEAMem).1
        have hInsertSubset : insert E lifts ⊆ blocker H := by
          intro T hT
          simp only [Finset.mem_insert] at hT
          rcases hT with rfl | hT
          · exact hEBlocker
          · exact hLiftsSubset hT
        have hInsertCard : (insert E lifts).card = 8 := by
          rw [Finset.card_insert_of_notMem hENot, hLiftsCard]
        have := Finset.card_le_card hInsertSubset
        omega
  · unfold MaxDegreeAtMost at hAtMostThree
    push Not at hAtMostThree
    obtain ⟨x, hx⟩ := hAtMostThree
    have hDegree : degree H x = 4 := by
      have := hDegreeUpper x
      omega
    have hContaining := G418.degreeFour_blockers_containing_card_ge_nine
      hHCard hHRows hBRows hDegree
    have hCardDegree : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_filter_le _ _
    omega

theorem mutual_blocker_total_card_ge_fourteen {α : Type*}
    [Fintype α] [DecidableEq α]
    {S C : G413.Hypergraph α}
    (hSClutter : IsClutter S) (hCClutter : IsClutter C)
    (hSC : S = blocker C) (hCS : C = blocker S)
    (hSNonempty : S.Nonempty) (hCNonempty : C.Nonempty)
    (hSRows : RowsCardAtLeast S 3)
    (hCRows : RowsCardAtLeast C 3) :
    14 ≤ S.card + C.card := by
  have hSCardLower : 3 ≤ S.card := by
    obtain ⟨Q, hQC⟩ := hCNonempty
    have hQBlocker : Q ∈ blocker S := by simpa [← hCS] using hQC
    exact (hCRows Q hQC).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hQBlocker))
  have hCCardLower : 3 ≤ C.card := by
    obtain ⟨P, hPS⟩ := hSNonempty
    have hPBlocker : P ∈ blocker C := by simpa [← hSC] using hPS
    exact (hSRows P hPS).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hPBlocker))
  by_contra hTotal
  have hTotalUpper : S.card + C.card ≤ 13 := by omega
  by_cases hOrder : S.card ≤ C.card
  · have hSUpper : S.card ≤ 6 := by omega
    have hCases : S.card = 3 ∨ S.card = 4 ∨ S.card = 5 ∨ S.card = 6 := by omega
    have hBRows : RowsCardAtLeast (blocker S) 3 := by simpa [← hCS] using hCRows
    rcases hCases with hCard | hCard | hCard | hCard
    · have hLower := threeRow_blocker_card_ge_twentySeven hCard hSRows hBRows
      rw [← hCS] at hLower
      omega
    · have hLower := fourRow_blocker_card_ge_ten hCard hSRows hBRows
      rw [← hCS] at hLower
      omega
    · have hLower := fiveRow_blocker_card_ge_nine hCard hSRows hBRows
      rw [← hCS] at hLower
      omega
    · have hLower := sixRow_blocker_card_ge_eight hSClutter hCard hSRows hBRows
      rw [← hCS] at hLower
      omega
  · have hOrder' : C.card ≤ S.card := by omega
    have hCUpper : C.card ≤ 6 := by omega
    have hCases : C.card = 3 ∨ C.card = 4 ∨ C.card = 5 ∨ C.card = 6 := by omega
    have hBRows : RowsCardAtLeast (blocker C) 3 := by simpa [← hSC] using hSRows
    rcases hCases with hCard | hCard | hCard | hCard
    · have hLower := threeRow_blocker_card_ge_twentySeven hCard hCRows hBRows
      rw [← hSC] at hLower
      omega
    · have hLower := fourRow_blocker_card_ge_ten hCard hCRows hBRows
      rw [← hSC] at hLower
      omega
    · have hLower := fiveRow_blocker_card_ge_nine hCard hCRows hBRows
      rw [← hSC] at hLower
      omega
    · have hLower := sixRow_blocker_card_ge_eight hCClutter hCard hCRows hBRows
      rw [← hSC] at hLower
      omega

end AiMathLab.P0054.MiddleLower
