import AiMathLab.P0054G420.FiveRowPairExactFiniteConsequences
import AiMathLab.P0054G420.FiveRowPairExact

namespace AiMathLab.P0054.G420

open G413 G419

theorem avoidPairRows_add_common_le_pairRows
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hAvoid : avoidPoint K x = {P, Q}) :
    (pairRows (avoidPoint (blocker K) x)).card + (P ∩ Q).card ≤
      (pairRows (blocker K)).card := by
  classical
  let commonPairs := (P ∩ Q).image fun y ↦ ({x, y} : G413.Row alpha)
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hCommonInjective : Set.InjOn
      (fun y ↦ ({x, y} : G413.Row alpha)) (↑(P ∩ Q) : Set alpha) := by
    intro y hy z _ hEq
    have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
    have hyx : y ≠ x := fun hyx ↦ hxP (hyx ▸ hyP)
    have hyMem : y ∈ ({x, z} : G413.Row alpha) := by
      change ({x, y} : G413.Row alpha) = {x, z} at hEq
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    exact hyMem.resolve_left hyx
  have hCommonCard : commonPairs.card = (P ∩ Q).card :=
    Finset.card_image_iff.mpr hCommonInjective
  have hCommonSubset : commonPairs ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hE
    exact commonPoint_pair_mem_blocker hKCard hMaxDegree hAvoid hy
  have hAvoidPairSubset : pairRows (avoidPoint (blocker K) x) ⊆
      pairRows (blocker K) := by
    intro E hE
    obtain ⟨hEAvoid, hECard⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨(mem_avoidPoint.mp hEAvoid).1, hECard⟩
  have hDisjoint : Disjoint (pairRows (avoidPoint (blocker K) x))
      commonPairs := by
    apply Finset.disjoint_left.mpr
    intro E hEAvoid hECommon
    have hxE : x ∉ E := (mem_avoidPoint.mp (Finset.mem_filter.mp hEAvoid).1).2
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hECommon
    exact hxE (by simp)
  have hUnionSubset : pairRows (avoidPoint (blocker K) x) ∪ commonPairs ⊆
      pairRows (blocker K) :=
    Finset.union_subset hAvoidPairSubset hCommonSubset
  have hCard := Finset.card_le_card hUnionSubset
  rw [Finset.card_union_of_disjoint hDisjoint, hCommonCard] at hCard
  exact hCard

theorem residual_eq_deletePoint_of_card_eq_five
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha}
    (hKCard : K.card = 5)
    (hRCard : (residual K x).card = 5) :
    residual K x = deletePoint K x := by
  classical
  apply Finset.eq_of_subset_of_card_le (minimize_subset _)
  change (minimize (deletePoint K x)).card = 5 at hRCard
  change (deletePoint K x).card ≤ (minimize (deletePoint K x)).card
  have hDeleteUpper : (deletePoint K x).card ≤ 5 := by
    exact Finset.card_image_le.trans_eq hKCard
  omega

theorem avoidBlocker_card_ge_three_of_one_commonPoint
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hPairUpper : (pairRows (blocker K)).card ≤ 2)
    (hAvoid : avoidPoint K x = {P, Q})
    (hCommonCard : (P ∩ Q).card = 1) :
    3 ≤ (avoidPoint (blocker K) x).card := by
  classical
  let R := residual K x
  let B := avoidPoint (blocker K) x
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter K x
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hKRows x
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hQAvoid : Q ∈ avoidPoint K x := by simp [hAvoid]
  have hPK : P ∈ K := (mem_avoidPoint.mp hPAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hPDelete : P ∈ deletePoint K x :=
    Finset.mem_image.mpr ⟨P, hPK, by simp [hxP]⟩
  obtain ⟨M, hMR, -⟩ := exists_minimize_subset hPDelete
  have hRNonempty : R.Nonempty := by
    refine ⟨M, ?_⟩
    change M ∈ minimize (deletePoint K x)
    exact hMR
  have hBLower : 2 ≤ B.card := by
    simpa [B] using avoidBlocker_card_ge_two_of_two_avoidingRows hKRows hAvoid
  have hBRows : RowsCardAtLeast B 2 := by
    have hAllRows := blocker_rows_cardAtLeast_two_of_fiveRow_maxDegree_three
      hKCard hMaxDegree
    intro E hE
    exact hAllRows E (mem_avoidPoint.mp (by simpa [B] using hE)).1
  have hBlockerR : blocker R = B := by
    simpa [R, B] using blocker_residual K x
  have hBlockerB : blocker B = R := by
    rw [← hBlockerR, blocker_involution hRClutter]
  have hDegree : degree K x = 3 := by
    have hPQ : P ≠ Q := by
      intro hEq
      have hPCard := hKRows P hPK
      have hInter : P ∩ Q = P := by simp [hEq]
      rw [hInter] at hCommonCard
      omega
    have hPartition := card_avoidPoint_add_degree K x
    rw [hAvoid, Finset.card_pair hPQ, hKCard] at hPartition
    omega
  have hRPairs : (pairRows R).card ≤ 3 := by
    exact (pairRows_residual_card_le_degree hKRows x).trans_eq hDegree
  change 3 ≤ B.card
  by_contra hNot
  have hBCard : B.card = 2 := by omega
  have hRUpper : R.card ≤ 3 := by
    have hRRowsUpper : ∀ E ∈ R, E.card ≤ 2 := by
      intro E hE
      have hEBlockerB : E ∈ blocker B := by rw [hBlockerB]; exact hE
      have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hEBlockerB)
      simpa [hBCard] using hUpper
    have hPairEq : pairRows R = R := by
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro E hE
      exact Finset.mem_filter.mpr
        ⟨hE, by have := hRRows E hE; have := hRRowsUpper E hE; omega⟩
    rw [← hPairEq]
    exact hRPairs
  obtain ⟨y, hyR⟩ :=
    exists_singleton_row_of_blocker_card_eq_two_of_card_le_three
      hRClutter hRUpper (by simpa [hBlockerR] using hBRows)
      (by simpa [hBlockerR] using hBCard)
  have hLarge := hRRows {y} hyR
  simp at hLarge

theorem avoidBlocker_card_ge_five_of_one_commonPoint
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hPairUpper : (pairRows (blocker K)).card ≤ 2)
    (hAvoid : avoidPoint K x = {P, Q})
    (hCommonCard : (P ∩ Q).card = 1) :
    5 ≤ (avoidPoint (blocker K) x).card := by
  classical
  let R := residual K x
  let B := avoidPoint (blocker K) x
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter K x
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hKRows x
  have hRUpper : R.card ≤ 5 := (residual_card_le K x).trans_eq hKCard
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hQAvoid : Q ∈ avoidPoint K x := by simp [hAvoid]
  have hPK : P ∈ K := (mem_avoidPoint.mp hPAvoid).1
  have hQK : Q ∈ K := (mem_avoidPoint.mp hQAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hxQ : x ∉ Q := (mem_avoidPoint.mp hQAvoid).2
  have hPCard := hKRows P hPK
  have hQCard := hKRows Q hQK
  have hPQ : P ≠ Q := by
    intro hEq
    have hInter : P ∩ Q = P := by simp [hEq]
    rw [hInter] at hCommonCard
    omega
  have hDegree : degree K x = 3 := by
    have hPartition := card_avoidPoint_add_degree K x
    rw [hAvoid, Finset.card_pair hPQ, hKCard] at hPartition
    omega
  have hRPairs : (pairRows R).card ≤ 3 := by
    exact (pairRows_residual_card_le_degree hKRows x).trans_eq hDegree
  have hBClutter : IsClutter B := by
    rw [show B = blocker R by simpa [R, B] using (blocker_residual K x).symm]
    exact blocker_isClutter R
  have hBRows : RowsCardAtLeast B 2 := by
    have hAllRows := blocker_rows_cardAtLeast_two_of_fiveRow_maxDegree_three
      hKCard hMaxDegree
    intro E hE
    exact hAllRows E (mem_avoidPoint.mp (by simpa [B] using hE)).1
  have hBUpper : ∀ E ∈ B, E.card ≤ 5 := by
    intro E hE
    have hEBlocker : E ∈ blocker K :=
      (mem_avoidPoint.mp (by simpa [B] using hE)).1
    exact (minimalTransversal_card_le_rows (mem_blocker.mp hEBlocker)).trans_eq hKCard
  have hBlockerR : blocker R = B := by
    simpa [R, B] using blocker_residual K x
  have hBlockerB : blocker B = R := by
    rw [← hBlockerR, blocker_involution hRClutter]
  have hBPairUpper : (pairRows B).card ≤ 1 := by
    have hAdd := avoidPairRows_add_common_le_pairRows hKCard hMaxDegree hAvoid
    change (pairRows B).card + (P ∩ Q).card ≤
      (pairRows (blocker K)).card at hAdd
    rw [hCommonCard] at hAdd
    omega
  have hBLower := avoidBlocker_card_ge_three_of_one_commonPoint
    hKCard hKRows hMaxDegree hPairUpper hAvoid hCommonCard
  change 5 ≤ B.card
  change 3 ≤ B.card at hBLower
  by_contra hNot
  have hBUpperCard : B.card ≤ 4 := by omega
  have hCases : B.card = 3 ∨ B.card = 4 := by omega
  rcases hCases with hBCard | hBCard
  · have hProperty := threeRow_padded_blocker_property hBClutter hBCard
      hBRows hBUpper hBPairUpper (by simpa [hBlockerB] using hRRows)
      (by simpa [hBlockerB] using hRUpper)
    have hRCard : R.card = 5 := by simpa [hBlockerB] using hProperty.1
    have hREqDelete : R = deletePoint K x := by
      simpa [R] using residual_eq_deletePoint_of_card_eq_five hKCard
        (by simpa [R] using hRCard)
    have hPR : P ∈ R := by
      rw [hREqDelete]
      exact Finset.mem_image.mpr ⟨P, hPK, by simp [hxP]⟩
    have hPCardTwo := hProperty.2 P (by simpa [hBlockerB] using hPR)
    omega
  · by_cases hPair : ∃ E ∈ B, E.card = 2
    · obtain ⟨E, hEB, hECard⟩ := hPair
      have hProperty := fourRow_uniquePair_blocker_property hBClutter hBCard
        hBRows hBUpper hBPairUpper (by simpa [hBlockerB] using hRRows)
        (by simpa [hBlockerB] using hRUpper)
        (by rw [hBlockerB]; exact hRPairs) hEB hECard
      have hRCard : R.card = 5 := by simpa [hBlockerB] using hProperty.1
      have hREqDelete : R = deletePoint K x := by
        simpa [R] using residual_eq_deletePoint_of_card_eq_five hKCard
          (by simpa [R] using hRCard)
      have hPR : P ∈ R := by
        rw [hREqDelete]
        exact Finset.mem_image.mpr ⟨P, hPK, by simp [hxP]⟩
      have hQR : Q ∈ R := by
        rw [hREqDelete]
        exact Finset.mem_image.mpr ⟨Q, hQK, by simp [hxQ]⟩
      have hInter := hProperty.2 P (by simpa [hBlockerB] using hPR)
        Q (by simpa [hBlockerB] using hQR) hPCard hQCard hPQ
      omega
    · have hBLarge : RowsCardAtLeast B 3 := by
        intro E hE
        have hLower := hBRows E hE
        have hNotPair : E.card ≠ 2 := fun hECard ↦ hPair ⟨E, hE, hECard⟩
        omega
      exact fourRow_large_blocker_card_not_le_five hBClutter hBCard
        hBLarge hBUpper (by simpa [hBlockerB] using hRRows)
        (by simpa [hBlockerB] using hRUpper)
        (by rw [hBlockerB]; exact hRPairs)

end AiMathLab.P0054.G420
