import AiMathLab.P0054MiddleSevenNineSevenSideBasics

/-!
# Soundness reductions for the six-row residual coupling

This file contains only arbitrary-finite structural statements.  The finite
mask certificates live in separate modules.
-/

namespace AiMathLab.P0054.MiddleSevenNineSixResidualSound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem nineRows_partition_by_threeBlockerRow
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hECard : E.card = 9)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) :
    (∀ x ∈ T, degree E x = 3) ∧
      ∀ R ∈ E, (R ∩ T).card = 1 := by
  classical
  obtain ⟨x, a, b, hxa, hxb, hab, hTForm⟩ :=
    Finset.card_eq_three.mp hTCard
  have hUnion : T.biUnion (pointSupport E) = E := by
    ext R
    constructor
    · intro hR
      obtain ⟨u, _huT, hRSupport⟩ := Finset.mem_biUnion.mp hR
      exact (mem_pointSupport.mp hRSupport).1
    · intro hRE
      obtain ⟨u, huT, huR⟩ := (mem_blocker.mp hTBlocker).prop R hRE
      exact Finset.mem_biUnion.mpr
        ⟨u, huT, mem_pointSupport.mpr ⟨hRE, huR⟩⟩
  have hSumLower :
      9 ≤ degree E x + degree E a + degree E b := by
    have hBound :
        (T.biUnion (pointSupport E)).card ≤
          ∑ u ∈ T, (pointSupport E u).card :=
      Finset.card_biUnion_le
    rw [hUnion, hECard] at hBound
    simpa [hTForm, pointSupport_card, hxa, hxb, hab, Nat.add_assoc] using hBound
  have hxT : x ∈ T := by simp [hTForm]
  have haT : a ∈ T := by simp [hTForm]
  have hbT : b ∈ T := by simp [hTForm]
  have hxUpper := hTMax x hxT
  have haUpper := hTMax a haT
  have hbUpper := hTMax b hbT
  have hxDegree : degree E x = 3 := by omega
  have haDegree : degree E a = 3 := by omega
  have hbDegree : degree E b = 3 := by omega
  have hEveryDegree : ∀ u ∈ T, degree E u = 3 := by
    intro u huT
    rw [hTForm] at huT
    simp only [Finset.mem_insert, Finset.mem_singleton] at huT
    rcases huT with rfl | rfl | rfl
    · exact hxDegree
    · exact haDegree
    · exact hbDegree
  refine ⟨hEveryDegree, ?_⟩
  intro R hRE
  obtain ⟨u, huT, huR⟩ := (mem_blocker.mp hTBlocker).prop R hRE
  have hPositive : 0 < (R ∩ T).card :=
    Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨huR, huT⟩⟩
  have hAtMostOne : (R ∩ T).card ≤ 1 := by
    by_contra hNot
    obtain ⟨i, hiInter, j, hjInter, hij⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (R ∩ T).card)
    have hiT : i ∈ T := (Finset.mem_inter.mp hiInter).2
    have hjT : j ∈ T := (Finset.mem_inter.mp hjInter).2
    have hiR : i ∈ R := (Finset.mem_inter.mp hiInter).1
    have hjR : j ∈ R := (Finset.mem_inter.mp hjInter).1
    have hOverlap :
        (pointSupport E i ∩ pointSupport E j).Nonempty := by
      exact ⟨R, Finset.mem_inter.mpr
        ⟨mem_pointSupport.mpr ⟨hRE, hiR⟩,
          mem_pointSupport.mpr ⟨hRE, hjR⟩⟩⟩
    have hStrict := AiMathLab.P0054.G420.card_biUnion_lt_sum_of_overlap
      (I := T) (events := pointSupport E) hiT hjT hij hOverlap
    have hSumEq :
        ∑ k ∈ T, (pointSupport E k).card = 9 := by
      simp [hTForm, pointSupport_card, hxa, hxb, hab,
        hxDegree, haDegree, hbDegree]
    rw [hUnion, hECard, hSumEq] at hStrict
    omega
  omega

theorem sixRow_kernel_basic_data
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) :
    ∃ x a b,
      x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ T = {x, a, b} ∧
      let K := avoidPoint E x
      let aSide := pointSupport K a
      let bSide := pointSupport K b
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) := by
  classical
  have hPartition := nineRows_partition_by_threeBlockerRow
    hECard hTBlocker hTCard hTMax
  obtain ⟨x, a, b, hxa, hxb, hab, hTForm⟩ :=
    Finset.card_eq_three.mp hTCard
  refine ⟨x, a, b, hxa, hxb, hab, hTForm, ?_⟩
  let K := avoidPoint E x
  let aSide := pointSupport K a
  let bSide := pointSupport K b
  have hxT : x ∈ T := by simp [hTForm]
  have haT : a ∈ T := by simp [hTForm]
  have hbT : b ∈ T := by simp [hTForm]
  have hxDegree : degree E x = 3 := hPartition.1 x hxT
  have haDegree : degree E a = 3 := hPartition.1 a haT
  have hbDegree : degree E b = 3 := hPartition.1 b hbT
  have hNoTwo {R : Row alpha} (hRE : R ∈ E)
      {u v : alpha} (huT : u ∈ T) (hvT : v ∈ T) (huv : u ≠ v)
      (huR : u ∈ R) (hvR : v ∈ R) : False := by
    have hSubset : ({u, v} : Row alpha) ⊆ R ∩ T := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huR, huT⟩
      · exact Finset.mem_inter.mpr ⟨hvR, hvT⟩
    have hLower := Finset.card_le_card hSubset
    have hPairCard : ({u, v} : Row alpha).card = 2 := by simp [huv]
    rw [hPairCard, hPartition.2 R hRE] at hLower
    omega
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hEClutter x
  have hKCard : K.card = 6 := by
    have hCardPartition := card_avoidPoint_add_degree E x
    simpa [K, hECard, hxDegree] using hCardPartition
  have hKRows : RowsCardAtLeast K 4 := by
    intro R hRK
    exact hERows R (mem_avoidPoint.mp (by simpa [K] using hRK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
  have hBKUpper : (blocker K).card ≤ 7 := by
    have hLift := blocker_avoidPoint_card_le_blocker E x
    simpa [K, hDualCard] using hLift
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker E) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hDualRows x
      _ ≤ 3 := hDualMax x
  have hASupport : aSide = pointSupport E a := by
    ext R
    constructor
    · intro hRA
      have hRK : R ∈ K := (mem_pointSupport.mp hRA).1
      have haR : a ∈ R := (mem_pointSupport.mp hRA).2
      exact mem_pointSupport.mpr
        ⟨(mem_avoidPoint.mp (by simpa [K] using hRK)).1, haR⟩
    · intro hRA
      obtain ⟨hRE, haR⟩ := mem_pointSupport.mp hRA
      have hxR : x ∉ R := by
        intro hxR
        exact hNoTwo hRE hxT haT hxa hxR haR
      have hRK : R ∈ K := by
        simpa [K] using mem_avoidPoint.mpr ⟨hRE, hxR⟩
      exact mem_pointSupport.mpr ⟨hRK, haR⟩
  have hBSupport : bSide = pointSupport E b := by
    ext R
    constructor
    · intro hRB
      have hRK : R ∈ K := (mem_pointSupport.mp hRB).1
      have hbR : b ∈ R := (mem_pointSupport.mp hRB).2
      exact mem_pointSupport.mpr
        ⟨(mem_avoidPoint.mp (by simpa [K] using hRK)).1, hbR⟩
    · intro hRB
      obtain ⟨hRE, hbR⟩ := mem_pointSupport.mp hRB
      have hxR : x ∉ R := by
        intro hxR
        exact hNoTwo hRE hxT hbT hxb hxR hbR
      have hRK : R ∈ K := by
        simpa [K] using mem_avoidPoint.mpr ⟨hRE, hxR⟩
      exact mem_pointSupport.mpr ⟨hRK, hbR⟩
  have hASideCard : aSide.card = 3 := by
    rw [hASupport, pointSupport_card, haDegree]
  have hBSideCard : bSide.card = 3 := by
    rw [hBSupport, pointSupport_card, hbDegree]
  have hSideCover : aSide ∪ bSide = K := by
    ext R
    constructor
    · intro hR
      rcases Finset.mem_union.mp hR with hRA | hRB
      · exact (mem_pointSupport.mp hRA).1
      · exact (mem_pointSupport.mp hRB).1
    · intro hRK
      obtain ⟨hRE, hxR⟩ := mem_avoidPoint.mp (by simpa [K] using hRK)
      obtain ⟨u, huT, huR⟩ := (mem_blocker.mp hTBlocker).prop R hRE
      rw [hTForm] at huT
      simp only [Finset.mem_insert, Finset.mem_singleton] at huT
      rcases huT with rfl | rfl | rfl
      · exact (hxR huR).elim
      · exact Finset.mem_union_left _ (mem_pointSupport.mpr ⟨hRK, huR⟩)
      · exact Finset.mem_union_right _ (mem_pointSupport.mpr ⟨hRK, huR⟩)
  have hSidesDisjoint : Disjoint aSide bSide := by
    apply Finset.disjoint_left.mpr
    intro R hRA hRB
    have hRK : R ∈ K := (mem_pointSupport.mp hRA).1
    have hRE : R ∈ E :=
      (mem_avoidPoint.mp (by simpa [K] using hRK)).1
    exact hNoTwo hRE haT hbT hab
      (mem_pointSupport.mp hRA).2 (mem_pointSupport.mp hRB).2
  have hPairTransversal : IsTransversal K ({a, b} : Row alpha) := by
    intro R hRK
    have hInUnion : R ∈ aSide ∪ bSide := by rw [hSideCover]; exact hRK
    rcases Finset.mem_union.mp hInUnion with hRA | hRB
    · exact ⟨a, by simp, (mem_pointSupport.mp hRA).2⟩
    · exact ⟨b, by simp, (mem_pointSupport.mp hRB).2⟩
  have hPairBlocker : ({a, b} : Row alpha) ∈ blocker K :=
    pair_mem_blocker_of_transversal hBKRows hPairTransversal
  have hPairRow : ({a, b} : Row alpha) ∈ pairRows (blocker K) :=
    Finset.mem_filter.mpr ⟨hPairBlocker, by simp [hab]⟩
  exact ⟨hKClutter, hKCard, hKRows, hBKRows, hBKUpper, hPairUpper,
    hASideCard, hBSideCard, hSideCover, hSidesDisjoint, hPairRow⟩

theorem blocker_rows_cardAtLeast_two_of_no_common
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHNonempty : H.Nonempty)
    (hHRows : RowsCardAtLeast H 1)
    (hNoCommon : ∀ x, ∃ R ∈ H, x ∉ R) :
    RowsCardAtLeast (blocker H) 2 := by
  classical
  intro Q hQBlocker
  have hQTransversal := (mem_blocker.mp hQBlocker).prop
  have hQPositive : 0 < Q.card := by
    by_contra hNot
    have hQEmpty : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨R, hRH⟩ := hHNonempty
    obtain ⟨x, hxQ, _hxR⟩ := hQTransversal R hRH
    simp [hQEmpty] at hxQ
  by_contra hNotTwo
  have hQCard : Q.card = 1 := by omega
  obtain ⟨x, hQForm⟩ := Finset.card_eq_one.mp hQCard
  obtain ⟨R, hRH, hxR⟩ := hNoCommon x
  obtain ⟨y, hyQ, hyR⟩ := hQTransversal R hRH
  have hyx : y = x := by simpa [hQForm] using hyQ
  exact hxR (hyx ▸ hyR)

theorem threeSide_erased_has_common
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K side : G413.Hypergraph alpha} {center opposite : alpha}
    (hSideEq : side = avoidPoint K opposite)
    (hSideCard : side.card = 3)
    (hSideClutter : IsClutter side)
    (hSideRows : RowsCardAtLeast side 4)
    (hCenter : ∀ R ∈ side, center ∈ R)
    (hBKUpper : (blocker K).card ≤ 7) :
    ∃ common, ∀ R ∈ deletePoint side center, common ∈ R := by
  classical
  let residualSide := deletePoint side center
  have hEraseInj : Set.InjOn (fun R : Row alpha ↦ R.erase center) side := by
    intro R hR S hS hErase
    calc
      R = insert center (R.erase center) := (Finset.insert_erase (hCenter R hR)).symm
      _ = insert center (S.erase center) := congrArg (insert center) hErase
      _ = S := Finset.insert_erase (hCenter S hS)
  have hResidualCard : residualSide.card = 3 := by
    change (side.image fun R ↦ R.erase center).card = 3
    rw [Finset.card_image_iff.mpr hEraseInj, hSideCard]
  have hResidualClutter : IsClutter residualSide := by
    intro A hA B hB hAB
    obtain ⟨RA, hRA, hRAEq⟩ := Finset.mem_image.mp (by
      simpa [residualSide, deletePoint] using hA)
    obtain ⟨RB, hRB, hRBEq⟩ := Finset.mem_image.mp (by
      simpa [residualSide, deletePoint] using hB)
    subst A
    subst B
    have hSourceSubset : RA ⊆ RB := by
      intro x hxRA
      by_cases hxc : x = center
      · subst x
        exact hCenter RB hRB
      · have hxEraseA : x ∈ RA.erase center :=
          Finset.mem_erase.mpr ⟨hxc, hxRA⟩
        exact (Finset.mem_erase.mp (hAB hxEraseA)).2
    have hSourceEq : RA = RB := hSideClutter hRA hRB hSourceSubset
    exact congrArg (fun R : Row alpha ↦ R.erase center) hSourceEq
  have hResidualRows : RowsCardAtLeast residualSide 3 := by
    intro A hA
    obtain ⟨R, hRSide, hREq⟩ := Finset.mem_image.mp (by
      simpa [residualSide, deletePoint] using hA)
    subst A
    have hRLower := hSideRows R hRSide
    rw [Finset.card_erase_of_mem (hCenter R hRSide)]
    omega
  by_contra hNoCommon
  have hNoCommonPoint : ∀ x, ∃ R ∈ residualSide, x ∉ R := by
    intro x
    by_contra hNoMissing
    push_neg at hNoMissing
    exact hNoCommon ⟨x, hNoMissing⟩
  have hResidualNonempty : residualSide.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < residualSide.card)
  have hResidualRowsOne : RowsCardAtLeast residualSide 1 := by
    intro R hR
    exact (hResidualRows R hR).trans' (by omega)
  have hResidualBlockerRows : RowsCardAtLeast (blocker residualSide) 2 :=
    blocker_rows_cardAtLeast_two_of_no_common
      hResidualNonempty hResidualRowsOne hNoCommonPoint
  have hResidualBlockerLower : 7 ≤ (blocker residualSide).card :=
    AiMathLab.P0054.G419.threeRow_blocker_card_ge_seven
      hResidualClutter hResidualCard hResidualRows hResidualBlockerRows
  have hDeleteBlocker :
      blocker residualSide = avoidPoint (blocker side) center := by
    simpa [residualSide] using blocker_deletePoint side center
  have hAvoidLower : 7 ≤ (avoidPoint (blocker side) center).card := by
    rw [← hDeleteBlocker]
    exact hResidualBlockerLower
  have hSideNonempty : side.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < side.card)
  have hSingletonTransversal :
      IsTransversal side ({center} : Row alpha) := by
    intro R hR
    exact ⟨center, by simp, hCenter R hR⟩
  have hSingletonMinimal :
      IsMinimalTransversal side ({center} : Row alpha) := by
    refine isMinimalTransversal_iff.mpr ⟨hSingletonTransversal, ?_⟩
    intro S hS hSTransversal
    have hSEmpty : S = ∅ := Finset.eq_empty_of_ssubset_singleton hS
    subst S
    obtain ⟨R, hRSide⟩ := hSideNonempty
    obtain ⟨x, hxEmpty, _hxR⟩ := hSTransversal R hRSide
    simp at hxEmpty
  have hSingletonBlocker :
      ({center} : Row alpha) ∈ blocker side :=
    mem_blocker.mpr hSingletonMinimal
  have hSingletonNotAvoid :
      ({center} : Row alpha) ∉ avoidPoint (blocker side) center := by
    intro hAvoid
    exact (mem_avoidPoint.mp hAvoid).2 (by simp)
  have hInsertSubset :
      insert ({center} : Row alpha) (avoidPoint (blocker side) center) ⊆
        blocker side := by
    apply Finset.insert_subset hSingletonBlocker
    intro Q hQ
    exact (mem_avoidPoint.mp hQ).1
  have hSideBlockerLower : 8 ≤ (blocker side).card := by
    have hCard := Finset.card_le_card hInsertSubset
    rw [Finset.card_insert_of_notMem hSingletonNotAvoid] at hCard
    omega
  let lifts := (blocker side).image (avoidBlockerLift K opposite)
  have hLiftSubset : lifts ⊆ blocker K := by
    intro Q hQ
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hQ
    apply avoidBlockerLift_mem_blocker
    simpa [← hSideEq] using hSource
  have hLiftInj : Set.InjOn (avoidBlockerLift K opposite) (blocker side) := by
    apply (avoidBlockerLift_injective K opposite).mono
    intro Q hQ
    simpa [← hSideEq] using hQ
  have hLiftCard : lifts.card = (blocker side).card := by
    exact Finset.card_image_iff.mpr hLiftInj
  have hSideBlockerUpper : (blocker side).card ≤ (blocker K).card := by
    have hCard := Finset.card_le_card hLiftSubset
    simpa [hLiftCard] using hCard
  omega

theorem sixRow_kernel_side_common_points
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) :
    ∃ x a b c d,
      x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ T = {x, a, b} ∧
      let K := avoidPoint E x
      let aSide := pointSupport K a
      let bSide := pointSupport K b
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) ∧
        (∀ R ∈ deletePoint aSide a, c ∈ R) ∧
        ∀ R ∈ deletePoint bSide b, d ∈ R := by
  classical
  obtain ⟨x, a, b, hxa, hxb, hab, hTForm, hBasic⟩ :=
    sixRow_kernel_basic_data hEClutter hECard hERows hDualCard
      hDualRows hDualMax hTBlocker hTCard hTMax
  let K := avoidPoint E x
  let aSide := pointSupport K a
  let bSide := pointSupport K b
  have hData :
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) := by
    simpa [K, aSide, bSide] using hBasic
  rcases hData with
    ⟨hKClutter, hKCard, hKRows, hBKRows, hBKUpper, hPairUpper,
      hASideCard, hBSideCard, hSideCover, hSidesDisjoint, hPairRow⟩
  have hASideEq : aSide = avoidPoint K b := by
    ext R
    constructor
    · intro hRA
      have hRK : R ∈ K := (mem_pointSupport.mp hRA).1
      have hbR : b ∉ R := by
        intro hbR
        have hRB : R ∈ bSide := mem_pointSupport.mpr ⟨hRK, hbR⟩
        exact Finset.disjoint_left.mp hSidesDisjoint hRA hRB
      exact mem_avoidPoint.mpr ⟨hRK, hbR⟩
    · intro hRAvoid
      obtain ⟨hRK, hbR⟩ := mem_avoidPoint.mp hRAvoid
      have hUnion : R ∈ aSide ∪ bSide := by rw [hSideCover]; exact hRK
      rcases Finset.mem_union.mp hUnion with hRA | hRB
      · exact hRA
      · exact (hbR (mem_pointSupport.mp hRB).2).elim
  have hBSideEq : bSide = avoidPoint K a := by
    ext R
    constructor
    · intro hRB
      have hRK : R ∈ K := (mem_pointSupport.mp hRB).1
      have haR : a ∉ R := by
        intro haR
        have hRA : R ∈ aSide := mem_pointSupport.mpr ⟨hRK, haR⟩
        exact Finset.disjoint_left.mp hSidesDisjoint hRA hRB
      exact mem_avoidPoint.mpr ⟨hRK, haR⟩
    · intro hBAvoid
      obtain ⟨hRK, haR⟩ := mem_avoidPoint.mp hBAvoid
      have hUnion : R ∈ aSide ∪ bSide := by rw [hSideCover]; exact hRK
      rcases Finset.mem_union.mp hUnion with hRA | hRB
      · exact (haR (mem_pointSupport.mp hRA).2).elim
      · exact hRB
  have hASideClutter : IsClutter aSide := by
    intro R hRA S hSA hRS
    exact hKClutter (mem_pointSupport.mp hRA).1
      (mem_pointSupport.mp hSA).1 hRS
  have hBSideClutter : IsClutter bSide := by
    intro R hRB S hSB hRS
    exact hKClutter (mem_pointSupport.mp hRB).1
      (mem_pointSupport.mp hSB).1 hRS
  have hASideRows : RowsCardAtLeast aSide 4 := by
    intro R hRA
    exact hKRows R (mem_pointSupport.mp hRA).1
  have hBSideRows : RowsCardAtLeast bSide 4 := by
    intro R hRB
    exact hKRows R (mem_pointSupport.mp hRB).1
  have hACenter : ∀ R ∈ aSide, a ∈ R := by
    intro R hRA
    exact (mem_pointSupport.mp hRA).2
  have hBCenter : ∀ R ∈ bSide, b ∈ R := by
    intro R hRB
    exact (mem_pointSupport.mp hRB).2
  obtain ⟨c, hcCommon⟩ := threeSide_erased_has_common
    hASideEq hASideCard hASideClutter hASideRows hACenter hBKUpper
  obtain ⟨d, hdCommon⟩ := threeSide_erased_has_common
    hBSideEq hBSideCard hBSideClutter hBSideRows hBCenter hBKUpper
  refine ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, ?_⟩
  exact ⟨hKClutter, hKCard, hKRows, hBKRows, hBKUpper, hPairUpper,
    hASideCard, hBSideCard, hSideCover, hSidesDisjoint, hPairRow,
    hcCommon, hdCommon⟩

theorem threeSide_common_pairRow
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K side other : G413.Hypergraph alpha} {center opposite common : alpha}
    (hSideNonempty : side.Nonempty)
    (hCover : side ∪ other = K)
    (hSideAvoid : ∀ R ∈ side, opposite ∉ R)
    (hOtherCenter : ∀ R ∈ other, opposite ∈ R)
    (hCommon : ∀ R ∈ deletePoint side center, common ∈ R)
    (hBKRows : RowsCardAtLeast (blocker K) 2) :
    common ≠ center ∧ common ≠ opposite ∧
      ({opposite, common} : Row alpha) ∈ pairRows (blocker K) := by
  classical
  obtain ⟨R, hRSide⟩ := hSideNonempty
  have hEraseMember : R.erase center ∈ deletePoint side center := by
    exact Finset.mem_image.mpr ⟨R, hRSide, rfl⟩
  have hcErase := hCommon (R.erase center) hEraseMember
  have hcNeCenter : common ≠ center := (Finset.mem_erase.mp hcErase).1
  have hcR : common ∈ R := (Finset.mem_erase.mp hcErase).2
  have hcNeOpposite : common ≠ opposite := by
    intro hEq
    exact hSideAvoid R hRSide (hEq ▸ hcR)
  have hPairTransversal :
      IsTransversal K ({opposite, common} : Row alpha) := by
    intro A hAK
    have hUnion : A ∈ side ∪ other := by rw [hCover]; exact hAK
    rcases Finset.mem_union.mp hUnion with hASide | hAOther
    · have hAErase : A.erase center ∈ deletePoint side center :=
        Finset.mem_image.mpr ⟨A, hASide, rfl⟩
      have hcA : common ∈ A :=
        (Finset.mem_erase.mp (hCommon (A.erase center) hAErase)).2
      exact ⟨common, by simp, hcA⟩
    · exact ⟨opposite, by simp, hOtherCenter A hAOther⟩
  have hPairBlocker :
      ({opposite, common} : Row alpha) ∈ blocker K :=
    pair_mem_blocker_of_transversal hBKRows hPairTransversal
  exact ⟨hcNeCenter, hcNeOpposite,
    Finset.mem_filter.mpr ⟨hPairBlocker,
      by simp [hcNeOpposite, hcNeOpposite.symm]⟩⟩

theorem sixRow_side_common_points_rigid
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K aSide bSide : G413.Hypergraph alpha} {a b c d : alpha}
    (hab : a ≠ b)
    (hKCard : K.card = 6)
    (hKMax : MaxDegreeAtMost K 4)
    (hASideCard : aSide.card = 3)
    (hBSideCard : bSide.card = 3)
    (hCover : aSide ∪ bSide = K)
    (hASideAvoid : ∀ R ∈ aSide, b ∉ R)
    (hBSideAvoid : ∀ R ∈ bSide, a ∉ R)
    (hACenter : ∀ R ∈ aSide, a ∈ R)
    (hBCenter : ∀ R ∈ bSide, b ∈ R)
    (hcCommon : ∀ R ∈ deletePoint aSide a, c ∈ R)
    (hdCommon : ∀ R ∈ deletePoint bSide b, d ∈ R)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hPairUpper : (pairRows (blocker K)).card ≤ 3)
    (hABPair : ({a, b} : Row alpha) ∈ pairRows (blocker K)) :
    pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} ∧
      (pairRows (blocker K)).card = 3 ∧
      c ≠ d ∧
      (∀ c', (∀ R ∈ deletePoint aSide a, c' ∈ R) → c' = c) ∧
      ∀ d', (∀ R ∈ deletePoint bSide b, d' ∈ R) → d' = d := by
  classical
  have hASideNonempty : aSide.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < aSide.card)
  have hBSideNonempty : bSide.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < bSide.card)
  obtain ⟨hcNeA, hcNeB, hBCPair⟩ := threeSide_common_pairRow
    hASideNonempty hCover hASideAvoid hBCenter hcCommon hBKRows
  have hReverseCover : bSide ∪ aSide = K := by
    simpa [Finset.union_comm] using hCover
  obtain ⟨hdNeB, hdNeA, hADPair⟩ := threeSide_common_pairRow
    hBSideNonempty hReverseCover hBSideAvoid hACenter hdCommon hBKRows
  have hABNeBC : ({a, b} : Row alpha) ≠ {b, c} := by
    intro hEq
    have haBC : a ∈ ({b, c} : Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at haBC
    rcases haBC with hab' | hac
    · exact hab hab'
    · exact hcNeA hac.symm
  have hABNeAD : ({a, b} : Row alpha) ≠ {a, d} := by
    intro hEq
    have hbAD : b ∈ ({a, d} : Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbAD
    rcases hbAD with hba | hbd
    · exact hab hba.symm
    · exact hdNeB hbd.symm
  have hBCNeAD : ({b, c} : Row alpha) ≠ {a, d} := by
    intro hEq
    have hbAD : b ∈ ({a, d} : Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbAD
    rcases hbAD with hba | hbd
    · exact hab hba.symm
    · exact hdNeB hbd.symm
  have hKnownPairsCard :
      ({{a, b}, {b, c}, {a, d}} : G413.Hypergraph alpha).card = 3 := by
    simp [hABNeBC, hABNeAD, hBCNeAD]
  have hKnownPairsSubset :
      ({{a, b}, {b, c}, {a, d}} : G413.Hypergraph alpha) ⊆
        pairRows (blocker K) := by
    intro Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact hABPair
    · exact hBCPair
    · exact hADPair
  have hPairRowsEq :
      pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} := by
    exact (Finset.eq_of_subset_of_card_le hKnownPairsSubset (by
      rw [hKnownPairsCard]
      exact hPairUpper)).symm
  have hcNeD : c ≠ d := by
    intro hcd
    have hKSubset : K ⊆ pointSupport K c := by
      intro R hRK
      have hSide : R ∈ aSide ∪ bSide := by
        rw [hCover]
        exact hRK
      rcases Finset.mem_union.mp hSide with hRA | hRB
      · have hErase : R.erase a ∈ deletePoint aSide a :=
          Finset.mem_image.mpr ⟨R, hRA, rfl⟩
        have hcR : c ∈ R :=
          (Finset.mem_erase.mp (hcCommon (R.erase a) hErase)).2
        exact mem_pointSupport.mpr ⟨hRK, hcR⟩
      · have hErase : R.erase b ∈ deletePoint bSide b :=
          Finset.mem_image.mpr ⟨R, hRB, rfl⟩
        have hdR : d ∈ R :=
          (Finset.mem_erase.mp (hdCommon (R.erase b) hErase)).2
        exact mem_pointSupport.mpr ⟨hRK, hcd.symm ▸ hdR⟩
    have hSixLower := Finset.card_le_card hKSubset
    rw [hKCard, pointSupport_card] at hSixLower
    have hFourUpper := hKMax c
    omega
  have hPairRowsCard : (pairRows (blocker K)).card = 3 := by
    rw [hPairRowsEq, hKnownPairsCard]
  refine ⟨hPairRowsEq, hPairRowsCard, hcNeD, ?_, ?_⟩
  · intro c' hc'Common
    obtain ⟨hc'NeA, hc'NeB, hBC'Pair⟩ := threeSide_common_pairRow
      hASideNonempty hCover hASideAvoid hBCenter hc'Common hBKRows
    have hBC'Mem :
        ({b, c'} : Row alpha) ∈
          ({{a, b}, {b, c}, {a, d}} : G413.Hypergraph alpha) := by
      rw [← hPairRowsEq]
      exact hBC'Pair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hBC'Mem
    rcases hBC'Mem with hEqAB | hEqBC | hEqAD
    · have hc'Mem : c' ∈ ({a, b} : Row alpha) := by
        rw [← hEqAB]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'Mem
      rcases hc'Mem with hc'a | hc'b
      · exact (hc'NeA hc'a).elim
      · exact (hc'NeB hc'b).elim
    · have hc'Mem : c' ∈ ({b, c} : Row alpha) := by
        rw [← hEqBC]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'Mem
      rcases hc'Mem with hc'b | hc'c
      · exact (hc'NeB hc'b).elim
      · exact hc'c
    · have hbAD : b ∈ ({a, d} : Row alpha) := by
        rw [← hEqAD]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbAD
      rcases hbAD with hba | hbd
      · exact (hab hba.symm).elim
      · exact (hdNeB hbd.symm).elim
  · intro d' hd'Common
    obtain ⟨hd'NeB, hd'NeA, hAD'Pair⟩ := threeSide_common_pairRow
      hBSideNonempty hReverseCover hBSideAvoid hACenter hd'Common hBKRows
    have hAD'Mem :
        ({a, d'} : Row alpha) ∈
          ({{a, b}, {b, c}, {a, d}} : G413.Hypergraph alpha) := by
      rw [← hPairRowsEq]
      exact hAD'Pair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hAD'Mem
    rcases hAD'Mem with hEqAB | hEqBC | hEqAD
    · have hd'Mem : d' ∈ ({a, b} : Row alpha) := by
        rw [← hEqAB]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd'Mem
      rcases hd'Mem with hd'a | hd'b
      · exact (hd'NeA hd'a).elim
      · exact (hd'NeB hd'b).elim
    · have haBC : a ∈ ({b, c} : Row alpha) := by
        rw [← hEqBC]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at haBC
      rcases haBC with hab' | hac
      · exact (hab hab').elim
      · exact (hcNeA hac.symm).elim
    · have hd'Mem : d' ∈ ({a, d} : Row alpha) := by
        rw [← hEqAD]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd'Mem
      rcases hd'Mem with hd'a | hd'd
      · exact (hd'NeA hd'a).elim
      · exact hd'd

theorem threeRow_delete_unique_common_data
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {common : alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 3)
    (hHRowsLower : RowsCardAtLeast H 3)
    (hHRowsUpper : ∀ R ∈ H, R.card ≤ 6)
    (hCommon : ∀ R ∈ H, common ∈ R)
    (hUnique : ∀ point, (∀ R ∈ H, point ∈ R) → point = common) :
    let residual := deletePoint H common
    IsClutter residual ∧ residual.card = 3 ∧
      RowsCardAtLeast residual 2 ∧
      (∀ R ∈ residual, R.card ≤ 5) ∧
      ∀ point, ∃ R ∈ residual, point ∉ R := by
  classical
  let residual := deletePoint H common
  have hEraseInj : Set.InjOn (fun R : Row alpha ↦ R.erase common) H := by
    intro R hR S hS hErase
    calc
      R = insert common (R.erase common) :=
        (Finset.insert_erase (hCommon R hR)).symm
      _ = insert common (S.erase common) := congrArg (insert common) hErase
      _ = S := Finset.insert_erase (hCommon S hS)
  have hResidualCard : residual.card = 3 := by
    change (H.image fun R ↦ R.erase common).card = 3
    rw [Finset.card_image_iff.mpr hEraseInj, hHCard]
  have hResidualClutter : IsClutter residual := by
    intro A hA B hB hAB
    obtain ⟨RA, hRA, hRAEq⟩ := Finset.mem_image.mp (by
      simpa [residual, deletePoint] using hA)
    obtain ⟨RB, hRB, hRBEq⟩ := Finset.mem_image.mp (by
      simpa [residual, deletePoint] using hB)
    subst A
    subst B
    have hSourceSubset : RA ⊆ RB := by
      intro x hxRA
      by_cases hxc : x = common
      · subst x
        exact hCommon RB hRB
      · have hxEraseA : x ∈ RA.erase common :=
          Finset.mem_erase.mpr ⟨hxc, hxRA⟩
        exact (Finset.mem_erase.mp (hAB hxEraseA)).2
    have hSourceEq : RA = RB := hHClutter hRA hRB hSourceSubset
    exact congrArg (fun R : Row alpha ↦ R.erase common) hSourceEq
  have hResidualRowsLower : RowsCardAtLeast residual 2 := by
    intro A hA
    obtain ⟨R, hRH, hREq⟩ := Finset.mem_image.mp (by
      simpa [residual, deletePoint] using hA)
    subst A
    have hLower := hHRowsLower R hRH
    rw [Finset.card_erase_of_mem (hCommon R hRH)]
    omega
  have hResidualRowsUpper : ∀ A ∈ residual, A.card ≤ 5 := by
    intro A hA
    obtain ⟨R, hRH, hREq⟩ := Finset.mem_image.mp (by
      simpa [residual, deletePoint] using hA)
    subst A
    have hUpper := hHRowsUpper R hRH
    rw [Finset.card_erase_of_mem (hCommon R hRH)]
    omega
  have hNoCommon : ∀ point, ∃ R ∈ residual, point ∉ R := by
    intro point
    by_contra hNoMissing
    push_neg at hNoMissing
    have hPointCommonH : ∀ R ∈ H, point ∈ R := by
      intro R hRH
      have hErase : R.erase common ∈ residual := by
        exact Finset.mem_image.mpr ⟨R, hRH, rfl⟩
      exact (Finset.mem_erase.mp
        (hNoMissing (R.erase common) hErase)).2
    have hPointEq : point = common := hUnique point hPointCommonH
    obtain ⟨R, hRH⟩ : H.Nonempty :=
      Finset.card_pos.mp (by omega : 0 < H.card)
    have hErase : R.erase common ∈ residual := by
      exact Finset.mem_image.mpr ⟨R, hRH, rfl⟩
    have hPointErase := hNoMissing (R.erase common) hErase
    rw [hPointEq] at hPointErase
    exact Finset.notMem_erase common R hPointErase
  exact ⟨hResidualClutter, hResidualCard, hResidualRowsLower,
    hResidualRowsUpper, hNoCommon⟩

theorem threeRow_delete_center_data
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {side : G413.Hypergraph alpha} {center : alpha}
    (hSideClutter : IsClutter side)
    (hSideCard : side.card = 3)
    (hSideRowsLower : RowsCardAtLeast side 4)
    (hSideRowsUpper : ∀ R ∈ side, R.card ≤ 7)
    (hCenter : ∀ R ∈ side, center ∈ R) :
    let deleted := deletePoint side center
    IsClutter deleted ∧ deleted.card = 3 ∧
      RowsCardAtLeast deleted 3 ∧
      ∀ R ∈ deleted, R.card ≤ 6 := by
  classical
  let deleted := deletePoint side center
  have hEraseInj : Set.InjOn (fun R : Row alpha ↦ R.erase center) side := by
    intro R hR S hS hErase
    calc
      R = insert center (R.erase center) :=
        (Finset.insert_erase (hCenter R hR)).symm
      _ = insert center (S.erase center) := congrArg (insert center) hErase
      _ = S := Finset.insert_erase (hCenter S hS)
  have hDeletedCard : deleted.card = 3 := by
    change (side.image fun R ↦ R.erase center).card = 3
    rw [Finset.card_image_iff.mpr hEraseInj, hSideCard]
  have hDeletedClutter : IsClutter deleted := by
    intro A hA B hB hAB
    obtain ⟨RA, hRA, hRAEq⟩ := Finset.mem_image.mp (by
      simpa [deleted, deletePoint] using hA)
    obtain ⟨RB, hRB, hRBEq⟩ := Finset.mem_image.mp (by
      simpa [deleted, deletePoint] using hB)
    subst A
    subst B
    have hSourceSubset : RA ⊆ RB := by
      intro x hxRA
      by_cases hxc : x = center
      · subst x
        exact hCenter RB hRB
      · have hxEraseA : x ∈ RA.erase center :=
          Finset.mem_erase.mpr ⟨hxc, hxRA⟩
        exact (Finset.mem_erase.mp (hAB hxEraseA)).2
    have hSourceEq : RA = RB := hSideClutter hRA hRB hSourceSubset
    exact congrArg (fun R : Row alpha ↦ R.erase center) hSourceEq
  have hDeletedRowsLower : RowsCardAtLeast deleted 3 := by
    intro A hA
    obtain ⟨R, hRSide, hREq⟩ := Finset.mem_image.mp (by
      simpa [deleted, deletePoint] using hA)
    subst A
    have hLower := hSideRowsLower R hRSide
    rw [Finset.card_erase_of_mem (hCenter R hRSide)]
    omega
  have hDeletedRowsUpper : ∀ A ∈ deleted, A.card ≤ 6 := by
    intro A hA
    obtain ⟨R, hRSide, hREq⟩ := Finset.mem_image.mp (by
      simpa [deleted, deletePoint] using hA)
    subst A
    have hUpper := hSideRowsUpper R hRSide
    rw [Finset.card_erase_of_mem (hCenter R hRSide)]
    omega
  exact ⟨hDeletedClutter, hDeletedCard, hDeletedRowsLower,
    hDeletedRowsUpper⟩

theorem sixRow_kernel_rigid_common_points
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hEMax : MaxDegreeAtMost E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) :
    ∃ x a b c d,
      x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ T = {x, a, b} ∧
      let K := avoidPoint E x
      let aSide := pointSupport K a
      let bSide := pointSupport K b
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        MaxDegreeAtMost K 4 ∧ (∀ R ∈ K, R.card ≤ 7) ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) ∧
        pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} ∧
        (pairRows (blocker K)).card = 3 ∧
        (∀ R ∈ aSide, b ∉ R) ∧ (∀ R ∈ bSide, a ∉ R) ∧
        (∀ R ∈ aSide, a ∈ R) ∧ (∀ R ∈ bSide, b ∈ R) ∧
        (∀ R ∈ deletePoint aSide a, c ∈ R) ∧
        (∀ R ∈ deletePoint bSide b, d ∈ R) ∧
        c ≠ d ∧
        (∀ c', (∀ R ∈ deletePoint aSide a, c' ∈ R) → c' = c) ∧
        ∀ d', (∀ R ∈ deletePoint bSide b, d' ∈ R) → d' = d := by
  classical
  obtain ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, hData⟩ :=
    sixRow_kernel_side_common_points hEClutter hECard hERows hDualCard
      hDualRows hDualMax hTBlocker hTCard hTMax
  let K := avoidPoint E x
  let aSide := pointSupport K a
  let bSide := pointSupport K b
  have hCore :
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) ∧
        (∀ R ∈ deletePoint aSide a, c ∈ R) ∧
        ∀ R ∈ deletePoint bSide b, d ∈ R := by
    simpa [K, aSide, bSide] using hData
  rcases hCore with
    ⟨hKClutter, hKCard, hKRows, hBKRows, hBKUpper, hPairUpper,
      hASideCard, hBSideCard, hCover, hDisjoint, hABPair,
      hcCommon, hdCommon⟩
  have hKSubsetE : K ⊆ E := by
    intro R hRK
    exact (mem_avoidPoint.mp (by simpa [K] using hRK)).1
  have hKMax : MaxDegreeAtMost K 4 := by
    intro point
    exact (degree_mono hKSubsetE point).trans (hEMax point)
  have hERowsUpper : ∀ R ∈ E, R.card ≤ 7 := by
    intro R hRE
    have hRDouble : R ∈ blocker (blocker E) := by
      rw [blocker_involution hEClutter]
      exact hRE
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hRDouble)
    simpa [hDualCard] using hUpper
  have hKRowsUpper : ∀ R ∈ K, R.card ≤ 7 := by
    intro R hRK
    exact hERowsUpper R (hKSubsetE hRK)
  have hASideAvoid : ∀ R ∈ aSide, b ∉ R := by
    intro R hRA hbR
    have hRB : R ∈ bSide :=
      mem_pointSupport.mpr ⟨(mem_pointSupport.mp hRA).1, hbR⟩
    exact Finset.disjoint_left.mp hDisjoint hRA hRB
  have hBSideAvoid : ∀ R ∈ bSide, a ∉ R := by
    intro R hRB haR
    have hRA : R ∈ aSide :=
      mem_pointSupport.mpr ⟨(mem_pointSupport.mp hRB).1, haR⟩
    exact Finset.disjoint_left.mp hDisjoint hRA hRB
  have hACenter : ∀ R ∈ aSide, a ∈ R := by
    intro R hRA
    exact (mem_pointSupport.mp hRA).2
  have hBCenter : ∀ R ∈ bSide, b ∈ R := by
    intro R hRB
    exact (mem_pointSupport.mp hRB).2
  obtain ⟨hPairRowsEq, hPairRowsCard, hcNeD, hcUnique, hdUnique⟩ :=
    sixRow_side_common_points_rigid
    hab hKCard hKMax hASideCard hBSideCard hCover
      hASideAvoid hBSideAvoid hACenter hBCenter hcCommon hdCommon
      hBKRows hPairUpper hABPair
  refine ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, ?_⟩
  exact ⟨hKClutter, hKCard, hKRows, hKMax, hKRowsUpper,
    hBKRows, hBKUpper, hPairUpper, hASideCard, hBSideCard,
    hCover, hDisjoint, hABPair, hPairRowsEq, hPairRowsCard,
    hASideAvoid, hBSideAvoid,
    hACenter, hBCenter, hcCommon, hdCommon, hcNeD, hcUnique, hdUnique⟩

theorem doubleDelete_blocker_add_pairRows_le
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K side : G413.Hypergraph alpha} {center common opposite : alpha}
    (hSideEq : side = avoidPoint K opposite)
    (hCenterNeOpposite : center ≠ opposite)
    (hCommonNeOpposite : common ≠ opposite)
    (hPairHit : ∀ Q ∈ pairRows (blocker K), center ∈ Q ∨ common ∈ Q) :
    (blocker (deletePoint (deletePoint side center) common)).card +
        (pairRows (blocker K)).card ≤
      (blocker K).card := by
  classical
  let residual := deletePoint (deletePoint side center) common
  let lifts := (blocker residual).image (avoidBlockerLift K opposite)
  have source_data {T : Row alpha} (hT : T ∈ blocker residual) :
      T ∈ blocker (avoidPoint K opposite) ∧ center ∉ T ∧ common ∉ T := by
    have hOuter :
        T ∈ avoidPoint (blocker (deletePoint side center)) common := by
      rw [← blocker_deletePoint (deletePoint side center) common]
      simpa [residual] using hT
    obtain ⟨hTFirst, hCommonT⟩ := mem_avoidPoint.mp hOuter
    have hInner : T ∈ avoidPoint (blocker side) center := by
      rw [← blocker_deletePoint side center]
      exact hTFirst
    obtain ⟨hTSide, hCenterT⟩ := mem_avoidPoint.mp hInner
    have hTSource : T ∈ blocker (avoidPoint K opposite) := by
      rw [← hSideEq]
      exact hTSide
    exact ⟨hTSource, hCenterT, hCommonT⟩
  have lift_avoids {T : Row alpha} (hT : T ∈ blocker residual) :
      center ∉ avoidBlockerLift K opposite T ∧
        common ∉ avoidBlockerLift K opposite T := by
    obtain ⟨_hTSource, hCenterT, hCommonT⟩ := source_data hT
    constructor
    · by_cases hTransversal : IsTransversal K T
      · simp [avoidBlockerLift, hTransversal, hCenterT]
      · simp [avoidBlockerLift, hTransversal,
          hCenterNeOpposite, hCenterT]
    · by_cases hTransversal : IsTransversal K T
      · simp [avoidBlockerLift, hTransversal, hCommonT]
      · simp [avoidBlockerLift, hTransversal,
          hCommonNeOpposite, hCommonT]
  have hLiftsSubset : lifts ⊆ blocker K := by
    intro Q hQ
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hQ
    exact avoidBlockerLift_mem_blocker (source_data hT).1
  have hLiftInj :
      Set.InjOn (avoidBlockerLift K opposite) (blocker residual) := by
    intro T hT U hU hEq
    exact avoidBlockerLift_injective K opposite
      (source_data hT).1 (source_data hU).1 hEq
  have hLiftsCard : lifts.card = (blocker residual).card := by
    exact Finset.card_image_iff.mpr hLiftInj
  have hPairSubset : pairRows (blocker K) ⊆ blocker K := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).1
  have hDisjoint : Disjoint lifts (pairRows (blocker K)) := by
    apply Finset.disjoint_left.mpr
    intro Q hQLift hQPair
    obtain ⟨T, hT, hLiftEq⟩ := Finset.mem_image.mp hQLift
    have hAvoid := lift_avoids hT
    have hHit := hPairHit Q hQPair
    rcases hHit with hCenterQ | hCommonQ
    · exact hAvoid.1 (hLiftEq.symm ▸ hCenterQ)
    · exact hAvoid.2 (hLiftEq.symm ▸ hCommonQ)
  have hUnionSubset : lifts ∪ pairRows (blocker K) ⊆ blocker K := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQLift | hQPair
    · exact hLiftsSubset hQLift
    · exact hPairSubset hQPair
  calc
    (blocker (deletePoint (deletePoint side center) common)).card +
          (pairRows (blocker K)).card =
        lifts.card + (pairRows (blocker K)).card := by
      simpa [residual] using congrArg
        (fun n ↦ n + (pairRows (blocker K)).card) hLiftsCard.symm
    _ = (lifts ∪ pairRows (blocker K)).card :=
      (Finset.card_union_of_disjoint hDisjoint).symm
    _ ≤ (blocker K).card := Finset.card_le_card hUnionSubset

theorem sixRow_kernel_residual_marginal_data
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : Row alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hEMax : MaxDegreeAtMost E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    (hTBlocker : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hTMax : ∀ x ∈ T, degree E x ≤ 3) :
    ∃ x a b c d,
      x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ T = {x, a, b} ∧
      let K := avoidPoint E x
      let aSide := pointSupport K a
      let bSide := pointSupport K b
      let aCentered := deletePoint aSide a
      let bCentered := deletePoint bSide b
      let aResidual := deletePoint aCentered c
      let bResidual := deletePoint bCentered d
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        MaxDegreeAtMost K 4 ∧ RowsCardAtLeast (blocker K) 2 ∧
        (blocker K).card ≤ 7 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        aSide = avoidPoint K b ∧ bSide = avoidPoint K a ∧
        (∀ R ∈ aSide, a ∈ R) ∧ (∀ R ∈ bSide, b ∈ R) ∧
        (∀ R ∈ aCentered, c ∈ R) ∧
        (∀ R ∈ bCentered, d ∈ R) ∧
        pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} ∧
        (pairRows (blocker K)).card = 3 ∧
        c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d ∧
        IsClutter aResidual ∧ aResidual.card = 3 ∧
        RowsCardAtLeast aResidual 2 ∧
        (∀ R ∈ aResidual, R.card ≤ 5) ∧
        (∀ point, ∃ R ∈ aResidual, point ∉ R) ∧
        (blocker aResidual).card ≤ 4 ∧
        IsClutter bResidual ∧ bResidual.card = 3 ∧
        RowsCardAtLeast bResidual 2 ∧
        (∀ R ∈ bResidual, R.card ≤ 5) ∧
        (∀ point, ∃ R ∈ bResidual, point ∉ R) ∧
        (blocker bResidual).card ≤ 4 := by
  classical
  obtain ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, hData⟩ :=
    sixRow_kernel_rigid_common_points hEClutter hECard hERows hEMax
      hDualCard hDualRows hDualMax hTBlocker hTCard hTMax
  let K := avoidPoint E x
  let aSide := pointSupport K a
  let bSide := pointSupport K b
  let aCentered := deletePoint aSide a
  let bCentered := deletePoint bSide b
  let aResidual := deletePoint aCentered c
  let bResidual := deletePoint bCentered d
  have hRigid :
      IsClutter K ∧ K.card = 6 ∧ RowsCardAtLeast K 4 ∧
        MaxDegreeAtMost K 4 ∧ (∀ R ∈ K, R.card ≤ 7) ∧
        RowsCardAtLeast (blocker K) 2 ∧ (blocker K).card ≤ 7 ∧
        (pairRows (blocker K)).card ≤ 3 ∧
        aSide.card = 3 ∧ bSide.card = 3 ∧
        aSide ∪ bSide = K ∧ Disjoint aSide bSide ∧
        ({a, b} : Row alpha) ∈ pairRows (blocker K) ∧
        pairRows (blocker K) = {{a, b}, {b, c}, {a, d}} ∧
        (pairRows (blocker K)).card = 3 ∧
        (∀ R ∈ aSide, b ∉ R) ∧ (∀ R ∈ bSide, a ∉ R) ∧
        (∀ R ∈ aSide, a ∈ R) ∧ (∀ R ∈ bSide, b ∈ R) ∧
        (∀ R ∈ aCentered, c ∈ R) ∧
        (∀ R ∈ bCentered, d ∈ R) ∧
        c ≠ d ∧
        (∀ c', (∀ R ∈ aCentered, c' ∈ R) → c' = c) ∧
        ∀ d', (∀ R ∈ bCentered, d' ∈ R) → d' = d := by
    simpa [K, aSide, bSide, aCentered, bCentered] using hData
  rcases hRigid with
    ⟨hKClutter, hKCard, hKRows, hKMax, hKRowsUpper,
      hBKRows, hBKUpper, hPairUpper, hASideCard, hBSideCard,
      hCover, hDisjoint, hABPair, hPairRowsEq, hPairRowsCard,
      hASideAvoid, hBSideAvoid, hACenter, hBCenter,
      hcCommon, hdCommon, hcNeD, hcUnique, hdUnique⟩
  have hASideEq : aSide = avoidPoint K b := by
    ext R
    constructor
    · intro hRA
      exact mem_avoidPoint.mpr
        ⟨(mem_pointSupport.mp hRA).1, hASideAvoid R hRA⟩
    · intro hRAvoid
      obtain ⟨hRK, hbR⟩ := mem_avoidPoint.mp hRAvoid
      have hUnion : R ∈ aSide ∪ bSide := by
        rw [hCover]
        exact hRK
      rcases Finset.mem_union.mp hUnion with hRA | hRB
      · exact hRA
      · exact (hbR (mem_pointSupport.mp hRB).2).elim
  have hBSideEq : bSide = avoidPoint K a := by
    ext R
    constructor
    · intro hRB
      exact mem_avoidPoint.mpr
        ⟨(mem_pointSupport.mp hRB).1, hBSideAvoid R hRB⟩
    · intro hRAvoid
      obtain ⟨hRK, haR⟩ := mem_avoidPoint.mp hRAvoid
      have hUnion : R ∈ aSide ∪ bSide := by
        rw [hCover]
        exact hRK
      rcases Finset.mem_union.mp hUnion with hRA | hRB
      · exact (haR (mem_pointSupport.mp hRA).2).elim
      · exact hRB
  have hASideClutter : IsClutter aSide := by
    intro R hRA S hSA hRS
    exact hKClutter (mem_pointSupport.mp hRA).1
      (mem_pointSupport.mp hSA).1 hRS
  have hBSideClutter : IsClutter bSide := by
    intro R hRB S hSB hRS
    exact hKClutter (mem_pointSupport.mp hRB).1
      (mem_pointSupport.mp hSB).1 hRS
  have hASideRows : RowsCardAtLeast aSide 4 := by
    intro R hRA
    exact hKRows R (mem_pointSupport.mp hRA).1
  have hBSideRows : RowsCardAtLeast bSide 4 := by
    intro R hRB
    exact hKRows R (mem_pointSupport.mp hRB).1
  have hASideRowsUpper : ∀ R ∈ aSide, R.card ≤ 7 := by
    intro R hRA
    exact hKRowsUpper R (mem_pointSupport.mp hRA).1
  have hBSideRowsUpper : ∀ R ∈ bSide, R.card ≤ 7 := by
    intro R hRB
    exact hKRowsUpper R (mem_pointSupport.mp hRB).1
  have hAFirstData :
      IsClutter aCentered ∧ aCentered.card = 3 ∧
        RowsCardAtLeast aCentered 3 ∧
        ∀ R ∈ aCentered, R.card ≤ 6 := by
    simpa [aCentered] using threeRow_delete_center_data
      hASideClutter hASideCard hASideRows hASideRowsUpper hACenter
  have hBFirstData :
      IsClutter bCentered ∧ bCentered.card = 3 ∧
        RowsCardAtLeast bCentered 3 ∧
        ∀ R ∈ bCentered, R.card ≤ 6 := by
    simpa [bCentered] using threeRow_delete_center_data
      hBSideClutter hBSideCard hBSideRows hBSideRowsUpper hBCenter
  rcases hAFirstData with
    ⟨hACenteredClutter, hACenteredCard, hACenteredRows,
      hACenteredUpper⟩
  rcases hBFirstData with
    ⟨hBCenteredClutter, hBCenteredCard, hBCenteredRows,
      hBCenteredUpper⟩
  have hAResidualData :
      IsClutter aResidual ∧ aResidual.card = 3 ∧
        RowsCardAtLeast aResidual 2 ∧
        (∀ R ∈ aResidual, R.card ≤ 5) ∧
        ∀ point, ∃ R ∈ aResidual, point ∉ R := by
    simpa [aResidual] using threeRow_delete_unique_common_data
      hACenteredClutter hACenteredCard hACenteredRows hACenteredUpper
      hcCommon hcUnique
  have hBResidualData :
      IsClutter bResidual ∧ bResidual.card = 3 ∧
        RowsCardAtLeast bResidual 2 ∧
        (∀ R ∈ bResidual, R.card ≤ 5) ∧
        ∀ point, ∃ R ∈ bResidual, point ∉ R := by
    simpa [bResidual] using threeRow_delete_unique_common_data
      hBCenteredClutter hBCenteredCard hBCenteredRows hBCenteredUpper
      hdCommon hdUnique
  rcases hAResidualData with
    ⟨hAResidualClutter, hAResidualCard, hAResidualRows,
      hAResidualUpper, hAResidualNoCommon⟩
  rcases hBResidualData with
    ⟨hBResidualClutter, hBResidualCard, hBResidualRows,
      hBResidualUpper, hBResidualNoCommon⟩
  have hASideNonempty : aSide.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < aSide.card)
  have hBSideNonempty : bSide.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < bSide.card)
  obtain ⟨hcNeA, hcNeB, _hBCPair⟩ := threeSide_common_pairRow
    hASideNonempty hCover hASideAvoid hBCenter hcCommon hBKRows
  have hReverseCover : bSide ∪ aSide = K := by
    simpa [Finset.union_comm] using hCover
  obtain ⟨hdNeB, hdNeA, _hADPair⟩ := threeSide_common_pairRow
    hBSideNonempty hReverseCover hBSideAvoid hACenter hdCommon hBKRows
  have hAPairHit :
      ∀ Q ∈ pairRows (blocker K), a ∈ Q ∨ c ∈ Q := by
    intro Q hQ
    rw [hPairRowsEq] at hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
  have hBPairHit :
      ∀ Q ∈ pairRows (blocker K), b ∈ Q ∨ d ∈ Q := by
    intro Q hQ
    rw [hPairRowsEq] at hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have hABlockerAdd :
      (blocker aResidual).card + (pairRows (blocker K)).card ≤
        (blocker K).card := by
    simpa [aResidual, aCentered] using
      doubleDelete_blocker_add_pairRows_le hASideEq hab hcNeB hAPairHit
  have hBBlockerAdd :
      (blocker bResidual).card + (pairRows (blocker K)).card ≤
        (blocker K).card := by
    simpa [bResidual, bCentered] using
      doubleDelete_blocker_add_pairRows_le hBSideEq hab.symm hdNeA hBPairHit
  have hABlockerUpper : (blocker aResidual).card ≤ 4 := by omega
  have hBBlockerUpper : (blocker bResidual).card ≤ 4 := by omega
  refine ⟨x, a, b, c, d, hxa, hxb, hab, hTForm, ?_⟩
  exact ⟨hKClutter, hKCard, hKRows, hKMax, hBKRows, hBKUpper,
    hASideCard, hBSideCard, hCover, hDisjoint, hASideEq, hBSideEq,
    hACenter, hBCenter, hcCommon, hdCommon, hPairRowsEq, hPairRowsCard,
    hcNeA, hcNeB, hdNeA, hdNeB, hcNeD,
    hAResidualClutter, hAResidualCard, hAResidualRows,
    hAResidualUpper, hAResidualNoCommon, hABlockerUpper,
    hBResidualClutter, hBResidualCard, hBResidualRows,
    hBResidualUpper, hBResidualNoCommon, hBBlockerUpper⟩

end AiMathLab.P0054.MiddleSevenNineSixResidualSound
