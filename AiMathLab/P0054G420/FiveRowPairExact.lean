import AiMathLab.P0054G420.MiddleEightEight
import AiMathLab.P0054G416.SupportMultigraphLift
import AiMathLab.P0054G413.ResidualBounds

namespace AiMathLab.P0054.G420

open G413 G419

theorem blocker_rows_cardAtLeast_two_of_fiveRow_maxDegree_three
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha}
    (hKCard : K.card = 5)
    (hMaxDegree : MaxDegreeAtMost K 3) :
    RowsCardAtLeast (blocker K) 2 := by
  classical
  intro T hT
  have hTTransversal := (mem_blocker.mp hT).prop
  have hKNonempty : K.Nonempty := Finset.card_pos.mp (by omega)
  have hTPositive : 0 < T.card := by
    by_contra hNot
    have hTEmpty : T = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨E, hEK⟩ := hKNonempty
    obtain ⟨y, hyT, -⟩ := hTTransversal E hEK
    simp [hTEmpty] at hyT
  by_contra hNot
  have hTCard : T.card = 1 := by omega
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hTCard
  have hAll : ∀ E ∈ K, y ∈ E := by
    intro E hEK
    obtain ⟨z, hz, hzE⟩ := hTTransversal E hEK
    have hzy : z = y := by simpa using hz
    simpa [hzy] using hzE
  have hDegree : degree K y = 5 := by
    rw [degree]
    have hFilter : K.filter (fun E ↦ y ∈ E) = K :=
      Finset.filter_eq_self.mpr hAll
    rw [hFilter, hKCard]
  have hUpper := hMaxDegree y
  omega

theorem commonPoint_pair_mem_blocker
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hAvoid : avoidPoint K x = {P, Q})
    {y : alpha} (hy : y ∈ P ∩ Q) :
    ({x, y} : G413.Row alpha) ∈ pairRows (blocker K) := by
  classical
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
  have hxy : x ≠ y := fun hxy ↦ hxP (hxy ▸ hyP)
  have hSingletonSource : ({y} : G413.Row alpha) ∈
      blocker (avoidPoint K x) := by
    rw [hAvoid, blocker_pairFamily]
    exact mem_twoRowBlockers.mpr (Or.inl ⟨y, hy, rfl⟩)
  have hNotTransversal : ¬IsTransversal K ({y} : G413.Row alpha) := by
    intro hTransversal
    have hAll : ∀ E ∈ K, y ∈ E := by
      intro E hEK
      obtain ⟨z, hz, hzE⟩ := hTransversal E hEK
      have hzy : z = y := by simpa using hz
      simpa [hzy] using hzE
    have hDegree : degree K y = 5 := by
      rw [degree]
      have hFilter : K.filter (fun E ↦ y ∈ E) = K :=
        Finset.filter_eq_self.mpr hAll
      rw [hFilter, hKCard]
    have hUpper := hMaxDegree y
    omega
  have hLiftMember := avoidBlockerLift_mem_blocker hSingletonSource
  have hLiftEq : avoidBlockerLift K x {y} = ({x, y} : G413.Row alpha) := by
    simp [avoidBlockerLift, hNotTransversal]
  rw [hLiftEq] at hLiftMember
  exact Finset.mem_filter.mpr ⟨hLiftMember, by simp [hxy]⟩

theorem commonPairRows_card_le
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hAvoid : avoidPoint K x = {P, Q}) :
    (P ∩ Q).card ≤ (pairRows (blocker K)).card := by
  classical
  let commonPairs := (P ∩ Q).image fun y ↦ ({x, y} : G413.Row alpha)
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hInjective : Set.InjOn (fun y ↦ ({x, y} : G413.Row alpha))
      (↑(P ∩ Q) : Set alpha) := by
    intro y hy z hz hEq
    have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
    have hyx : y ≠ x := fun hyx ↦ hxP (hyx ▸ hyP)
    change ({x, y} : G413.Row alpha) = {x, z} at hEq
    have hyMem : y ∈ ({x, z} : G413.Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    rcases hyMem with hyx' | hyz
    · exact (hyx hyx').elim
    · exact hyz
  have hSubset : commonPairs ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hE
    exact commonPoint_pair_mem_blocker hKCard hMaxDegree hAvoid hy
  calc
    (P ∩ Q).card = commonPairs.card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (pairRows (blocker K)).card := Finset.card_le_card hSubset

theorem twoRow_blocker_card_ge_inter_add_sdiff_product
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (P Q : G413.Row alpha) :
    (P ∩ Q).card + (P \ Q).card * (Q \ P).card ≤
      (blocker ({P, Q} : G413.Hypergraph alpha)).card := by
  classical
  rw [blocker_pairFamily]
  unfold twoRowBlockers
  have hSingletonCard : (singletonRows (P ∩ Q)).card = (P ∩ Q).card := by
    unfold singletonRows
    rw [Finset.card_image_iff.mpr]
    intro x _ y _ hEq
    simpa using hEq
  have hDisjointDiff : Disjoint (P \ Q) (Q \ P) := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_sdiff.mp hxQ).1
  have hCrossLower : (P \ Q).card * (Q \ P).card ≤
      (crossPairRows (P \ Q) (Q \ P)).card :=
    card_mul_le_crossPairRows_card_of_disjoint hDisjointDiff
  have hFamiliesDisjoint :
      Disjoint (singletonRows (P ∩ Q))
        (crossPairRows (P \ Q) (Q \ P)) := by
    apply Finset.disjoint_left.mpr
    intro E hSingleton hCross
    obtain ⟨y, -, hyE⟩ := mem_singletonRows.mp hSingleton
    obtain ⟨p, hp, q, hq, hpqE⟩ := mem_crossPairRows.mp hCross
    have hpq : p ≠ q := by
      intro hpq
      exact (Finset.mem_sdiff.mp hp).2
        (hpq ▸ (Finset.mem_sdiff.mp hq).1)
    have hCardEq := congrArg Finset.card (hyE.trans hpqE.symm)
    simp [hpq] at hCardEq
  rw [Finset.card_union_of_disjoint hFamiliesDisjoint, hSingletonCard]
  omega

theorem twoAvoidingRows_source_add_common_le_degree_add_pairs
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hAvoid : avoidPoint K x = {P, Q}) :
    (blocker (avoidPoint K x)).card + (P ∩ Q).card ≤
      degree (blocker K) x + (pairRows (blocker K)).card := by
  classical
  let source := blocker (avoidPoint K x)
  let lifts := source.image (avoidBlockerLift K x)
  let commonPairs := (P ∩ Q).image fun y ↦ ({x, y} : G413.Row alpha)
  have hBRows : RowsCardAtLeast (blocker K) 2 :=
    blocker_rows_cardAtLeast_two_of_fiveRow_maxDegree_three hKCard hMaxDegree
  have hLiftSubset : lifts ⊆ blocker K := by
    intro E hE
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hE
    exact avoidBlockerLift_mem_blocker (by simpa [source] using hT)
  have hLiftCard : lifts.card = source.card := by
    exact Finset.card_image_iff.mpr
      ((avoidBlockerLift_injective K x).mono (by
        simpa [source] using (Set.Subset.rfl :
          (↑source : Set (G413.Row alpha)) ⊆ ↑source)))
  have hAvoidLiftsPair : avoidPoint lifts x ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨hELifts, hxE⟩ := mem_avoidPoint.mp hE
    obtain ⟨T, hTSource, hLiftEq⟩ := Finset.mem_image.mp hELifts
    have hTSource' : T ∈ blocker (avoidPoint K x) := by
      simpa [source] using hTSource
    have hEMember : E ∈ blocker K := hLiftSubset hELifts
    have hTUpper : T.card ≤ 2 := by
      have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hTSource')
      rw [hAvoid] at hUpper
      exact hUpper.trans Finset.card_le_two
    have hErase : E.erase x = T := by
      rw [← hLiftEq]
      exact avoidBlockerLift_erase K x hTSource'
    have hECard : E.card = 2 := by
      have hCardEq := congrArg Finset.card hErase
      rw [Finset.erase_eq_of_notMem hxE] at hCardEq
      have hLower := hBRows E hEMember
      omega
    exact Finset.mem_filter.mpr ⟨hEMember, hECard⟩
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hCommonInjective : Set.InjOn
      (fun y ↦ ({x, y} : G413.Row alpha)) (↑(P ∩ Q) : Set alpha) := by
    intro y hy z _ hEq
    have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
    have hyx : y ≠ x := fun hyx ↦ hxP (hyx ▸ hyP)
    change ({x, y} : G413.Row alpha) = {x, z} at hEq
    have hyMem : y ∈ ({x, z} : G413.Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    exact hyMem.resolve_left hyx
  have hCommonCard : commonPairs.card = (P ∩ Q).card := by
    exact Finset.card_image_iff.mpr hCommonInjective
  have hCommonSubset : commonPairs ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hE
    exact commonPoint_pair_mem_blocker hKCard hMaxDegree hAvoid hy
  have hDisjoint : Disjoint (avoidPoint lifts x) commonPairs := by
    apply Finset.disjoint_left.mpr
    intro E hEAvoid hECommon
    have hxE : x ∉ E := (mem_avoidPoint.mp hEAvoid).2
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hECommon
    exact hxE (by simp)
  have hPairUnionSubset : avoidPoint lifts x ∪ commonPairs ⊆
      pairRows (blocker K) :=
    Finset.union_subset hAvoidLiftsPair hCommonSubset
  have hPairCount := Finset.card_le_card hPairUnionSubset
  rw [Finset.card_union_of_disjoint hDisjoint, hCommonCard] at hPairCount
  have hDegreeLift : degree lifts x ≤ degree (blocker K) x :=
    degree_mono hLiftSubset x
  have hLiftPartition := card_avoidPoint_add_degree lifts x
  rw [hLiftCard] at hLiftPartition
  simpa [source] using (show
    source.card + (P ∩ Q).card ≤
      degree (blocker K) x + (pairRows (blocker K)).card by omega)

theorem avoidBlocker_card_ge_two_of_two_avoidingRows
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKRows : RowsCardAtLeast K 3)
    (hAvoid : avoidPoint K x = {P, Q}) :
    2 ≤ (avoidPoint (blocker K) x).card := by
  classical
  let R := residual K x
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter K x
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hKRows x
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hPK : P ∈ K := (mem_avoidPoint.mp hPAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hPDelete : P ∈ deletePoint K x := by
    exact Finset.mem_image.mpr ⟨P, hPK, by simp [hxP]⟩
  obtain ⟨M, hMMinimize, -⟩ := exists_minimize_subset hPDelete
  have hRNonempty : R.Nonempty := by
    refine ⟨M, ?_⟩
    change M ∈ minimize (deletePoint K x)
    exact hMMinimize
  have hLower : 2 ≤ (blocker R).card :=
    blocker_card_ge_two_of_rows_cardAtLeast_two hRClutter hRNonempty hRRows
  simpa [R, blocker_residual] using hLower

theorem avoidBlocker_card_ge_six_of_two_commonPoints
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} {x : alpha} {P Q : G413.Row alpha}
    (hKCard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hMaxDegree : MaxDegreeAtMost K 3)
    (hDegree : degree K x = 3)
    (hPairUpper : (pairRows (blocker K)).card ≤ 2)
    (hAvoid : avoidPoint K x = {P, Q})
    (hCommonCard : (P ∩ Q).card = 2) :
    6 ≤ (avoidPoint (blocker K) x).card := by
  classical
  let R := residual K x
  let commonPairs := (P ∩ Q).image fun y ↦ ({x, y} : G413.Row alpha)
  have hBRows : RowsCardAtLeast (blocker K) 2 :=
    blocker_rows_cardAtLeast_two_of_fiveRow_maxDegree_three hKCard hMaxDegree
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hCommonInjective : Set.InjOn
      (fun y ↦ ({x, y} : G413.Row alpha)) (↑(P ∩ Q) : Set alpha) := by
    intro y hy z _ hEq
    have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
    have hyx : y ≠ x := fun hyx ↦ hxP (hyx ▸ hyP)
    change ({x, y} : G413.Row alpha) = {x, z} at hEq
    have hyMem : y ∈ ({x, z} : G413.Row alpha) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    exact hyMem.resolve_left hyx
  have hCommonPairsCard : commonPairs.card = 2 := by
    rw [Finset.card_image_iff.mpr hCommonInjective, hCommonCard]
  have hCommonSubset : commonPairs ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hE
    exact commonPoint_pair_mem_blocker hKCard hMaxDegree hAvoid hy
  have hPairCard : (pairRows (blocker K)).card = 2 := by
    have hLower := Finset.card_le_card hCommonSubset
    omega
  have hCommonEq : commonPairs = pairRows (blocker K) := by
    apply Finset.eq_of_subset_of_card_le hCommonSubset
    rw [hCommonPairsCard, hPairCard]
  have hAvoidRows : RowsCardAtLeast (avoidPoint (blocker K) x) 3 := by
    intro E hE
    obtain ⟨hEBlocker, hxE⟩ := mem_avoidPoint.mp hE
    have hLower := hBRows E hEBlocker
    by_contra hNot
    have hECard : E.card = 2 := by omega
    have hEPair : E ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hEBlocker, hECard⟩
    have hECommon : E ∈ commonPairs := by rw [hCommonEq]; exact hEPair
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hECommon
    exact hxE (by simp)
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter K x
  have hRUpper : R.card ≤ 5 := by
    exact (residual_card_le K x).trans_eq hKCard
  have hRRows : RowsCardAtLeast R 2 := by
    simpa [R] using residual_rows_cardAtLeast hKRows x
  have hRPairs : (pairRows R).card ≤ 3 := by
    exact (pairRows_residual_card_le_degree hKRows x).trans_eq hDegree
  have hBlockerRRows : RowsCardAtLeast (blocker R) 3 := by
    simpa [R, blocker_residual] using hAvoidRows
  have hRRowsNonempty : RowsNonempty R := by
    intro E hE
    exact Finset.card_pos.mp (by have := hRRows E hE; omega)
  obtain ⟨T, hTBlocker⟩ := blocker_nonempty hRRowsNonempty
  have hRLower : 3 ≤ R.card := by
    have hTLower := hBlockerRRows T hTBlocker
    have hTUpper := minimalTransversal_card_le_rows (mem_blocker.mp hTBlocker)
    omega
  have hSix := residualLemma2 R hRClutter hRLower hRUpper hRRows hRPairs
    hBlockerRRows
  simpa [R, blocker_residual] using hSix

end AiMathLab.P0054.G420
