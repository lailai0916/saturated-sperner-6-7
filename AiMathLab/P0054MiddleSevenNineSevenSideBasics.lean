import AiMathLab.P0054MiddleSevenNineDegree

/-!
# Structural reductions for a three-row on the seven-row side

The finite five-row and six-row certificates are kept out of this file.  We
record only the arbitrary-finite reductions which feed those certificates.
-/

namespace AiMathLab.P0054.MiddleSevenNineSevenSideBasics

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

set_option maxHeartbeats 1000000 in
-- The private-row construction needs more than the default elaboration budget.
theorem fiveRow_maxDegreeAtMost_three_of_rowsFour_pairUpperThree
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha}
    (hKCard : K.card = 5)
    (hKRows : RowsCardAtLeast K 4)
    (hKMaxFour : MaxDegreeAtMost K 4)
    (hPairUpper : (pairRows (blocker K)).card ≤ 3) :
    MaxDegreeAtMost K 3 := by
  classical
  intro y
  by_contra hNot
  have hyUpper := hKMaxFour y
  have hyDegree : degree K y = 4 := by omega
  have hAvoidCard : (avoidPoint K y).card = 1 := by
    have hPartition := card_avoidPoint_add_degree K y
    omega
  obtain ⟨R, hAvoid⟩ := Finset.card_eq_one.mp hAvoidCard
  have hRAvoid : R ∈ avoidPoint K y := by simp [hAvoid]
  have hRK : R ∈ K := (mem_avoidPoint.mp hRAvoid).1
  have hyR : y ∉ R := (mem_avoidPoint.mp hRAvoid).2
  have hRCard : 4 ≤ R.card := hKRows R hRK
  let pairs : G413.Hypergraph alpha :=
    R.image fun z ↦ ({y, z} : Row alpha)
  have hPairsSubset : pairs ⊆ pairRows (blocker K) := by
    intro pair hPair
    obtain ⟨z, hzR, rfl⟩ := Finset.mem_image.mp hPair
    have hzy : z ≠ y := by
      intro hzy
      exact hyR (hzy ▸ hzR)
    have hyz : y ≠ z := hzy.symm
    have hYPrivate : ∃ S ∈ K, y ∈ S ∧ z ∉ S := by
      by_contra hNoPrivate
      have hzOfY : ∀ S ∈ K, y ∈ S → z ∈ S := by
        intro S hSK hyS
        by_contra hzS
        exact hNoPrivate ⟨S, hSK, hyS, hzS⟩
      have hzAll : ∀ S ∈ K, z ∈ S := by
        intro S hSK
        by_cases hyS : y ∈ S
        · exact hzOfY S hSK hyS
        · have hSAvoid : S ∈ avoidPoint K y :=
            mem_avoidPoint.mpr ⟨hSK, hyS⟩
          have hSR : S = R := by simpa [hAvoid] using hSAvoid
          exact hSR ▸ hzR
      have hFilter : K.filter (fun S ↦ z ∈ S) = K :=
        Finset.filter_eq_self.mpr hzAll
      have hzDegree : degree K z = 5 := by
        rw [degree, hFilter, hKCard]
      have hzUpper := hKMaxFour z
      omega
    obtain ⟨S, hSK, hyS, hzS⟩ := hYPrivate
    have hTransversal : IsTransversal K ({y, z} : Row alpha) := by
      intro A hAK
      by_cases hyA : y ∈ A
      · exact ⟨y, by simp, hyA⟩
      · have hAAvoid : A ∈ avoidPoint K y :=
          mem_avoidPoint.mpr ⟨hAK, hyA⟩
        have hAR : A = R := by simpa [hAvoid] using hAAvoid
        exact ⟨z, by simp, hAR ▸ hzR⟩
    have hMinimal : IsMinimalTransversal K ({y, z} : Row alpha) := by
      apply hTransversal.minimal_of_privateRows
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · refine ⟨S, hSK, by simp, hyS, ?_⟩
        intro w hwPair hwS
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
        rcases hwPair with rfl | rfl
        · rfl
        · exact (hzS hwS).elim
      · refine ⟨R, hRK, by simp, hzR, ?_⟩
        intro w hwPair hwR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
        rcases hwPair with rfl | rfl
        · exact (hyR hwR).elim
        · rfl
    exact Finset.mem_filter.mpr
      ⟨mem_blocker.mpr hMinimal, by simp [hyz]⟩
  have hPairMapInj : Set.InjOn
      (fun z ↦ ({y, z} : Row alpha)) (↑R : Set alpha) := by
    intro z hzR' w hwR hEq
    have hzy : z ≠ y := by
      intro hzy
      exact hyR (hzy ▸ hzR')
    change ({y, z} : Row alpha) = ({y, w} : Row alpha) at hEq
    have hzLeft : z ∈ ({y, z} : Row alpha) := by simp
    have hzRight : z ∈ ({y, w} : Row alpha) := hEq ▸ hzLeft
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzRight
    exact hzRight.resolve_left hzy
  have hPairsCard : pairs.card = R.card := by
    exact Finset.card_image_iff.mpr hPairMapInj
  have hCardUpper := Finset.card_le_card hPairsSubset
  rw [hPairsCard] at hCardUpper
  omega

set_option maxHeartbeats 1000000 in
-- The nested blocker reductions need more than the default elaboration budget.
theorem degreeFour_fiveKernel_data
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha}
    (hEClutter : IsClutter E)
    (hECard : E.card = 9)
    (hERows : RowsCardAtLeast E 4)
    (hEMax : MaxDegreeAtMost E 4)
    (hDualCard : (blocker E).card = 7)
    (hDualRows : RowsCardAtLeast (blocker E) 3)
    (hDualMax : MaxDegreeAtMost (blocker E) 3)
    {x : alpha} (hxDegree : degree E x = 4) :
    let K := avoidPoint E x
    IsClutter K ∧ K.card = 5 ∧ RowsCardAtLeast K 4 ∧
      (∀ R ∈ K, R.card ≤ 7) ∧
      RowsCardAtLeast (blocker K) 2 ∧ MaxDegreeAtMost K 3 ∧
      (blocker K).card ≤ 7 ∧ (pairRows (blocker K)).card ≤ 3 := by
  let K := avoidPoint E x
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hEClutter x
  have hKCard : K.card = 5 := by
    have hPartition := card_avoidPoint_add_degree E x
    simpa [K, hECard, hxDegree] using hPartition
  have hKRows : RowsCardAtLeast K 4 := by
    intro R hRK
    exact hERows R (mem_avoidPoint.mp (by simpa [K] using hRK)).1
  have hKUpper : ∀ R ∈ K, R.card ≤ 7 := by
    intro R hRK
    have hRE : R ∈ E :=
      (mem_avoidPoint.mp (by simpa [K] using hRK)).1
    have hRDouble : R ∈ blocker (blocker E) := by
      simpa [blocker_involution hEClutter] using hRE
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hRDouble)).trans_eq hDualCard
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
  have hKMaxFour : MaxDegreeAtMost K 4 := by
    intro y
    apply (degree_mono (H := K) (K := E) ?_ y).trans (hEMax y)
    intro R hRK
    exact (mem_avoidPoint.mp (by simpa [K] using hRK)).1
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker E) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hDualRows x
      _ ≤ 3 := hDualMax x
  have hKMax : MaxDegreeAtMost K 3 :=
    fiveRow_maxDegreeAtMost_three_of_rowsFour_pairUpperThree
      hKCard hKRows hKMaxFour hPairUpper
  have hBKUpper : (blocker K).card ≤ 7 := by
    have hLift := blocker_avoidPoint_card_le_blocker E x
    simpa [K, hDualCard] using hLift
  exact ⟨hKClutter, hKCard, hKRows, hKUpper, hBKRows, hKMax,
    hBKUpper, hPairUpper⟩

end AiMathLab.P0054.MiddleSevenNineSevenSideBasics
