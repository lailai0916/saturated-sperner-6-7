import AiMathLab.P0054G413.ResidualBounds
import AiMathLab.P0054G413.ThreeRowExact

namespace AiMathLab.P0054.G413

theorem pairSide_pairRows_card_le_of_endpoint_degree_le_two {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hHRows : RowsCardAtLeast H 2)
    (hPair : ({p, q} : Row α) ∈ H)
    (hDegree : degree H q ≤ 2) :
    (pairRows (pairSide H p q)).card ≤ (pairRows H).card := by
  classical
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hPairCard := hHRows {p} (by simpa using hPair)
    simp at hPairCard
  have exists_source {E : Row α} (hE : E ∈ pairRows (pairSide H p q)) :
      ∃ A ∈ avoidPoint H p, A.erase q = E := by
    have hESide : E ∈ pairSide H p q := (Finset.mem_filter.mp hE).1
    have hEDelete : E ∈ deletePoint (avoidPoint H p) q :=
      minimize_subset _ hESide
    exact Finset.mem_image.mp hEDelete
  let source : Row α → Row α := fun E ↦
    if hE : E ∈ pairRows (pairSide H p q) then
      Classical.choose (exists_source hE)
    else ∅
  have source_spec {E : Row α} (hE : E ∈ pairRows (pairSide H p q)) :
      source E ∈ avoidPoint H p ∧ (source E).erase q = E := by
    simp only [source, dif_pos hE]
    exact Classical.choose_spec (exists_source hE)
  let target : Row α → Row α := fun E ↦
    if q ∈ source E then {p, q} else source E
  have target_mem {E : Row α} (hE : E ∈ pairRows (pairSide H p q)) :
      target E ∈ pairRows H := by
    obtain ⟨hSourceAvoid, hSourceErase⟩ := source_spec hE
    obtain ⟨hSourceH, -⟩ := mem_avoidPoint.mp hSourceAvoid
    rw [pairRows, Finset.mem_filter]
    by_cases hqSource : q ∈ source E
    · simpa [target, hqSource, hpq] using hPair
    · have hSourceEq : source E = E := by
        calc
          source E = (source E).erase q :=
            (Finset.erase_eq_of_notMem hqSource).symm
          _ = E := hSourceErase
      have hTargetEq : target E = source E := by simp [target, hqSource]
      exact ⟨by simpa [hTargetEq] using hSourceH,
        by simpa [hTargetEq, hSourceEq] using (Finset.mem_filter.mp hE).2⟩
  apply Finset.card_le_card_of_injOn target
  · intro E hE
    exact target_mem hE
  · intro E hE F hF hTarget
    obtain ⟨hEAvoid, hEErase⟩ := source_spec hE
    obtain ⟨hFAvoid, hFErase⟩ := source_spec hF
    obtain ⟨hEH, hpE⟩ := mem_avoidPoint.mp hEAvoid
    obtain ⟨hFH, hpF⟩ := mem_avoidPoint.mp hFAvoid
    by_cases hqE : q ∈ source E
    · by_cases hqF : q ∈ source F
      · have hSourceEq : source E = source F := by
          by_contra hne
          have hPairNeE : ({p, q} : Row α) ≠ source E := by
            intro hEq
            exact hpE (hEq ▸ by simp)
          have hPairNeF : ({p, q} : Row α) ≠ source F := by
            intro hEq
            exact hpF (hEq ▸ by simp)
          have hThreeCard :
              ({{p, q}, source E, source F} : Hypergraph α).card = 3 := by
            simp [hPairNeE, hPairNeF, hne]
          have hThreeSubset :
              ({{p, q}, source E, source F} : Hypergraph α) ⊆
                H.filter (fun A ↦ q ∈ A) := by
            intro A hA
            simp only [Finset.mem_insert, Finset.mem_singleton] at hA
            rcases hA with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hPair, by simp⟩
            · exact Finset.mem_filter.mpr ⟨hEH, hqE⟩
            · exact Finset.mem_filter.mpr ⟨hFH, hqF⟩
          have hThreeDegree : 3 ≤ degree H q := by
            rw [degree]
            simpa [hThreeCard] using Finset.card_le_card hThreeSubset
          omega
        calc
          E = (source E).erase q := hEErase.symm
          _ = (source F).erase q := by rw [hSourceEq]
          _ = F := hFErase
      · have hpTarget : p ∈ target F := by
          rw [← hTarget]
          simp [target, hqE]
        exact (hpF (by simpa [target, hqF] using hpTarget)).elim
    · by_cases hqF : q ∈ source F
      · have hpTarget : p ∈ target E := by
          rw [hTarget]
          simp [target, hqF]
        exact (hpE (by simpa [target, hqE] using hpTarget)).elim
      · have hSourceEq : source E = source F := by
          simpa [target, hqE, hqF] using hTarget
        calc
          E = (source E).erase q := hEErase.symm
          _ = (source F).erase q := by rw [hSourceEq]
          _ = F := hFErase

theorem exists_endpoint_pair_of_pairSide_blocker_card_eq_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hDegree : degree H q ≤ 2)
    (hBRows : RowsCardAtLeast (blocker (pairSide H p q)) 2)
    (hBcard : (blocker (pairSide H p q)).card = 2) :
    ∃ w, ({w} : Row α) ∈ pairSide H p q ∧
      ({q, w} : Row α) ∈ H ∧ p ∉ ({q, w} : Row α) := by
  classical
  let L := pairSide H p q
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker L := by simpa [L, hBQ]
  have hQ₂b : Q₂ ∈ blocker L := by simpa [L, hBQ]
  have hQ₁card : 2 ≤ Q₁.card := by simpa [L] using hBRows Q₁ hQ₁b
  have hQ₂card : 2 ≤ Q₂.card := by simpa [L] using hBRows Q₂ hQ₂b
  have hLtwo : L = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair
      (H := L) (by simpa [L, pairSide] using residual_isClutter (avoidPoint H p) q) hBQ
  have hInter : (Q₁ ∩ Q₂).Nonempty := by
    by_contra hnot
    have hDisjoint : Disjoint Q₁ Q₂ := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hnot
    have hCrossSubset : crossPairRows Q₁ Q₂ ⊆ pairRows L := by
      intro E hE
      obtain ⟨a, haQ₁, b, hbQ₂, rfl⟩ := mem_crossPairRows.mp hE
      have hab : a ≠ b := fun hab ↦
        Finset.disjoint_left.mp hDisjoint haQ₁ (hab ▸ hbQ₂)
      exact Finset.mem_filter.mpr ⟨by
        rw [hLtwo, twoRowBlockers,
          Finset.sdiff_eq_self_of_disjoint hDisjoint,
          Finset.sdiff_eq_self_of_disjoint hDisjoint.symm]
        exact Finset.mem_union_right _ hE, by simp [hab]⟩
    have hCrossLower : 4 ≤ (crossPairRows Q₁ Q₂).card := by
      calc
        4 = 2 * 2 := rfl
        _ ≤ Q₁.card * Q₂.card := Nat.mul_le_mul hQ₁card hQ₂card
        _ ≤ (crossPairRows Q₁ Q₂).card :=
          card_mul_le_crossPairRows_card_of_disjoint hDisjoint
    have hPairSideUpper : (pairRows L).card ≤ 3 := by
      calc
        (pairRows L).card ≤ (pairRows H).card := by
          simpa [L] using
            pairSide_pairRows_card_le_of_endpoint_degree_le_two
              hHRows hPair hDegree
        _ ≤ 3 := hPairRows
    have hCrossUpper := Finset.card_le_card hCrossSubset
    omega
  obtain ⟨w, hwInter⟩ := hInter
  have hSingletonL : ({w} : Row α) ∈ L := by
    rw [hLtwo]
    exact mem_twoRowBlockers.mpr (Or.inl ⟨w, hwInter, rfl⟩)
  have hSingletonDelete :
      ({w} : Row α) ∈ deletePoint (avoidPoint H p) q :=
    minimize_subset _ hSingletonL
  obtain ⟨A, hAAvoid, hAErase⟩ := Finset.mem_image.mp hSingletonDelete
  obtain ⟨hAH, -⟩ := mem_avoidPoint.mp hAAvoid
  have hqA : q ∈ A := by
    by_contra hqA
    have hAeq : A = {w} := by
      calc
        A = A.erase q := (Finset.erase_eq_of_notMem hqA).symm
        _ = {w} := hAErase
    have hAcard := hHRows A hAH
    simp [hAeq] at hAcard
  have hAeq : A = {q, w} := by
    calc
      A = insert q (A.erase q) := (Finset.insert_erase hqA).symm
      _ = {q, w} := by rw [hAErase]
  exact ⟨w, by simpa [L] using hSingletonL, hAeq ▸ hAH,
    hAeq ▸ (mem_avoidPoint.mp hAAvoid).2⟩

theorem pairSide_singletonRows_card_le_one_of_endpoint_degree_le_two {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hHRows : RowsCardAtLeast H 2)
    (hPair : ({p, q} : Row α) ∈ H)
    (hDegree : degree H q ≤ 2) :
    (rowsCardAtMost (pairSide H p q) 1).card ≤ 1 := by
  classical
  by_contra hnot
  have hTwo : 2 ≤ (rowsCardAtMost (pairSide H p q) 1).card := by omega
  obtain ⟨U, hU, V, hV, hUV⟩ := Finset.one_lt_card.mp hTwo
  obtain ⟨hUSide, hUcard⟩ := mem_rowsCardAtMost.mp hU
  obtain ⟨hVSide, hVcard⟩ := mem_rowsCardAtMost.mp hV
  have hUDelete : U ∈ deletePoint (avoidPoint H p) q :=
    minimize_subset _ hUSide
  have hVDelete : V ∈ deletePoint (avoidPoint H p) q :=
    minimize_subset _ hVSide
  obtain ⟨A, hAAvoid, hAerase⟩ := Finset.mem_image.mp hUDelete
  obtain ⟨B, hBAvoid, hBerase⟩ := Finset.mem_image.mp hVDelete
  obtain ⟨hAH, hpA⟩ := mem_avoidPoint.mp hAAvoid
  obtain ⟨hBH, hpB⟩ := mem_avoidPoint.mp hBAvoid
  have hqA : q ∈ A := by
    by_contra hqA
    have hAeqU : A = U := by
      calc
        A = A.erase q := (Finset.erase_eq_of_notMem hqA).symm
        _ = U := hAerase
    have hAlarge := hHRows A hAH
    have hAupper : A.card ≤ 1 := by simpa [hAeqU] using hUcard
    omega
  have hqB : q ∈ B := by
    by_contra hqB
    have hBeqV : B = V := by
      calc
        B = B.erase q := (Finset.erase_eq_of_notMem hqB).symm
        _ = V := hBerase
    have hBlarge := hHRows B hBH
    have hBupper : B.card ≤ 1 := by simpa [hBeqV] using hVcard
    omega
  have hAB : A ≠ B := by
    intro hAB
    apply hUV
    calc
      U = A.erase q := hAerase.symm
      _ = B.erase q := by rw [hAB]
      _ = V := hBerase
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hPairCard := hHRows {p} (by simpa using hPair)
    simp at hPairCard
  have hPairA : ({p, q} : Row α) ≠ A := by
    intro hEq
    exact hpA (hEq ▸ by simp)
  have hPairB : ({p, q} : Row α) ≠ B := by
    intro hEq
    exact hpB (hEq ▸ by simp)
  have hThreeCard : ({{p, q}, A, B} : Hypergraph α).card = 3 := by
    simp [hPairA, hPairB, hAB]
  have hThreeSubset : ({{p, q}, A, B} : Hypergraph α) ⊆
      H.filter (fun E ↦ q ∈ E) := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hPair, by simp⟩
    · exact Finset.mem_filter.mpr ⟨hAH, hqA⟩
    · exact Finset.mem_filter.mpr ⟨hBH, hqB⟩
  have hThreeDegree : 3 ≤ degree H q := by
    rw [degree]
    simpa [hThreeCard] using Finset.card_le_card hThreeSubset
  omega

theorem pairSide_two_blocker_structure {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hDegree : degree H q ≤ 2)
    (hBRows : RowsCardAtLeast (blocker (pairSide H p q)) 2)
    (hBcard : (blocker (pairSide H p q)).card = 2) :
    ∃ w A,
      ({q, w} : Row α) ∈ H ∧ p ∉ ({q, w} : Row α) ∧
      A ∈ H ∧ A.card = 2 ∧ p ∉ A ∧ q ∉ A ∧
      ∀ E ∈ H, p ∉ E → q ∉ E → E = A ∨ w ∈ E := by
  classical
  let L := pairSide H p q
  obtain ⟨w, hSingletonL, hEndpointPair, hpEndpointPair⟩ :=
    exists_endpoint_pair_of_pairSide_blocker_card_eq_two
      hHRows hPairRows hPair hDegree hBRows hBcard
  obtain ⟨Q₁, Q₂, hQNe, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker L := by simpa [L, hBQ]
  have hQ₂b : Q₂ ∈ blocker L := by simpa [L, hBQ]
  have hLtwo : L = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair
      (H := L) (by simpa [L, pairSide] using residual_isClutter (avoidPoint H p) q) hBQ
  have hwInter : w ∈ Q₁ ∩ Q₂ := by
    have hSingletonTwo : ({w} : Row α) ∈ twoRowBlockers Q₁ Q₂ := by
      rw [← hLtwo]
      simpa [L] using hSingletonL
    rcases mem_twoRowBlockers.mp hSingletonTwo with hInter | hCross
    · obtain ⟨z, hzInter, hzEq⟩ := hInter
      have hzw : z = w := by simpa using hzEq
      simpa [hzw] using hzInter
    · obtain ⟨a, haQ₁, b, hbQ₂, hPairEq⟩ := hCross
      have hab : a ≠ b := fun hab ↦
        (Finset.mem_sdiff.mp haQ₁).2 (hab ▸ (Finset.mem_sdiff.mp hbQ₂).1)
      have hCardEq := congrArg Finset.card hPairEq
      simp [hab] at hCardEq
  have hInterEq : Q₁ ∩ Q₂ = {w} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hwInter, ?_⟩
    intro z hzInter
    have hzL : ({z} : Row α) ∈ L := by
      rw [hLtwo]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨z, hzInter, rfl⟩)
    have hSingletonUpper : (rowsCardAtMost L 1).card ≤ 1 := by
      simpa [L] using
        pairSide_singletonRows_card_le_one_of_endpoint_degree_le_two
          hHRows hPair hDegree
    have hwSmall : ({w} : Row α) ∈ rowsCardAtMost L 1 :=
      mem_rowsCardAtMost.mpr ⟨by simpa [L] using hSingletonL, by simp⟩
    have hzSmall : ({z} : Row α) ∈ rowsCardAtMost L 1 :=
      mem_rowsCardAtMost.mpr ⟨hzL, by simp⟩
    have hSingletonEq : ({z} : Row α) = {w} :=
      Finset.card_le_one.mp hSingletonUpper {z} hzSmall {w} hwSmall
    simpa using hSingletonEq
  have hQ₁notSubset : ¬ Q₁ ⊆ Q₂ := by
    intro hsub
    exact hQNe (blocker_isClutter L hQ₁b hQ₂b hsub)
  have hQ₂notSubset : ¬ Q₂ ⊆ Q₁ := by
    intro hsub
    exact hQNe.symm (blocker_isClutter L hQ₂b hQ₁b hsub)
  obtain ⟨a, haQ₁, haQ₂⟩ := Finset.not_subset.mp hQ₁notSubset
  obtain ⟨b, hbQ₂, hbQ₁⟩ := Finset.not_subset.mp hQ₂notSubset
  have hab : a ≠ b := fun hab ↦ haQ₂ (hab ▸ hbQ₂)
  let A : Row α := {a, b}
  have hACross : A ∈ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) := by
    exact mem_crossPairRows.mpr
      ⟨a, Finset.mem_sdiff.mpr ⟨haQ₁, haQ₂⟩,
        b, Finset.mem_sdiff.mpr ⟨hbQ₂, hbQ₁⟩, rfl⟩
  have cross_source {E : Row α}
      (hE : E ∈ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁)) : E ∈ pairRows H := by
    have hEL : E ∈ L := by
      rw [hLtwo]
      exact mem_twoRowBlockers.mpr (Or.inr (mem_crossPairRows.mp hE))
    have hEDelete : E ∈ deletePoint (avoidPoint H p) q :=
      minimize_subset _ hEL
    obtain ⟨R, hRAvoid, hRErase⟩ := Finset.mem_image.mp hEDelete
    obtain ⟨hRH, hpR⟩ := mem_avoidPoint.mp hRAvoid
    obtain ⟨u, huQ₁, v, hvQ₂, huvE⟩ := mem_crossPairRows.mp hE
    have huv : u ≠ v := fun huv ↦
      (Finset.mem_sdiff.mp huQ₁).2 (huv ▸ (Finset.mem_sdiff.mp hvQ₂).1)
    have hEcard : E.card = 2 := by rw [← huvE]; simp [huv]
    have hqR : q ∉ R := by
      intro hqR
      have hEndpointNePair : ({q, w} : Row α) ≠ {p, q} := by
        intro hEq
        exact hpEndpointPair (hEq ▸ by simp)
      have hREndpoint : R = {q, w} := by
        by_contra hne
        have hPairNeR : ({p, q} : Row α) ≠ R := by
          intro hEq
          exact hpR (hEq ▸ by simp)
        have hEndpointNeR : ({q, w} : Row α) ≠ R := by
          intro hEq
          exact hne hEq.symm
        have hThreeCard :
            ({{p, q}, {q, w}, R} : Hypergraph α).card = 3 := by
          simp [hEndpointNePair, hEndpointNePair.symm, hPairNeR, hPairNeR.symm,
            hEndpointNeR, hEndpointNeR.symm]
        have hThreeSubset :
            ({{p, q}, {q, w}, R} : Hypergraph α) ⊆
              H.filter (fun S ↦ q ∈ S) := by
          intro S hS
          simp only [Finset.mem_insert, Finset.mem_singleton] at hS
          rcases hS with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hPair, by simp⟩
          · exact Finset.mem_filter.mpr ⟨hEndpointPair, by simp⟩
          · exact Finset.mem_filter.mpr ⟨hRH, hqR⟩
        have hThreeDegree : 3 ≤ degree H q := by
          rw [degree]
          simpa [hThreeCard] using Finset.card_le_card hThreeSubset
        omega
      have hEraseCard := congrArg Finset.card hRErase
      rw [hREndpoint] at hEraseCard
      have hqw : q ≠ w := by
        intro hqw
        subst w
        have hEndpointCard := hHRows {q} (by simpa using hEndpointPair)
        simp at hEndpointCard
      simp [hqw, hEcard] at hEraseCard
    have hReqE : R = E := by
      calc
        R = R.erase q := (Finset.erase_eq_of_notMem hqR).symm
        _ = E := hRErase
    exact Finset.mem_filter.mpr ⟨hReqE ▸ hRH, hEcard⟩
  have hCrossSubset :
      crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) ⊆ pairRows H := by
    exact fun _ hE ↦ cross_source hE
  have hPairRow : ({p, q} : Row α) ∈ pairRows H := by
    exact Finset.mem_filter.mpr ⟨hPair, by
      have hpq : p ≠ q := by
        intro hpq
        subst q
        have hPairCard := hHRows {p} (by simpa using hPair)
        simp at hPairCard
      simp [hpq]⟩
  have hEndpointPairRow : ({q, w} : Row α) ∈ pairRows H := by
    exact Finset.mem_filter.mpr ⟨hEndpointPair, by
      have hqw : q ≠ w := by
        intro hqw
        subst w
        have hEndpointCard := hHRows {q} (by simpa using hEndpointPair)
        simp at hEndpointCard
      simp [hqw]⟩
  have hPairNeEndpoint : ({p, q} : Row α) ≠ {q, w} := by
    intro hEq
    exact hpEndpointPair (hEq ▸ by simp)
  have hCrossAvoidPair :
      ∀ E ∈ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁), E ≠ {p, q} := by
    intro E hE hEq
    have hpE : p ∈ E := hEq ▸ (by simp)
    obtain ⟨u, huQ₁, v, hvQ₂, huvE⟩ := mem_crossPairRows.mp hE
    have hEL : E ∈ L := by
      rw [hLtwo]
      exact mem_twoRowBlockers.mpr (Or.inr ⟨u, huQ₁, v, hvQ₂, huvE⟩)
    have hpL : p ∉ E := pairSide_rows_avoid_first H p q E (by simpa [L] using hEL)
    exact hpL hpE
  have hCrossAvoidEndpoint :
      ∀ E ∈ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁), E ≠ {q, w} := by
    intro E hE hEq
    have hqE : q ∈ E := hEq ▸ (by simp)
    obtain ⟨u, huQ₁, v, hvQ₂, huvE⟩ := mem_crossPairRows.mp hE
    have hEL : E ∈ L := by
      rw [hLtwo]
      exact mem_twoRowBlockers.mpr (Or.inr ⟨u, huQ₁, v, hvQ₂, huvE⟩)
    have hqL : q ∉ E := pairSide_rows_avoid_second H p q E (by simpa [L] using hEL)
    exact hqL hqE
  have hCrossCardUpper :
      (crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁)).card ≤ 1 := by
    have hUnionSubset :
        insert ({p, q} : Row α)
            (insert ({q, w} : Row α)
              (crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁))) ⊆ pairRows H := by
      exact Finset.insert_subset hPairRow
        (Finset.insert_subset hEndpointPairRow hCrossSubset)
    have hPairNotCross :
        ({p, q} : Row α) ∉ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) :=
      fun hMem ↦ hCrossAvoidPair _ hMem rfl
    have hEndpointNotCross :
        ({q, w} : Row α) ∉ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) :=
      fun hMem ↦ hCrossAvoidEndpoint _ hMem rfl
    have hPairNotInsert :
        ({p, q} : Row α) ∉ insert ({q, w} : Row α)
          (crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁)) := by
      simp [hPairNeEndpoint, hPairNotCross]
    have hCard := Finset.card_le_card hUnionSubset
    rw [Finset.card_insert_of_notMem hPairNotInsert,
      Finset.card_insert_of_notMem hEndpointNotCross] at hCard
    omega
  have hCrossEq : crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) = {A} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hACross, ?_⟩
    intro E hE
    exact Finset.card_le_one.mp hCrossCardUpper E hE A hACross
  have hAH : A ∈ H := (Finset.mem_filter.mp (cross_source hACross)).1
  have hAcard : A.card = 2 := by simp [A, hab]
  have hAL : A ∈ L := by
    rw [hLtwo]
    exact mem_twoRowBlockers.mpr (Or.inr (mem_crossPairRows.mp hACross))
  refine ⟨w, A, hEndpointPair, hpEndpointPair, hAH, hAcard,
    pairSide_rows_avoid_first H p q A (by simpa [L] using hAL),
    pairSide_rows_avoid_second H p q A (by simpa [L] using hAL), ?_⟩
  intro E hEH hpE hqE
  have hEDelete : E ∈ deletePoint (avoidPoint H p) q := by
    exact Finset.mem_image.mpr
      ⟨E, mem_avoidPoint.mpr ⟨hEH, hpE⟩, Finset.erase_eq_of_notMem hqE⟩
  obtain ⟨M, hML, hME⟩ := exists_minimize_subset hEDelete
  change M ∈ L at hML
  have hMTwo : M ∈ twoRowBlockers Q₁ Q₂ := by
    rw [← hLtwo]
    exact hML
  rcases mem_twoRowBlockers.mp hMTwo with hSingleton | hCross
  · obtain ⟨z, hzInter, hzM⟩ := hSingleton
    have hzw : z = w := by simpa [hInterEq] using hzInter
    have hwM : w ∈ M := by rw [← hzM, hzw]; simp
    exact Or.inr (hME hwM)
  · have hMA : M = A := by
      have hMCross : M ∈ crossPairRows (Q₁ \ Q₂) (Q₂ \ Q₁) :=
        mem_crossPairRows.mpr hCross
      simpa [hCrossEq] using hMCross
    exact Or.inl (hH hAH hEH (by simpa [hMA] using hME)).symm

theorem pairSide_blocker_card_ge_two_of_endpoint_degree_le_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hDegree : degree H q ≤ 2) :
    2 ≤ (blocker (pairSide H p q)).card := by
  exact blocker_card_ge_two_of_atMostOne_singletonRow
    (residual_isClutter _ _)
    (pairSide_rows_nonempty hHRows p q)
    (pairSide_blocker_rows_cardAtLeast_two hPair hBRows)
    (pairSide_singletonRows_card_le_one_of_endpoint_degree_le_two
      hHRows hPair hDegree)

theorem opposite_pairSide_structure_of_two_blockers {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hpDegree : degree H p ≤ 2)
    (hqDegree : degree H q ≤ 2)
    (hFirstCard : (blocker (pairSide H p q)).card = 2) :
    H.card = 6 ∧
      (avoidPoint (avoidPoint H p) q).card = 3 ∧
      3 ≤ (blocker (pairSide H q p)).card := by
  classical
  have hFirstRows : RowsCardAtLeast (blocker (pairSide H p q)) 2 :=
    pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  obtain ⟨w, A, hEndpointPair, hpEndpointPair, hAH, hAcard, hpA, hqA,
      hAvoidStructure⟩ :=
    pairSide_two_blocker_structure hH hHRows hPairRows hPair hqDegree
      hFirstRows hFirstCard
  let Z := avoidPoint (avoidPoint H p) q
  have hAZ : A ∈ Z := by
    exact mem_avoidPoint.mpr ⟨mem_avoidPoint.mpr ⟨hAH, hpA⟩, hqA⟩
  have hEndpointNotZ : ({q, w} : Row α) ∉ Z := by
    intro hMem
    exact (mem_avoidPoint.mp hMem).2 (by simp)
  have hInsertSubset : insert ({q, w} : Row α) Z ⊆ H := by
    apply Finset.insert_subset hEndpointPair
    intro E hE
    exact (mem_avoidPoint.mp (mem_avoidPoint.mp hE).1).1
  have hwEndpoint : w ∈ ({q, w} : Row α) := by simp
  have hDegreeInsert : degree (insert ({q, w} : Row α) Z) w = degree Z w + 1 := by
    rw [degree_insert_of_notMem hEndpointNotZ hwEndpoint]
  have hDegreeZ : degree Z w + 1 ≤ degree H w := by
    rw [← hDegreeInsert]
    exact degree_mono hInsertSubset w
  have hAvoidZSubset : avoidPoint Z w ⊆ {A} := by
    intro E hE
    obtain ⟨hEZ, hwE⟩ := mem_avoidPoint.mp hE
    obtain ⟨hEH, hpE⟩ := mem_avoidPoint.mp (mem_avoidPoint.mp hEZ).1
    have hqE := (mem_avoidPoint.mp hEZ).2
    rcases hAvoidStructure E hEH hpE hqE with hEA | hwE'
    · simp [hEA]
    · exact (hwE hwE').elim
  have hAvoidZCard : (avoidPoint Z w).card ≤ 1 := by
    calc
      (avoidPoint Z w).card ≤ ({A} : Hypergraph α).card :=
        Finset.card_le_card hAvoidZSubset
      _ = 1 := Finset.card_singleton A
  have hZpartition := card_avoidPoint_add_degree Z w
  have hZcardUpper : Z.card ≤ 3 := by
    have hwUpper := hMaxDegree w
    omega
  have hAvoidCommute :
      avoidPoint (avoidPoint H q) p = avoidPoint (avoidPoint H p) q := by
    ext E
    simp only [mem_avoidPoint]
    tauto
  have hPairNotAvoidQ : ({p, q} : Row α) ∉ avoidPoint H q := by
    intro hMem
    exact (mem_avoidPoint.mp hMem).2 (by simp)
  have hPairAvoidInsertSubset : insert ({p, q} : Row α) (avoidPoint H q) ⊆ H :=
    Finset.insert_subset hPair (by
      intro E hE
      exact (mem_avoidPoint.mp hE).1)
  have hpPair : p ∈ ({p, q} : Row α) := by simp
  have hAvoidQDegree : degree (avoidPoint H q) p + 1 ≤ degree H p := by
    have hInsertDegree :
        degree (insert ({p, q} : Row α) (avoidPoint H q)) p =
          degree (avoidPoint H q) p + 1 := by
      rw [degree_insert_of_notMem hPairNotAvoidQ hpPair]
    rw [← hInsertDegree]
    exact degree_mono hPairAvoidInsertSubset p
  have hPartitionQ := card_avoidPoint_add_degree H q
  have hPartitionP := card_avoidPoint_add_degree (avoidPoint H q) p
  rw [hAvoidCommute] at hPartitionP
  have hZcardUpper' : (avoidPoint (avoidPoint H p) q).card ≤ 3 := by
    simpa [Z] using hZcardUpper
  have hHcardUpper : H.card ≤ 6 := by omega
  have hHcardEq : H.card = 6 := by omega
  have hZcardEq : Z.card = 3 := by
    have hZcardEq' : (avoidPoint (avoidPoint H p) q).card = 3 := by omega
    simpa [Z] using hZcardEq'
  have hOtherRows : RowsCardAtLeast (blocker (pairSide H q p)) 2 := by
    exact pairSide_blocker_rows_cardAtLeast_two
      (by simpa [Finset.pair_comm] using hPair) hBRows
  have hOtherLower : 2 ≤ (blocker (pairSide H q p)).card :=
    pairSide_blocker_card_ge_two_of_endpoint_degree_le_two
      hHRows hBRows (by simpa [Finset.pair_comm] using hPair) hpDegree
  have hOtherNotTwo : (blocker (pairSide H q p)).card ≠ 2 := by
    intro hOtherCard
    obtain ⟨v, -, hOtherEndpointPair, hqOtherEndpointPair⟩ :=
      exists_endpoint_pair_of_pairSide_blocker_card_eq_two
        hHRows hPairRows (by simpa [Finset.pair_comm] using hPair)
          hpDegree hOtherRows hOtherCard
    have hFourPairRows :
        ({{p, q}, {q, w}, A, {p, v}} : Hypergraph α) ⊆ pairRows H := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hPair, by
          have hpq : p ≠ q := by
            intro hpq
            subst q
            have hPairCard := hHRows {p} (by simpa using hPair)
            simp at hPairCard
          simp [hpq]⟩
      · exact Finset.mem_filter.mpr ⟨hEndpointPair, by
          have hqw : q ≠ w := by
            intro hqw
            subst w
            have hEndpointCard := hHRows {q} (by simpa using hEndpointPair)
            simp at hEndpointCard
          simp [hqw]⟩
      · exact Finset.mem_filter.mpr ⟨hAH, hAcard⟩
      · exact Finset.mem_filter.mpr ⟨hOtherEndpointPair, by
          have hpv : p ≠ v := by
            intro hpv
            subst v
            have hEndpointCard := hHRows {p} (by simpa using hOtherEndpointPair)
            simp at hEndpointCard
          simp [hpv]⟩
    have hPairNeEndpoint : ({p, q} : Row α) ≠ {q, w} := by
      intro hEq
      exact hpEndpointPair (hEq ▸ by simp)
    have hPairNeA : ({p, q} : Row α) ≠ A := by
      intro hEq
      exact hpA (hEq ▸ by simp)
    have hPairNeOther : ({p, q} : Row α) ≠ {p, v} := by
      intro hEq
      exact hqOtherEndpointPair (hEq ▸ by simp)
    have hEndpointNeA : ({q, w} : Row α) ≠ A := by
      intro hEq
      exact hqA (hEq ▸ by simp)
    have hEndpointNeOther : ({q, w} : Row α) ≠ {p, v} := by
      intro hEq
      exact hqOtherEndpointPair (hEq ▸ by simp)
    have hANeOther : A ≠ ({p, v} : Row α) := by
      intro hEq
      exact hpA (hEq ▸ by simp)
    have hFourCard : ({{p, q}, {q, w}, A, {p, v}} : Hypergraph α).card = 4 := by
      simp [hPairNeEndpoint, hPairNeA, hPairNeOther, hEndpointNeA,
        hEndpointNeOther, hANeOther]
    have hFourLower := Finset.card_le_card hFourPairRows
    omega
  refine ⟨hHcardEq, by simpa [Z] using hZcardEq, ?_⟩
  omega

theorem six_row_decomposition_of_two_blockers {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hpDegree : degree H p ≤ 2)
    (hqDegree : degree H q ≤ 2)
    (hFirstCard : (blocker (pairSide H p q)).card = 2) :
    ∃ w A X,
      ({q, w} : Row α) ∈ H ∧ p ∉ ({q, w} : Row α) ∧
      A ∈ H ∧ A.card = 2 ∧ p ∉ A ∧ q ∉ A ∧
      X ∈ H ∧ p ∈ X ∧ q ∉ X ∧ 3 ≤ X.card ∧
      (avoidPoint (avoidPoint H p) q).card = 3 ∧
      (∀ E ∈ H, p ∉ E → q ∉ E → E = A ∨ w ∈ E) ∧
      H = insert ({p, q} : Row α)
        (insert ({q, w} : Row α)
          (insert X (avoidPoint (avoidPoint H p) q))) ∧
      pairRows H = {{p, q}, {q, w}, A} ∧
      pairRows (pairSide H q p) ⊆ {A, X.erase p} := by
  classical
  obtain ⟨hHcardEq, hZcard, -⟩ :=
    opposite_pairSide_structure_of_two_blockers hH hHcard hHRows hPairRows
      hBRows hMaxDegree hPair hpDegree hqDegree hFirstCard
  have hFirstRows : RowsCardAtLeast (blocker (pairSide H p q)) 2 :=
    pairSide_blocker_rows_cardAtLeast_two hPair hBRows
  obtain ⟨w, A, hEndpointPair, hpEndpointPair, hAH, hAcard, hpA, hqA,
      hAvoidStructure⟩ :=
    pairSide_two_blocker_structure hH hHRows hPairRows hPair hqDegree
      hFirstRows hFirstCard
  let Z := avoidPoint (avoidPoint H p) q
  have hAZ : A ∈ Z :=
    mem_avoidPoint.mpr ⟨mem_avoidPoint.mpr ⟨hAH, hpA⟩, hqA⟩
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hPairCard := hHRows {p} (by simpa using hPair)
    simp at hPairCard
  have hqw : q ≠ w := by
    intro hqw
    subst w
    have hEndpointCard := hHRows {q} (by simpa using hEndpointPair)
    simp at hEndpointCard
  have hPairRow : ({p, q} : Row α) ∈ pairRows H :=
    Finset.mem_filter.mpr ⟨hPair, by simp [hpq]⟩
  have hEndpointPairRow : ({q, w} : Row α) ∈ pairRows H :=
    Finset.mem_filter.mpr ⟨hEndpointPair, by simp [hqw]⟩
  have hARow : A ∈ pairRows H := Finset.mem_filter.mpr ⟨hAH, hAcard⟩
  have hPairNeEndpoint : ({p, q} : Row α) ≠ {q, w} := by
    intro hEq
    exact hpEndpointPair (hEq ▸ by simp)
  have hPairNeA : ({p, q} : Row α) ≠ A := by
    intro hEq
    exact hpA (hEq ▸ by simp)
  have hEndpointNeA : ({q, w} : Row α) ≠ A := by
    intro hEq
    exact hqA (hEq ▸ by simp)
  have hKnownPairsCard : ({{p, q}, {q, w}, A} : Hypergraph α).card = 3 := by
    simp [hPairNeEndpoint, hPairNeA, hEndpointNeA]
  have hKnownPairsSubset : ({{p, q}, {q, w}, A} : Hypergraph α) ⊆ pairRows H := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact hPairRow
    · exact hEndpointPairRow
    · exact hARow
  have hPairRowsEq : pairRows H = {{p, q}, {q, w}, A} := by
    exact (Finset.eq_of_subset_of_card_le hKnownPairsSubset (by
      rw [hKnownPairsCard]
      exact hPairRows)).symm
  have hPairNotZ : ({p, q} : Row α) ∉ Z := by
    intro hMem
    exact (mem_avoidPoint.mp hMem).2 (by simp)
  have hEndpointNotZ : ({q, w} : Row α) ∉ Z := by
    intro hMem
    exact (mem_avoidPoint.mp hMem).2 (by simp)
  let F : Hypergraph α := insert ({p, q} : Row α) (insert ({q, w} : Row α) Z)
  have hFsubset : F ⊆ H := by
    apply Finset.insert_subset hPair
    apply Finset.insert_subset hEndpointPair
    intro E hE
    exact (mem_avoidPoint.mp (mem_avoidPoint.mp hE).1).1
  have hPairNotEndpointInsert :
      ({p, q} : Row α) ∉ insert ({q, w} : Row α) Z := by
    simp [hPairNeEndpoint, hPairNotZ]
  have hFcard : F.card = 5 := by
    rw [show F = insert ({p, q} : Row α) (insert ({q, w} : Row α) Z) from rfl,
      Finset.card_insert_of_notMem hPairNotEndpointInsert,
      Finset.card_insert_of_notMem hEndpointNotZ]
    simpa [Z] using hZcard
  have hFltH : F.card < H.card := by omega
  obtain ⟨X, hXH, hXF⟩ := Finset.exists_mem_notMem_of_card_lt_card hFltH
  have hXNePair : X ≠ ({p, q} : Row α) := by
    intro hEq
    exact hXF (by simp [F, hEq])
  have hXNeEndpoint : X ≠ ({q, w} : Row α) := by
    intro hEq
    exact hXF (by simp [F, hEq])
  have hXnotZ : X ∉ Z := by
    intro hXZ
    exact hXF (by simp [F, hXZ])
  have hqX : q ∉ X := by
    intro hqX
    have hThreeSubset :
        ({{p, q}, {q, w}, X} : Hypergraph α) ⊆ H.filter (fun E ↦ q ∈ E) := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hPair, by simp⟩
      · exact Finset.mem_filter.mpr ⟨hEndpointPair, by simp⟩
      · exact Finset.mem_filter.mpr ⟨hXH, hqX⟩
    have hThreeCard : ({{p, q}, {q, w}, X} : Hypergraph α).card = 3 := by
      simp [hPairNeEndpoint, hXNePair.symm, hXNeEndpoint.symm]
    have hLower := Finset.card_le_card hThreeSubset
    have hThreeDegree : 3 ≤ degree H q := by
      rw [degree]
      simpa [hThreeCard] using hLower
    omega
  have hpX : p ∈ X := by
    by_contra hpX
    exact hXnotZ (by
      exact mem_avoidPoint.mpr ⟨mem_avoidPoint.mpr ⟨hXH, hpX⟩, hqX⟩)
  have hXnotA : X ≠ A := by
    intro hEq
    exact hXnotZ (hEq ▸ hAZ)
  have hXcard : 3 ≤ X.card := by
    have hLower := hHRows X hXH
    by_contra hnot
    have hTwo : X.card = 2 := by omega
    have hXPair : X ∈ pairRows H := Finset.mem_filter.mpr ⟨hXH, hTwo⟩
    rw [hPairRowsEq] at hXPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXPair
    rcases hXPair with hEq | hEq | hEq
    · exact hXNePair hEq
    · exact hXNeEndpoint hEq
    · exact hXnotA hEq
  have hXFcard : (insert X F).card = 6 := by
    rw [Finset.card_insert_of_notMem hXF, hFcard]
  have hXFsubset : insert X F ⊆ H := Finset.insert_subset hXH hFsubset
  have hHdecomp :
      H = insert ({p, q} : Row α)
        (insert ({q, w} : Row α) (insert X Z)) := by
    have hEq : insert X F = H :=
      Finset.eq_of_subset_of_card_le hXFsubset (by omega)
    rw [← hEq]
    ext E
    simp [F, or_comm, or_left_comm]
  have hOtherPairSubset : pairRows (pairSide H q p) ⊆ {A, X.erase p} := by
    intro E hE
    have hESide := (Finset.mem_filter.mp hE).1
    have hEDelete : E ∈ deletePoint (avoidPoint H q) p :=
      minimize_subset _ hESide
    obtain ⟨R, hRAvoid, hRErase⟩ := Finset.mem_image.mp hEDelete
    obtain ⟨hRH, hqR⟩ := mem_avoidPoint.mp hRAvoid
    rw [hHdecomp] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with hRPair | hREndpoint | hRX | hRZ
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      simp [hRErase]
    · have hpR : p ∉ R := (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).2
      have hReqE : R = E := by
        calc
          R = R.erase p := (Finset.erase_eq_of_notMem hpR).symm
          _ = E := hRErase
      have hRPair : R ∈ pairRows H := Finset.mem_filter.mpr
        ⟨(mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).1, by
          simpa [hReqE] using (Finset.mem_filter.mp hE).2⟩
      rw [hPairRowsEq] at hRPair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRPair
      rcases hRPair with hEq | hEq | hEq
      · exact (hpR (hEq ▸ by simp)).elim
      · exact (hqR (hEq ▸ by simp)).elim
      · simp [← hReqE, hEq]
  refine ⟨w, A, X, hEndpointPair, hpEndpointPair, hAH, hAcard, hpA, hqA,
    hXH, hpX, hqX, hXcard, hZcard, hAvoidStructure, ?_, hPairRowsEq,
    hOtherPairSubset⟩
  simpa [Z] using hHdecomp

theorem opposite_pairSide_tight_counts {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hpDegree : degree H p ≤ 2)
    (hqDegree : degree H q ≤ 2)
    (hFirstCard : (blocker (pairSide H p q)).card = 2)
    (hOtherCard : (blocker (pairSide H q p)).card = 3) :
    (pairSide H q p).card = 4 ∧
      RowsCardAtLeast (pairSide H q p) 2 ∧
      (pairRows (pairSide H q p)).card = 2 := by
  classical
  obtain ⟨w, A, X, hEndpointPair, hpEndpointPair, hAH, hAcard, hpA, hqA,
      hXH, hpX, hqX, hXcard, hZcard, -, hHdecomp, -, hOtherPairSubset⟩ :=
    six_row_decomposition_of_two_blockers hH hHcard hHRows hPairRows hBRows
      hMaxDegree hPair hpDegree hqDegree hFirstCard
  let Z := avoidPoint (avoidPoint H p) q
  let L := pairSide H q p
  have hDeleteRows : RowsCardAtLeast (deletePoint (avoidPoint H q) p) 2 := by
    intro E hE
    obtain ⟨R, hRAvoid, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hRH, hqR⟩ := mem_avoidPoint.mp hRAvoid
    rw [hHdecomp] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with hRPair | hREndpoint | hRX | hRZ
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      rw [Finset.card_erase_of_mem hpX]
      omega
    · have hpR : p ∉ R := (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).2
      rw [Finset.erase_eq_of_notMem hpR]
      exact hHRows R (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).1
  have hLRows : RowsCardAtLeast L 2 := by
    intro E hE
    have hEResidual : E ∈ residual (avoidPoint H q) p := by
      simpa [L, pairSide] using hE
    exact hDeleteRows E (minimize_subset _ hEResidual)
  have hADelete : A ∈ deletePoint (avoidPoint H q) p :=
    Finset.mem_image.mpr
      ⟨A, mem_avoidPoint.mpr ⟨hAH, hqA⟩, Finset.erase_eq_of_notMem hpA⟩
  have hAL : A ∈ L := by
    change A ∈ minimize (deletePoint (avoidPoint H q) p)
    apply mem_minimize.mpr
    refine ⟨hADelete, ?_⟩
    intro E hE hEA
    have hEcard := hDeleteRows E hE
    have hEq : E = A := Finset.eq_of_subset_of_card_le hEA (by omega)
    simpa [hEq]
  have hXEraseDelete : X.erase p ∈ deletePoint (avoidPoint H q) p :=
    Finset.mem_image.mpr ⟨X, mem_avoidPoint.mpr ⟨hXH, hqX⟩, rfl⟩
  have hXEraseL : X.erase p ∈ L := by
    change X.erase p ∈ minimize (deletePoint (avoidPoint H q) p)
    apply mem_minimize.mpr
    refine ⟨hXEraseDelete, ?_⟩
    intro E hE hEX
    obtain ⟨R, hRAvoid, hRErase⟩ := Finset.mem_image.mp hE
    obtain ⟨hRH, hqR⟩ := mem_avoidPoint.mp hRAvoid
    rw [hHdecomp] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with hRPair | hREndpoint | hRX | hRZ
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      simpa [hRErase]
    · have hpR : p ∉ R := (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).2
      have hReqE : R = E := by
        calc
          R = R.erase p := (Finset.erase_eq_of_notMem hpR).symm
          _ = E := hRErase
      have hRXsubset : R ⊆ X := by
        intro x hxR
        exact Finset.mem_of_mem_erase (hEX (hReqE ▸ hxR))
      have hReqX : R = X := hH
        (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).1 hXH hRXsubset
      exact (hpR (hReqX ▸ hpX)).elim
  have hAneXErase : A ≠ X.erase p := by
    intro hEq
    have hAX : A ⊆ X := by
      intro x hxA
      exact Finset.mem_of_mem_erase (hEq ▸ hxA)
    have hAXEq : A = X := hH hAH hXH hAX
    exact hpA (hAXEq ▸ hpX)
  have hLcardLowerTwo : 2 ≤ L.card := by
    have hTwoSubset : ({A, X.erase p} : Hypergraph α) ⊆ L := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact hAL
      · exact hXEraseL
    have hCard := Finset.card_le_card hTwoSubset
    simpa [hAneXErase] using hCard
  have hKnownQRows :
      ({{p, q}, {q, w}} : Hypergraph α) ⊆ H.filter (fun E ↦ q ∈ E) := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hPair, by simp⟩
    · exact Finset.mem_filter.mpr ⟨hEndpointPair, by simp⟩
  have hPairNeEndpoint : ({p, q} : Row α) ≠ {q, w} := by
    intro hEq
    exact hpEndpointPair (hEq ▸ by simp)
  have hKnownQCard : ({{p, q}, {q, w}} : Hypergraph α).card = 2 := by
    simp [hPairNeEndpoint]
  have hqDegreeLower : 2 ≤ degree H q := by
    rw [degree]
    simpa [hKnownQCard] using Finset.card_le_card hKnownQRows
  have hqDegreeEq : degree H q = 2 := by omega
  have hAvoidQCard : (avoidPoint H q).card = 4 := by
    have hPartition := card_avoidPoint_add_degree H q
    have hHcardEq : H.card = 6 := by
      obtain ⟨hEq, -, -⟩ := opposite_pairSide_structure_of_two_blockers
        hH hHcard hHRows hPairRows hBRows hMaxDegree hPair hpDegree hqDegree hFirstCard
      exact hEq
    omega
  have hLcardUpper : L.card ≤ 4 := by
    simpa [L, pairSide, hAvoidQCard] using residual_card_le (avoidPoint H q) p
  have hOtherRows : RowsCardAtLeast (blocker L) 2 := by
    simpa [L] using pairSide_blocker_rows_cardAtLeast_two
      (by simpa [Finset.pair_comm] using hPair) hBRows
  have hOtherPairUpper : (pairRows L).card ≤ 2 := by
    calc
      (pairRows L).card ≤ ({A, X.erase p} : Hypergraph α).card :=
        Finset.card_le_card (by simpa [L] using hOtherPairSubset)
      _ ≤ 2 := Finset.card_le_two
  have hLcard : L.card = 4 := by
    by_contra hnot
    have hCases : L.card = 2 ∨ L.card = 3 := by omega
    rcases hCases with hTwo | hThree
    · obtain ⟨E, F, hEF, hLTwo⟩ := Finset.card_eq_two.mp hTwo
      have hEcard : 2 ≤ E.card := hLRows E (by simp [hLTwo])
      have hFcard : 2 ≤ F.card := hLRows F (by simp [hLTwo])
      have hProduct : E.card * F.card ≤ (blocker L).card := by
        simpa [hLTwo] using twoRow_blocker_card_ge_product
          (A := E) (B := F) (by simpa [hLTwo] using hOtherRows)
      have hFourProduct : 4 ≤ E.card * F.card := by
        exact Nat.mul_le_mul hEcard hFcard
      rw [show (blocker L).card = 3 by simpa [L] using hOtherCard] at hProduct
      omega
    · have hFour := threeRow_blocker_card_ge_four_of_pairRows_card_le_two
        (residual_isClutter (avoidPoint H q) p) hThree hLRows hOtherRows
        hOtherPairUpper
      change 4 ≤ (blocker L).card at hFour
      rw [show (blocker L).card = 3 by simpa [L] using hOtherCard] at hFour
      omega
  have hOtherPairPositive : 1 ≤ (pairRows L).card := by
    apply Finset.one_le_card.mpr
    exact ⟨A, Finset.mem_filter.mpr ⟨hAL, hAcard⟩⟩
  obtain ⟨T₁, T₂, T₃, hT₁T₂, hT₁T₃, hT₂T₃, hK⟩ :=
    Finset.card_eq_three.mp (by simpa [L] using hOtherCard)
  let K := blocker L
  have hK' : K = {T₁, T₂, T₃} := by simpa [K] using hK
  have hLClutter : IsClutter L := by
    simpa [L, pairSide] using residual_isClutter (avoidPoint H q) p
  have hBlockerK : blocker K = L := by
    simpa [K] using blocker_involution hLClutter
  have hKRows : RowsCardAtLeast K 2 := by simpa [K] using hOtherRows
  have hBlockerKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hBlockerK] using hLRows
  have hBlockerKcard : (blocker K).card = 4 := by rw [hBlockerK, hLcard]
  have hBlockerKPairPositive : 1 ≤ (pairRows (blocker K)).card := by
    simpa [hBlockerK] using hOtherPairPositive
  have hBlockerKPairUpper : (pairRows (blocker K)).card ≤ 2 := by
    simpa [hBlockerK] using hOtherPairUpper
  have hPairCard := threeRow_pairRows_card_eq_two_of_blocker_card_eq_four
    hK' hT₁T₂ hT₁T₃ hT₂T₃ hKRows hBlockerKRows hBlockerKcard
    hBlockerKPairPositive hBlockerKPairUpper
  exact ⟨by simpa [L] using hLcard, by simpa [L] using hLRows,
    by simpa [hBlockerK, L] using hPairCard⟩

theorem blocker_mem_of_six_row_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q u s t r₁ r₂ : α}
    (hpq : p ≠ q)
    (hpOutside : p ∉ ({u, s, t, r₁, r₂} : Row α))
    (hqOutside : q ∉ ({u, s, t, r₁, r₂} : Row α))
    (huNeS : u ≠ s) (huNeT : u ≠ t) (huNeR₁ : u ≠ r₁) (huNeR₂ : u ≠ r₂)
    (hsNeT : s ≠ t) (hsNeR₁ : s ≠ r₁) (hsNeR₂ : s ≠ r₂)
    (htNeR₁ : t ≠ r₁) (htNeR₂ : t ≠ r₂) (hr₁NeR₂ : r₁ ≠ r₂)
    (hHNormal : H =
      {{p, q}, {q, s}, insert p {u, r₂}, {u, r₁}, {s, t, r₁}, {s, t, r₂}}) :
    ({p, q, t, r₁} : Row α) ∈ blocker H := by
  classical
  have hpU : p ≠ u := by
    intro hEq
    exact hpOutside (hEq ▸ by simp)
  have hpS : p ≠ s := by
    intro hEq
    exact hpOutside (hEq ▸ by simp)
  have hpT : p ≠ t := by
    intro hEq
    exact hpOutside (hEq ▸ by simp)
  have hpR₁ : p ≠ r₁ := by
    intro hEq
    exact hpOutside (hEq ▸ by simp)
  have hpR₂ : p ≠ r₂ := by
    intro hEq
    exact hpOutside (hEq ▸ by simp)
  have hqU : q ≠ u := by
    intro hEq
    exact hqOutside (hEq ▸ by simp)
  have hqS : q ≠ s := by
    intro hEq
    exact hqOutside (hEq ▸ by simp)
  have hqT : q ≠ t := by
    intro hEq
    exact hqOutside (hEq ▸ by simp)
  have hqR₁ : q ≠ r₁ := by
    intro hEq
    exact hqOutside (hEq ▸ by simp)
  have hqR₂ : q ≠ r₂ := by
    intro hEq
    exact hqOutside (hEq ▸ by simp)
  apply mem_blocker.mpr
  have hTransversal : IsTransversal H {p, q, t, r₁} := by
    intro E hE
    rw [hHNormal] at hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨p, by simp, by simp⟩
    · exact ⟨q, by simp, by simp⟩
    · exact ⟨p, by simp, by simp⟩
    · exact ⟨r₁, by simp, by simp⟩
    · exact ⟨t, by simp, by simp⟩
    · exact ⟨t, by simp, by simp⟩
  apply hTransversal.minimal_of_privateRows
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx
  · subst x
    refine ⟨insert p {u, r₂}, by rw [hHNormal]; simp, by simp, by simp, ?_⟩
    intro y hyT hyX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyT hyX
    rcases hyT with rfl | rfl | rfl | rfl <;>
      rcases hyX with h | h | h <;> simp_all
  · subst x
    refine ⟨{q, s}, by rw [hHNormal]; simp, by simp, by simp, ?_⟩
    intro y hyT hyY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyT hyY
    rcases hyT with rfl | rfl | rfl | rfl <;>
      rcases hyY with h | h <;> simp_all
  · subst x
    refine ⟨{s, t, r₂}, by rw [hHNormal]; simp, by simp, by simp, ?_⟩
    intro y hyT hyZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyT hyZ
    rcases hyT with rfl | rfl | rfl | rfl <;>
      rcases hyZ with h | h | h <;> simp_all
  · subst x
    refine ⟨{u, r₁}, by rw [hHNormal]; simp, by simp, by simp, ?_⟩
    intro y hyT hyA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyT hyA
    rcases hyT with rfl | rfl | rfl | rfl <;>
      rcases hyA with h | h <;> simp_all

theorem exists_extra_blocker_of_two_three_pairSides {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hpDegree : degree H p ≤ 2)
    (hqDegree : degree H q ≤ 2)
    (hFirstCard : (blocker (pairSide H p q)).card = 2)
    (hOtherCard : (blocker (pairSide H q p)).card = 3) :
    ∃ T ∈ blocker H, p ∈ T ∧ q ∈ T := by
  classical
  obtain ⟨w, A, X, hEndpointPair, hpEndpointPair, hAH, hAcard, hpA, hqA,
      hXH, hpX, hqX, hXcard, hZcard, hAvoidStructure, hHdecomp, -, hPairSubset⟩ :=
    six_row_decomposition_of_two_blockers hH hHcard hHRows hPairRows hBRows
      hMaxDegree hPair hpDegree hqDegree hFirstCard
  obtain ⟨hLcard, hLRows, hLPairCard⟩ :=
    opposite_pairSide_tight_counts hH hHcard hHRows hPairRows hBRows
      hMaxDegree hPair hpDegree hqDegree hFirstCard hOtherCard
  let Z := avoidPoint (avoidPoint H p) q
  let L := pairSide H q p
  let K := blocker L
  have hLClutter : IsClutter L := by
    simpa [L, pairSide] using residual_isClutter (avoidPoint H q) p
  have hOtherRows : RowsCardAtLeast K 2 := by
    simpa [K, L] using pairSide_blocker_rows_cardAtLeast_two
      (by simpa [Finset.pair_comm] using hPair) hBRows
  obtain ⟨T₁, T₂, T₃, hT₁T₂, hT₁T₃, hT₂T₃, hKRowsEq⟩ :=
    Finset.card_eq_three.mp (by simpa [K, L] using hOtherCard)
  have hKRowsEq' : K = {T₁, T₂, T₃} := hKRowsEq
  have hBlockerK : blocker K = L := by
    simpa [K] using blocker_involution hLClutter
  have hBlockerKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [hBlockerK, L] using hLRows
  have hBlockerKcard : (blocker K).card = 4 := by
    rw [hBlockerK]
    simpa [L] using hLcard
  have hBlockerKPairCard : (pairRows (blocker K)).card = 2 := by
    rw [hBlockerK]
    simpa [L] using hLPairCard
  obtain ⟨u, a, b, c₁, c₂, huNeA, huNeB, huNeC₁, huNeC₂,
      haNeB, haNeC₁, haNeC₂, hbNeC₁, hbNeC₂, hc₁NeC₂, hNormal⟩ :=
    threeRow_two_pair_normal_form hKRowsEq' hT₁T₂ hT₁T₃ hT₂T₃
      hOtherRows hBlockerKRows hBlockerKcard hBlockerKPairCard
  have hLNormal :
      L = {{u, c₁}, {u, c₂}, {a, b, c₁}, {a, b, c₂}} := by
    rw [← hBlockerK]
    exact hNormal
  have hPairNormal : pairRows L = {{u, c₁}, {u, c₂}} := by
    rw [hLNormal]
    ext E
    simp only [pairRows, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hE, hCard⟩
      rcases hE with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [huNeA, huNeB, huNeC₁, huNeC₂, haNeB, haNeC₁,
          haNeC₂, hbNeC₁, hbNeC₂, hc₁NeC₂] at hCard
      · simp [huNeA, huNeB, huNeC₁, huNeC₂, haNeB, haNeC₁,
          haNeC₂, hbNeC₁, hbNeC₂, hc₁NeC₂] at hCard
    · intro hE
      rcases hE with rfl | rfl
      · exact ⟨Or.inl rfl, by simp [huNeC₁]⟩
      · exact ⟨Or.inr (Or.inl rfl), by simp [huNeC₂]⟩
  have hAZ : A ∈ Z := by
    exact mem_avoidPoint.mpr ⟨mem_avoidPoint.mpr ⟨hAH, hpA⟩, hqA⟩
  have hAneXErase : A ≠ X.erase p := by
    intro hEq
    have hAX : A ⊆ X := by
      intro x hxA
      exact Finset.mem_of_mem_erase (hEq ▸ hxA)
    have hAXEq : A = X := hH hAH hXH hAX
    exact hpA (hAXEq ▸ hpX)
  have hCandidateCard : ({A, X.erase p} : Hypergraph α).card = 2 := by
    simp [hAneXErase]
  have hPairCandidate : pairRows L = {A, X.erase p} := by
    exact Finset.eq_of_subset_of_card_le (by simpa [L] using hPairSubset) (by
      rw [hCandidateCard]
      have : (pairRows L).card = 2 := by simpa [L] using hLPairCard
      omega)
  have hXEraseCard : (X.erase p).card = 2 := by
    have hMem : X.erase p ∈ pairRows L := by simp [hPairCandidate]
    exact (Finset.mem_filter.mp hMem).2
  have triple_mem_Z {E : Row α} (hEL : E ∈ L) (hEcard : E.card = 3) : E ∈ Z := by
    have hEResidual : E ∈ residual (avoidPoint H q) p := by simpa [L, pairSide] using hEL
    have hEDelete : E ∈ deletePoint (avoidPoint H q) p := minimize_subset _ hEResidual
    obtain ⟨R, hRAvoid, hRErase⟩ := Finset.mem_image.mp hEDelete
    obtain ⟨hRH, hqR⟩ := mem_avoidPoint.mp hRAvoid
    rw [hHdecomp] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with hRPair | hREndpoint | hRX | hRZ
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      exact (hqR (by simp)).elim
    · subst R
      have hCardEq := congrArg Finset.card hRErase
      omega
    · have hpR : p ∉ R := (mem_avoidPoint.mp (mem_avoidPoint.mp hRZ).1).2
      have hReqE : R = E := by
        calc
          R = R.erase p := (Finset.erase_eq_of_notMem hpR).symm
          _ = E := hRErase
      simpa [Z, hReqE] using hRZ
  have hTriple₁L : ({a, b, c₁} : Row α) ∈ L := by simp [hLNormal]
  have hTriple₂L : ({a, b, c₂} : Row α) ∈ L := by simp [hLNormal]
  have hTriple₁card : ({a, b, c₁} : Row α).card = 3 := by
    simp [haNeB, haNeC₁, hbNeC₁]
  have hTriple₂card : ({a, b, c₂} : Row α).card = 3 := by
    simp [haNeB, haNeC₂, hbNeC₂]
  have hTriple₁Z := triple_mem_Z hTriple₁L hTriple₁card
  have hTriple₂Z := triple_mem_Z hTriple₂L hTriple₂card
  have hwTriple₁ : w ∈ ({a, b, c₁} : Row α) := by
    rcases hAvoidStructure _
        (mem_avoidPoint.mp (mem_avoidPoint.mp hTriple₁Z).1).1
        (mem_avoidPoint.mp (mem_avoidPoint.mp hTriple₁Z).1).2
        (mem_avoidPoint.mp hTriple₁Z).2 with hEq | hw
    · have hCardEq := congrArg Finset.card hEq
      omega
    · exact hw
  have hwTriple₂ : w ∈ ({a, b, c₂} : Row α) := by
    rcases hAvoidStructure _
        (mem_avoidPoint.mp (mem_avoidPoint.mp hTriple₂Z).1).1
        (mem_avoidPoint.mp (mem_avoidPoint.mp hTriple₂Z).1).2
        (mem_avoidPoint.mp hTriple₂Z).2 with hEq | hw
    · have hCardEq := congrArg Finset.card hEq
      omega
    · exact hw
  have hwCases : w = a ∨ w = b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple₁ hwTriple₂
    rcases hwTriple₁ with hwa | hwb | hwc₁
    · exact Or.inl hwa
    · exact Or.inr hwb
    · rcases hwTriple₂ with hwa | hwb | hwc₂
      · exact (haNeC₁ (hwa.symm.trans hwc₁)).elim
      · exact (hbNeC₁ (hwb.symm.trans hwc₁)).elim
      · exact (hc₁NeC₂ (hwc₁.symm.trans hwc₂)).elim
  have hAPair : A ∈ pairRows L := by simp [hPairCandidate]
  rw [hPairNormal] at hAPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hAPair
  have hAneTriple₁ : A ≠ ({a, b, c₁} : Row α) := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hAneTriple₂ : A ≠ ({a, b, c₂} : Row α) := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hTripleNe : ({a, b, c₁} : Row α) ≠ {a, b, c₂} := by
    intro hEq
    have hc₁Mem : c₁ ∈ ({a, b, c₂} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc₁Mem
    rcases hc₁Mem with hc₁a | hc₁b | hc₁c₂
    · exact haNeC₁ hc₁a.symm
    · exact hbNeC₁ hc₁b.symm
    · exact hc₁NeC₂ hc₁c₂
  have hZSubset :
      ({A, {a, b, c₁}, {a, b, c₂}} : Hypergraph α) ⊆ Z := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl
    · exact hAZ
    · exact hTriple₁Z
    · exact hTriple₂Z
  have hZFamilyCard :
      ({A, {a, b, c₁}, {a, b, c₂}} : Hypergraph α).card = 3 := by
    simp [hAneTriple₁, hAneTriple₂, hTripleNe]
  have hZeq : Z = {A, {a, b, c₁}, {a, b, c₂}} := by
    exact (Finset.eq_of_subset_of_card_le hZSubset (by
      rw [hZFamilyCard]
      have : Z.card = 3 := by simpa [Z] using hZcard
      omega)).symm
  have hZeqRaw :
      avoidPoint (avoidPoint H p) q =
        {A, {a, b, c₁}, {a, b, c₂}} := by
    simpa [Z] using hZeq
  have hpNormal : p ∉ ({u, a, b, c₁, c₂} : Row α) := by
    have hpPair₁ : p ∉ ({u, c₁} : Row α) :=
      pairSide_rows_avoid_second H q p _ (by
        show ({u, c₁} : Row α) ∈ L
        rw [hLNormal]
        simp)
    have hpPair₂ : p ∉ ({u, c₂} : Row α) :=
      pairSide_rows_avoid_second H q p _ (by
        show ({u, c₂} : Row α) ∈ L
        rw [hLNormal]
        simp)
    have hpTriple : p ∉ ({a, b, c₁} : Row α) :=
      pairSide_rows_avoid_second H q p _ hTriple₁L
    intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hpu | hpa | hpb | hpc₁ | hpc₂
    · exact hpPair₁ (hpu ▸ by simp)
    · exact hpTriple (hpa ▸ by simp)
    · exact hpTriple (hpb ▸ by simp)
    · exact hpPair₁ (hpc₁ ▸ by simp)
    · exact hpPair₂ (hpc₂ ▸ by simp)
  have hqNormal : q ∉ ({u, a, b, c₁, c₂} : Row α) := by
    have hqPair₁ : q ∉ ({u, c₁} : Row α) :=
      pairSide_rows_avoid_first H q p _ (by
        show ({u, c₁} : Row α) ∈ L
        rw [hLNormal]
        simp)
    have hqPair₂ : q ∉ ({u, c₂} : Row α) :=
      pairSide_rows_avoid_first H q p _ (by
        show ({u, c₂} : Row α) ∈ L
        rw [hLNormal]
        simp)
    have hqTriple : q ∉ ({a, b, c₁} : Row α) :=
      pairSide_rows_avoid_first H q p _ hTriple₁L
    intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hqu | hqa | hqb | hqc₁ | hqc₂
    · exact hqPair₁ (hqu ▸ by simp)
    · exact hqTriple (hqa ▸ by simp)
    · exact hqTriple (hqb ▸ by simp)
    · exact hqPair₁ (hqc₁ ▸ by simp)
    · exact hqPair₂ (hqc₂ ▸ by simp)
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hPairCard := hHRows {p} (by simpa using hPair)
    simp at hPairCard
  have hXPair : X.erase p ∈ pairRows L := by simp [hPairCandidate]
  rw [hPairNormal] at hXPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hXPair
  rcases hAPair with hA₁ | hA₂
  · have hX₂ : X.erase p = {u, c₂} := by
      rcases hXPair with hX₁ | hX₂
      · exact (hAneXErase (hA₁.trans hX₁.symm)).elim
      · exact hX₂
    have hXeq : X = insert p {u, c₂} := by
      calc
        X = insert p (X.erase p) := (Finset.insert_erase hpX).symm
        _ = insert p {u, c₂} := by rw [hX₂]
    rcases hwCases with hwa | hwb
    · have hHNormal : H =
          {{p, q}, {q, a}, insert p {u, c₂}, {u, c₁},
            {a, b, c₁}, {a, b, c₂}} := by
        rw [hHdecomp, hZeqRaw, hA₁, hXeq, hwa]
      have hExtra := blocker_mem_of_six_row_normal_form
        (H := H) (p := p) (q := q) (u := u) (s := a) (t := b)
        (r₁ := c₁) (r₂ := c₂) hpq hpNormal hqNormal huNeA huNeB
        huNeC₁ huNeC₂ haNeB haNeC₁ haNeC₂ hbNeC₁ hbNeC₂ hc₁NeC₂ hHNormal
      exact ⟨{p, q, b, c₁}, hExtra, by simp, by simp⟩
    · have hpOutside : p ∉ ({u, b, a, c₁, c₂} : Row α) := by
        simpa [or_comm, or_left_comm] using hpNormal
      have hqOutside : q ∉ ({u, b, a, c₁, c₂} : Row α) := by
        simpa [or_comm, or_left_comm] using hqNormal
      have hHNormal : H =
          {{p, q}, {q, b}, insert p {u, c₂}, {u, c₁},
            {b, a, c₁}, {b, a, c₂}} := by
        rw [hHdecomp, hZeqRaw, hA₁, hXeq, hwb]
        ext E
        simp [Finset.ext_iff, or_comm, or_left_comm]
      have hExtra := blocker_mem_of_six_row_normal_form
        (H := H) (p := p) (q := q) (u := u) (s := b) (t := a)
        (r₁ := c₁) (r₂ := c₂) hpq hpOutside hqOutside huNeB huNeA
        huNeC₁ huNeC₂ haNeB.symm hbNeC₁ hbNeC₂ haNeC₁ haNeC₂ hc₁NeC₂
        hHNormal
      exact ⟨{p, q, a, c₁}, hExtra, by simp, by simp⟩
  · have hX₁ : X.erase p = {u, c₁} := by
      rcases hXPair with hX₁ | hX₂
      · exact hX₁
      · exact (hAneXErase (hA₂.trans hX₂.symm)).elim
    have hXeq : X = insert p {u, c₁} := by
      calc
        X = insert p (X.erase p) := (Finset.insert_erase hpX).symm
        _ = insert p {u, c₁} := by rw [hX₁]
    rcases hwCases with hwa | hwb
    · have hpOutside : p ∉ ({u, a, b, c₂, c₁} : Row α) := by
        simpa [or_comm, or_left_comm] using hpNormal
      have hqOutside : q ∉ ({u, a, b, c₂, c₁} : Row α) := by
        simpa [or_comm, or_left_comm] using hqNormal
      have hHNormal : H =
          {{p, q}, {q, a}, insert p {u, c₁}, {u, c₂},
            {a, b, c₂}, {a, b, c₁}} := by
        rw [hHdecomp, hZeqRaw, hA₂, hXeq, hwa]
        ext E
        simp [Finset.ext_iff, or_comm, or_left_comm]
      have hExtra := blocker_mem_of_six_row_normal_form
        (H := H) (p := p) (q := q) (u := u) (s := a) (t := b)
        (r₁ := c₂) (r₂ := c₁) hpq hpOutside hqOutside huNeA huNeB
        huNeC₂ huNeC₁ haNeB haNeC₂ haNeC₁ hbNeC₂ hbNeC₁ hc₁NeC₂.symm
        hHNormal
      exact ⟨{p, q, b, c₂}, hExtra, by simp, by simp⟩
    · have hpOutside : p ∉ ({u, b, a, c₂, c₁} : Row α) := by
        simpa [or_comm, or_left_comm] using hpNormal
      have hqOutside : q ∉ ({u, b, a, c₂, c₁} : Row α) := by
        simpa [or_comm, or_left_comm] using hqNormal
      have hHNormal : H =
          {{p, q}, {q, b}, insert p {u, c₁}, {u, c₂},
            {b, a, c₂}, {b, a, c₁}} := by
        rw [hHdecomp, hZeqRaw, hA₂, hXeq, hwb]
        ext E
        simp [Finset.ext_iff, or_comm, or_left_comm]
      have hExtra := blocker_mem_of_six_row_normal_form
        (H := H) (p := p) (q := q) (u := u) (s := b) (t := a)
        (r₁ := c₂) (r₂ := c₁) hpq hpOutside hqOutside huNeB huNeA
        huNeC₂ huNeC₁ haNeB.symm hbNeC₂ hbNeC₁ haNeC₂ haNeC₁ hc₁NeC₂.symm
        hHNormal
      exact ⟨{p, q, a, c₂}, hExtra, by simp, by simp⟩

theorem pairEndpoint_blocker_card_ge_six {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hPair : ({p, q} : Row α) ∈ H)
    (hpDegree : degree H p ≤ 2)
    (hqDegree : degree H q ≤ 2) :
    6 ≤ (blocker H).card := by
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hPairCard := hHRows {p} (by simpa using hPair)
    simp at hPairCard
  have hFirstLower : 2 ≤ (blocker (pairSide H p q)).card :=
    pairSide_blocker_card_ge_two_of_endpoint_degree_le_two
      hHRows hBRows hPair hqDegree
  have hPairSwap : ({q, p} : Row α) ∈ H := by
    simpa [Finset.pair_comm] using hPair
  have hOtherLower : 2 ≤ (blocker (pairSide H q p)).card :=
    pairSide_blocker_card_ge_two_of_endpoint_degree_le_two
      hHRows hBRows hPairSwap hpDegree
  have hSum := pairSide_blocker_card_add_le hpq hPair
  by_cases hFirstTwo : (blocker (pairSide H p q)).card = 2
  · have hOtherThree : 3 ≤ (blocker (pairSide H q p)).card :=
      (opposite_pairSide_structure_of_two_blockers hH hHcard hHRows hPairRows
        hBRows hMaxDegree hPair hpDegree hqDegree hFirstTwo).2.2
    by_cases hOtherFour : 4 ≤ (blocker (pairSide H q p)).card
    · omega
    · have hOtherThreeEq : (blocker (pairSide H q p)).card = 3 := by omega
      obtain ⟨T, hT, hpT, hqT⟩ :=
        exists_extra_blocker_of_two_three_pairSides hH hHcard hHRows hPairRows
          hBRows hMaxDegree hPair hpDegree hqDegree hFirstTwo hOtherThreeEq
      have hPlus := pairSide_blocker_card_add_one_le
        hpq hPair hT hpT hqT
      omega
  · have hFirstThree : 3 ≤ (blocker (pairSide H p q)).card := by omega
    by_cases hOtherTwo : (blocker (pairSide H q p)).card = 2
    · by_cases hFirstFour : 4 ≤ (blocker (pairSide H p q)).card
      · omega
      · have hFirstThreeEq : (blocker (pairSide H p q)).card = 3 := by omega
        obtain ⟨T, hT, hqT, hpT⟩ :=
          exists_extra_blocker_of_two_three_pairSides
            (H := H) (p := q) (q := p) hH hHcard hHRows hPairRows hBRows
              hMaxDegree hPairSwap hqDegree hpDegree hOtherTwo hFirstThreeEq
        have hPlus := pairSide_blocker_card_add_one_le
          hpq hPair hT hpT hqT
        omega
    · have hOtherThree : 3 ≤ (blocker (pairSide H q p)).card := by omega
      omega

theorem pairRow_has_degree_three_endpoint_of_five_blockers {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (hHcard : 6 ≤ H.card)
    (hHRows : RowsCardAtLeast H 2)
    (hPairRows : (pairRows H).card ≤ 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hMaxDegree : MaxDegreeAtMost H 3)
    (hBcard : (blocker H).card = 5) :
    ∀ Q ∈ H, Q.card = 2 → ∃ y ∈ Q, degree H y = 3 := by
  intro Q hQH hQcard
  obtain ⟨p, q, hpq, hQeq⟩ := Finset.card_eq_two.mp hQcard
  have hPair : ({p, q} : Row α) ∈ H := by simpa [hQeq] using hQH
  by_cases hpThree : degree H p = 3
  · exact ⟨p, by simp [hQeq], hpThree⟩
  by_cases hqThree : degree H q = 3
  · exact ⟨q, by simp [hQeq], hqThree⟩
  have hpDegree : degree H p ≤ 2 := by
    have := hMaxDegree p
    omega
  have hqDegree : degree H q ≤ 2 := by
    have := hMaxDegree q
    omega
  have hSix := pairEndpoint_blocker_card_ge_six hH hHcard hHRows hPairRows
    hBRows hMaxDegree hPair hpDegree hqDegree
  omega

end AiMathLab.P0054.G413
