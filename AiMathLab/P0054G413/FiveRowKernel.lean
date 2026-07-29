import AiMathLab.P0054G413.PairGraphs.Eight

namespace AiMathLab.P0054.G413

def liftPairRow {α : Type*} [DecidableEq α] (x : α) (Q : Row α) : Row α :=
  if Q.card = 2 then insert x Q else Q

def forcedBase {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) : Hypergraph α :=
  H.image (liftPairRow x)

def IsKernelCompletion {α : Type*} [Fintype α] [DecidableEq α]
    (K : Hypergraph α) (x : α) (D : Hypergraph α) : Prop :=
  IsClutter D ∧
  D.card = 8 ∧
  RowsCardAtLeast D 3 ∧
  MaxDegreeAtMost D 3 ∧
  MaxDegreeAtMost K 3 ∧
  forcedBase (blocker K) x ⊆ D ∧
  K ⊆ blocker D

@[simp]
theorem erase_liftPairRow {α : Type*} [DecidableEq α]
    {x : α} {Q : Row α} (hxQ : x ∉ Q) :
    (liftPairRow x Q).erase x = Q := by
  unfold liftPairRow
  split
  · simp [hxQ]
  · exact Finset.erase_eq_of_notMem hxQ

theorem mem_liftPairRow_iff {α : Type*} [DecidableEq α]
    {x y : α} (hyx : y ≠ x) (Q : Row α) :
    y ∈ liftPairRow x Q ↔ y ∈ Q := by
  unfold liftPairRow
  split
  · simp [hyx]
  · rfl

theorem liftPairRow_injOn {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} (hxH : ∀ Q ∈ H, x ∉ Q) :
    Set.InjOn (liftPairRow x) H := by
  intro Q hQ R hR hEq
  have hErase := congrArg (fun E : Row α ↦ E.erase x) hEq
  simpa [erase_liftPairRow (hxH Q hQ), erase_liftPairRow (hxH R hR)] using hErase

theorem forcedBase_card {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} (hxH : ∀ Q ∈ H, x ∉ Q) :
    (forcedBase H x).card = H.card := by
  unfold forcedBase
  exact Finset.card_image_iff.mpr (liftPairRow_injOn hxH)

theorem mem_forcedBase_lift {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {Q : Row α} (hQ : Q ∈ H) :
    liftPairRow x Q ∈ forcedBase H x := by
  exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩

theorem degree_forcedBase_eq {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x y : α} (hyx : y ≠ x)
    (hxH : ∀ Q ∈ H, x ∉ Q) :
    degree (forcedBase H x) y = degree H y := by
  have hfilter :
      (forcedBase H x).filter (fun Q ↦ y ∈ Q) =
        (H.filter fun Q ↦ y ∈ Q).image (liftPairRow x) := by
    ext R
    constructor
    · intro hR
      obtain ⟨hRbase, hyR⟩ := Finset.mem_filter.mp hR
      obtain ⟨Q, hQH, hQR⟩ := Finset.mem_image.mp hRbase
      subst R
      have hyQ := (mem_liftPairRow_iff hyx Q).mp hyR
      exact Finset.mem_image.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQH, hyQ⟩, rfl⟩
    · intro hR
      obtain ⟨Q, hQ, hQR⟩ := Finset.mem_image.mp hR
      obtain ⟨hQH, hyQ⟩ := Finset.mem_filter.mp hQ
      subst R
      exact Finset.mem_filter.mpr
        ⟨mem_forcedBase_lift hQH, (mem_liftPairRow_iff hyx Q).mpr hyQ⟩
  rw [degree, degree, hfilter]
  exact Finset.card_image_iff.mpr
    ((liftPairRow_injOn hxH).mono (by exact Finset.filter_subset _ _))

theorem center_mem_liftPairRow_iff {α : Type*} [DecidableEq α]
    {x : α} {Q : Row α} (hxQ : x ∉ Q) :
    x ∈ liftPairRow x Q ↔ Q.card = 2 := by
  unfold liftPairRow
  split <;> simp_all

theorem degree_forcedBase_center {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} (hxH : ∀ Q ∈ H, x ∉ Q) :
    degree (forcedBase H x) x = (pairRows H).card := by
  have hfilter :
      (forcedBase H x).filter (fun Q ↦ x ∈ Q) =
        (pairRows H).image (liftPairRow x) := by
    ext R
    constructor
    · intro hR
      obtain ⟨hRbase, hxR⟩ := Finset.mem_filter.mp hR
      obtain ⟨Q, hQH, hQR⟩ := Finset.mem_image.mp hRbase
      subst R
      have hQpair := (center_mem_liftPairRow_iff (hxH Q hQH)).mp hxR
      exact Finset.mem_image.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQH, hQpair⟩, rfl⟩
    · intro hR
      obtain ⟨Q, hQ, hQR⟩ := Finset.mem_image.mp hR
      obtain ⟨hQH, hQpair⟩ := Finset.mem_filter.mp hQ
      subst R
      exact Finset.mem_filter.mpr
        ⟨mem_forcedBase_lift hQH, (center_mem_liftPairRow_iff (hxH Q hQH)).mpr hQpair⟩
  rw [degree, hfilter]
  exact Finset.card_image_iff.mpr
    ((liftPairRow_injOn hxH).mono (by exact Finset.filter_subset _ _))

theorem extraRow_avoids_center {α : Type*} [DecidableEq α]
    {H D : Hypergraph α} {x : α}
    (hxH : ∀ Q ∈ H, x ∉ Q)
    (hPairCount : (pairRows H).card = 3)
    (hBaseD : forcedBase H x ⊆ D)
    (hDegreeD : MaxDegreeAtMost D 3)
    {R : Row α} (hRD : R ∈ D) (hRbase : R ∉ forcedBase H x) :
    x ∉ R := by
  intro hxR
  have hInsertD : insert R (forcedBase H x) ⊆ D := Finset.insert_subset hRD hBaseD
  have hInsertDegree : degree (insert R (forcedBase H x)) x = 4 := by
    rw [degree_insert_of_notMem hRbase hxR, degree_forcedBase_center hxH, hPairCount]
  have hle := degree_mono hInsertD x
  have hupper := hDegreeD x
  omega

theorem extraRow_contains_pair {α : Type*} [Fintype α] [DecidableEq α]
    {K D : Hypergraph α} {x : α}
    (hD : IsClutter D)
    (hBaseD : forcedBase (blocker K) x ⊆ D)
    (hKD : K ⊆ blocker D)
    {R : Row α} (hRD : R ∈ D)
    (hRbase : R ∉ forcedBase (blocker K) x) :
    ∃ Q ∈ blocker K, Q.card = 2 ∧ Q ⊆ R := by
  have hRtrans : IsTransversal K R := by
    intro A hAK
    obtain ⟨y, hyA, hyR⟩ := (mem_blocker.mp (hKD hAK)).prop R hRD
    exact ⟨y, hyR, hyA⟩
  obtain ⟨Q, hQR, hQmin⟩ := exists_minimalTransversal_subset hRtrans
  have hQblocker : Q ∈ blocker K := mem_blocker.mpr hQmin
  refine ⟨Q, hQblocker, ?_, hQR⟩
  by_contra hQcard
  have hLift : liftPairRow x Q = Q := by simp [liftPairRow, hQcard]
  have hQD : Q ∈ D := by
    apply hBaseD
    simpa [hLift] using mem_forcedBase_lift (x := x) hQblocker
  have hEq : Q = R := hD hQD hRD hQR
  have hQbase : Q ∈ forcedBase (blocker K) x := by
    simpa [hLift] using mem_forcedBase_lift (x := x) hQblocker
  exact hRbase (hEq ▸ hQbase)

theorem extraRow_endpoint_contradiction {α : Type*} [DecidableEq α]
    {H D : Hypergraph α} {x : α}
    (hxH : ∀ Q ∈ H, x ∉ Q)
    (hBaseD : forcedBase H x ⊆ D)
    (hDegreeD : MaxDegreeAtMost D 3)
    {R Q : Row α}
    (hRD : R ∈ D)
    (hRbase : R ∉ forcedBase H x)
    (hQH : Q ∈ H)
    (hQR : Q ⊆ R)
    (hEndpoint : ∃ y ∈ Q, degree H y = 3) :
    False := by
  obtain ⟨y, hyQ, hyDegree⟩ := hEndpoint
  have hyx : y ≠ x := fun hyx ↦ hxH Q hQH (hyx ▸ hyQ)
  have hyR : y ∈ R := hQR hyQ
  have hInsertD : insert R (forcedBase H x) ⊆ D := Finset.insert_subset hRD hBaseD
  have hInsertDegree : degree (insert R (forcedBase H x)) y = 4 := by
    rw [degree_insert_of_notMem hRbase hyR, degree_forcedBase_eq hyx hxH, hyDegree]
  have hle := degree_mono hInsertD y
  have hupper := hDegreeD y
  omega

theorem kernelCompletion_blocker_maxDegree {α : Type*}
    [Fintype α] [DecidableEq α] {K D : Hypergraph α} {x : α}
    (hxK : ∀ E ∈ K, x ∉ E)
    (hCompletion : IsKernelCompletion K x D) :
    MaxDegreeAtMost (blocker K) 3 := by
  obtain ⟨-, -, -, hDdegree, -, hBaseD, -⟩ := hCompletion
  have hxH : ∀ Q ∈ blocker K, x ∉ Q := blocker_rows_avoid_inactive hxK
  intro y
  by_cases hyx : y = x
  · subst y
    have hFilterEmpty :
        (blocker K).filter (fun Q ↦ x ∈ Q) = ∅ := by
      ext Q
      constructor
      · intro h
        obtain ⟨hQ, hxQ⟩ := Finset.mem_filter.mp h
        exact (hxH Q hQ hxQ).elim
      · intro h
        simp at h
    rw [degree, hFilterEmpty]
    simp
  · rw [← degree_forcedBase_eq hyx hxH]
    exact (degree_mono hBaseD y).trans (hDdegree y)

theorem no_kernel_completion_of_locked_dependencies {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hResidualLemma2 : ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  rintro ⟨D, hCompletion⟩
  have hHdegree := kernelCompletion_blocker_maxDegree hxK hCompletion
  obtain ⟨hDclutter, hDcard, -, hDdegree, hKdegree, hBaseD, hKD⟩ := hCompletion
  have hxH : ∀ Q ∈ blocker K, x ∉ Q := blocker_rows_avoid_inactive hxK
  have hHcardLower : 3 ≤ (blocker K).card := by
    have hKpositive : 0 < K.card := by omega
    obtain ⟨A, hAK⟩ := Finset.card_pos.mp hKpositive
    have hAdual : A ∈ blocker (blocker K) := by
      rw [blocker_involution hK]
      exact hAK
    have hAcard : 3 ≤ A.card := hKrows A hAK
    have hAle : A.card ≤ (blocker K).card :=
      minimalTransversal_card_le_rows (mem_blocker.mp hAdual)
    omega
  have hHcardSix : 6 ≤ (blocker K).card := by
    by_contra hnot
    have hupper : (blocker K).card ≤ 5 := by omega
    have hDualRows : RowsCardAtLeast (blocker (blocker K)) 3 := by
      rw [blocker_involution hK]
      exact hKrows
    have hsix := hResidualLemma2 (blocker K) (blocker_isClutter K)
      hHcardLower hupper hHrows (by omega) hDualRows
    rw [blocker_involution hK, hKcard] at hsix
    omega
  have hcases :
      (blocker K).card = 6 ∨ (blocker K).card = 7 ∨ (blocker K).card = 8 := by
    omega
  rcases hcases with hcard | hcard | hcard
  · have hBaseCard : (forcedBase (blocker K) x).card = 6 := by
      rw [forcedBase_card hxH, hcard]
    have hlt : (forcedBase (blocker K) x).card < D.card := by omega
    obtain ⟨R, hRD, hRbase⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have _hxR := extraRow_avoids_center hxH hHpairs hBaseD hDdegree hRD hRbase
    obtain ⟨Q, hQH, hQpair, hQR⟩ :=
      extraRow_contains_pair hDclutter hBaseD hKD hRD hRbase
    exact extraRow_endpoint_contradiction hxH hBaseD hDdegree hRD hRbase hQH hQR
      (hEndpoint (Or.inl hcard) Q hQH hQpair)
  · have hBaseCard : (forcedBase (blocker K) x).card = 7 := by
      rw [forcedBase_card hxH, hcard]
    have hlt : (forcedBase (blocker K) x).card < D.card := by omega
    obtain ⟨R, hRD, hRbase⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have _hxR := extraRow_avoids_center hxH hHpairs hBaseD hDdegree hRD hRbase
    obtain ⟨Q, hQH, hQpair, hQR⟩ :=
      extraRow_contains_pair hDclutter hBaseD hKD hRD hRbase
    exact extraRow_endpoint_contradiction hxH hBaseD hDdegree hRD hRbase hQH hQR
      (hEndpoint (Or.inr hcard) Q hQH hQpair)
  · exact fiveRow_eight_blocker_impossible hK hKcard hKrows hKdegree hcard
      hHrows hHdegree hHpairs

theorem no_kernel_completion_of_four_five_endpoint_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hFour : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  exact no_kernel_completion_of_locked_dependencies hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper
    (residualLemma2_of_four_and_five_row_cases hFour hFive) hEndpoint

theorem no_kernel_completion_of_four_pair_five_endpoint_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hFourPair : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      (∃ E ∈ R, E.card = 2) →
      6 ≤ (blocker R).card)
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  exact no_kernel_completion_of_locked_dependencies hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper
    (residualLemma2_of_four_pair_and_five_row_cases hFourPair hFive) hEndpoint

theorem no_kernel_completion_of_five_endpoint_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  exact no_kernel_completion_of_locked_dependencies hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper
    (residualLemma2_of_five_row_case hFive) hEndpoint

theorem no_kernel_completion_of_five_large_endpoint_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hFiveLarge : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  exact no_kernel_completion_of_locked_dependencies hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper
    (residualLemma2_of_five_large_row_case hFiveLarge) hEndpoint

theorem no_kernel_completion_of_endpoint_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8)
    (hEndpoint : (blocker K).card = 6 ∨ (blocker K).card = 7 →
      ∀ Q ∈ blocker K, Q.card = 2 → ∃ y ∈ Q, degree (blocker K) y = 3) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  exact no_kernel_completion_of_locked_dependencies hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper residualLemma2 hEndpoint

theorem kernelCompletion_pair_endpoint {α : Type*}
    [Fintype α] [DecidableEq α] {K D : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hCompletion : IsKernelCompletion K x D)
    (hHcard : (blocker K).card = 6 ∨ (blocker K).card = 7) :
    ∀ Q ∈ blocker K, Q.card = 2 →
      ∃ y ∈ Q, degree (blocker K) y = 3 := by
  have hHdegree := kernelCompletion_blocker_maxDegree hxK hCompletion
  have hDualRows : RowsCardAtLeast (blocker (blocker K)) 3 := by
    rw [blocker_involution hK]
    exact hKrows
  have hDualCard : (blocker (blocker K)).card = 5 := by
    rw [blocker_involution hK, hKcard]
  apply pairRow_has_degree_three_endpoint_of_five_blockers
    (blocker_isClutter K) (by rcases hHcard with h | h <;> omega) hHrows
      (by omega) hDualRows hHdegree hDualCard

theorem no_kernel_completion_of_eight {α : Type*}
    [Fintype α] [DecidableEq α] {K : Hypergraph α} {x : α}
    (hK : IsClutter K)
    (hKcard : K.card = 5)
    (hKrows : RowsCardAtLeast K 3)
    (hxK : ∀ E ∈ K, x ∉ E)
    (hHrows : RowsCardAtLeast (blocker K) 2)
    (hHpairs : (pairRows (blocker K)).card = 3)
    (hHcardUpper : (blocker K).card ≤ 8) :
    ¬ ∃ D, IsKernelCompletion K x D := by
  intro hExists
  obtain ⟨D, hCompletion⟩ := hExists
  have hEndpoint := kernelCompletion_pair_endpoint hK hKcard hKrows hxK
    hHrows hHpairs hCompletion
  exact (no_kernel_completion_of_endpoint_eight hK hKcard hKrows hxK
    hHrows hHpairs hHcardUpper hEndpoint) ⟨D, hCompletion⟩

end AiMathLab.P0054.G413
