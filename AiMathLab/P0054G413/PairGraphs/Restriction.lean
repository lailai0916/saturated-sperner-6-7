import AiMathLab.P0054G413.PairGraphs.P4

namespace AiMathLab.P0054.G413

def restrictRows {α : Type*} [DecidableEq α]
    (K : Hypergraph α) (V : Row α) : Hypergraph α :=
  K.image fun R ↦ R ∩ V

@[simp]
theorem mem_restrictRows {α : Type*} [DecidableEq α]
    {K : Hypergraph α} {V P : Row α} :
    P ∈ restrictRows K V ↔ ∃ R ∈ K, R ∩ V = P := by
  simp [restrictRows]

theorem blocker_restrictRows_lift {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {V T : Row α}
    (hTV : T ⊆ V) (hT : T ∈ blocker (restrictRows K V)) :
    T ∈ blocker K := by
  apply mem_blocker.mpr
  have hTransversal : IsTransversal K T := by
    intro R hRK
    have hProjection : R ∩ V ∈ restrictRows K V :=
      mem_restrictRows.mpr ⟨R, hRK, rfl⟩
    obtain ⟨x, hxT, hxProjection⟩ := (mem_blocker.mp hT).prop _ hProjection
    exact ⟨x, hxT, (Finset.mem_inter.mp hxProjection).1⟩
  apply hTransversal.minimal_of_privateRows
  intro x hxT
  obtain ⟨P, hPPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
  obtain ⟨R, hRK, hProjection⟩ := mem_restrictRows.mp hPPrivate.1
  refine ⟨R, hRK, hxT, ?_, ?_⟩
  · have hxP : x ∈ P := hPPrivate.2.2.1
    rw [← hProjection] at hxP
    exact (Finset.mem_inter.mp hxP).1
  · intro y hyT hyR
    have hyV : y ∈ V := hTV hyT
    have hyP : y ∈ P := by
      rw [← hProjection]
      exact Finset.mem_inter.mpr ⟨hyR, hyV⟩
    exact hPPrivate.2.2.2 hyT hyP

theorem blocker_degree_ge_of_restriction {α : Type*}
    [Fintype α] [DecidableEq α]
    {K H : Hypergraph α} {V : Row α} {x : α}
    (hLift : ∀ T ∈ blocker (restrictRows K V), T ∈ H)
    (hDegree : 4 ≤ degree (blocker (restrictRows K V)) x) :
    4 ≤ degree H x := by
  apply hDegree.trans
  apply Finset.card_le_card
  intro T hT
  obtain ⟨hTb, hxT⟩ := Finset.mem_filter.mp hT
  exact Finset.mem_filter.mpr ⟨hLift T hTb, hxT⟩

theorem blocker_replace_of_equal_support {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a q : α} {T : Row α}
    (haq : a ≠ q)
    (hSupport : pointSupport K a = pointSupport K q)
    (hT : T ∈ blocker K) (haT : a ∈ T) (hqT : q ∉ T) :
    insert q (T.erase a) ∈ blocker K := by
  have hSupportIff (R : Row α) (hRK : R ∈ K) : a ∈ R ↔ q ∈ R := by
    constructor
    · intro haR
      have hRa : R ∈ pointSupport K a := mem_pointSupport.mpr ⟨hRK, haR⟩
      exact (mem_pointSupport.mp (hSupport ▸ hRa)).2
    · intro hqR
      have hRq : R ∈ pointSupport K q := mem_pointSupport.mpr ⟨hRK, hqR⟩
      exact (mem_pointSupport.mp (hSupport.symm ▸ hRq)).2
  apply mem_blocker.mpr
  have hTransversal : IsTransversal K (insert q (T.erase a)) := by
    intro R hRK
    obtain ⟨x, hxT, hxR⟩ := (mem_blocker.mp hT).prop R hRK
    by_cases hxa : x = a
    · subst x
      exact ⟨q, by simp, (hSupportIff R hRK).mp hxR⟩
    · exact ⟨x, by simp [Finset.mem_erase.mpr ⟨hxa, hxT⟩], hxR⟩
  apply hTransversal.minimal_of_privateRows
  intro x hxSwap
  simp only [Finset.mem_insert] at hxSwap
  rcases hxSwap with hxq | hxErase
  · subst x
    obtain ⟨R, hRPrivate⟩ := (mem_blocker.mp hT).exists_privateRow haT
    refine ⟨R, hRPrivate.1, by simp, (hSupportIff R hRPrivate.1).mp hRPrivate.2.2.1, ?_⟩
    intro y hySwap hyR
    simp only [Finset.mem_insert] at hySwap
    rcases hySwap with hyq | hyErase
    · exact hyq
    · obtain ⟨hya, hyT⟩ := Finset.mem_erase.mp hyErase
      exact (hya (hRPrivate.2.2.2 hyT hyR)).elim
  · obtain ⟨hxa, hxT⟩ := Finset.mem_erase.mp hxErase
    obtain ⟨R, hRPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
    have haR : a ∉ R := by
      intro haR
      exact hxa (hRPrivate.2.2.2 haT haR).symm
    have hqR : q ∉ R := fun hqR ↦ haR ((hSupportIff R hRPrivate.1).mpr hqR)
    refine ⟨R, hRPrivate.1, by simp [hxErase], hRPrivate.2.2.1, ?_⟩
    intro y hySwap hyR
    simp only [Finset.mem_insert] at hySwap
    rcases hySwap with hyq | hyErase
    · exact (hqR (hyq ▸ hyR)).elim
    · exact hRPrivate.2.2.2 (Finset.mem_of_mem_erase hyErase) hyR

theorem twin_endpoint_amplifier {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a q t : α} {S T : Row α}
    (haq : a ≠ q) (hat : a ≠ t)
    (hSupport : pointSupport K a = pointSupport K q)
    (hS : S ∈ blocker K) (hT : T ∈ blocker K)
    (hST : S ≠ T) (haS : a ∈ S) (haT : a ∈ T)
    (hqS : q ∉ S) (hqT : q ∉ T) (htS : t ∈ S) (htT : t ∈ T) :
    4 ≤ degree (blocker K) t := by
  let S' := insert q (S.erase a)
  let T' := insert q (T.erase a)
  have hS' : S' ∈ blocker K :=
    blocker_replace_of_equal_support haq hSupport hS haS hqS
  have hT' : T' ∈ blocker K :=
    blocker_replace_of_equal_support haq hSupport hT haT hqT
  have haS' : a ∉ S' := by simp [S', haq, hqS]
  have haT' : a ∉ T' := by simp [T', haq, hqT]
  have hqS' : q ∈ S' := by simp [S']
  have hqT' : q ∈ T' := by simp [T']
  have htS' : t ∈ S' := by simp [S', hat.symm, htS]
  have htT' : t ∈ T' := by simp [T', hat.symm, htT]
  have hSS' : S ≠ S' := fun hEq ↦ hqS (hEq ▸ hqS')
  have hST' : S ≠ T' := fun hEq ↦ hqS (hEq ▸ hqT')
  have hTS' : T ≠ S' := fun hEq ↦ hqT (hEq ▸ hqS')
  have hTT' : T ≠ T' := fun hEq ↦ hqT (hEq ▸ hqT')
  have hS'T' : S' ≠ T' := by
    intro hEq
    have hErase := congrArg (fun U : Row α ↦ U.erase q) hEq
    have hSErase : S'.erase q = S.erase a := by simp [S', haq.symm, hqS]
    have hTErase : T'.erase q = T.erase a := by simp [T', haq.symm, hqT]
    have hErasedEq : S.erase a = T.erase a := hSErase ▸ hTErase ▸ hErase
    have hEqST := congrArg (insert a) hErasedEq
    rw [Finset.insert_erase haS, Finset.insert_erase haT] at hEqST
    exact hST hEqST
  let Q : Hypergraph α := {S, T, S', T'}
  have hQcard : Q.card = 4 := by
    simp [Q, hST, hSS', hST', hTS', hTT', hS'T']
  have hQSubset : Q ⊆ pointSupport (blocker K) t := by
    intro U hU
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl
    · exact mem_pointSupport.mpr ⟨hS, htS⟩
    · exact mem_pointSupport.mpr ⟨hT, htT⟩
    · exact mem_pointSupport.mpr ⟨hS', htS'⟩
    · exact mem_pointSupport.mpr ⟨hT', htT'⟩
  have hCard := Finset.card_le_card hQSubset
  simpa [hQcard, pointSupport_card] using hCard

end AiMathLab.P0054.G413
