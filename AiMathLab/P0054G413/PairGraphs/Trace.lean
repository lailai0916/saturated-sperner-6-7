import AiMathLab.P0054G413.PairGraphs.Shapes

namespace AiMathLab.P0054.G413

def IsGoodTraceBlocker {α : Type*} [DecidableEq α]
    (a b : α) (C E T : Row α) : Prop :=
  (a ∈ T → Disjoint T E) ∧ (b ∈ T → Disjoint T C)

def HasTraceA {α : Type*} [DecidableEq α] (a b : α) (R : Row α) : Prop :=
  a ∈ R ∧ b ∈ R

def HasTraceC {α : Type*} [DecidableEq α]
    (a b : α) (C R : Row α) : Prop :=
  a ∈ R ∧ b ∉ R ∧ C ⊆ R

def HasTraceE {α : Type*} [DecidableEq α]
    (a b : α) (E R : Row α) : Prop :=
  a ∉ R ∧ b ∈ R ∧ E ⊆ R

def HasTraceN {α : Type*} [DecidableEq α]
    (a b : α) (C E R : Row α) : Prop :=
  a ∉ R ∧ b ∉ R ∧ C ⊆ R ∧ E ⊆ R

theorem goodTraceBlocker_mono {α : Type*} [DecidableEq α]
    {a b : α} {C E S T : Row α}
    (hGood : IsGoodTraceBlocker a b C E T) (hST : S ⊆ T) :
    IsGoodTraceBlocker a b C E S := by
  constructor
  · intro haS
    exact (hGood.1 (hST haS)).mono hST Finset.Subset.rfl
  · intro hbS
    exact (hGood.2 (hST hbS)).mono hST Finset.Subset.rfl

theorem exists_good_blocker_subset {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E T : Row α}
    (hTransversal : IsTransversal Z T)
    (hGood : IsGoodTraceBlocker a b C E T) :
    ∃ S ∈ blocker Z, S ⊆ T ∧ IsGoodTraceBlocker a b C E S := by
  obtain ⟨S, hST, hS⟩ := exists_minimalTransversal_subset hTransversal
  exact ⟨S, mem_blocker.mpr hS, hST, goodTraceBlocker_mono hGood hST⟩

theorem two_good_blockers_of_transversals {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E U V : Row α}
    (hU : IsTransversal Z U) (hV : IsTransversal Z V)
    (hUGood : IsGoodTraceBlocker a b C E U)
    (hVGood : IsGoodTraceBlocker a b C E V)
    (hInter : ¬ IsTransversal Z (U ∩ V)) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  obtain ⟨S, hSb, hSU, hSGood⟩ := exists_good_blocker_subset hU hUGood
  obtain ⟨T, hTb, hTV, hTGood⟩ := exists_good_blocker_subset hV hVGood
  have hST : S ≠ T := by
    intro hEq
    subst T
    apply hInter
    apply (mem_blocker.mp hSb).prop.mono
    intro x hxS
    exact Finset.mem_inter.mpr ⟨hSU hxS, hTV hxS⟩
  exact ⟨S, T, hSb, hTb, hST, hSGood, hTGood⟩

theorem not_transversal_of_subset_singleton_of_degree_le_two {α : Type*}
    [DecidableEq α] {Z : Hypergraph α} {x : α} {T : Row α}
    (hZcard : Z.card = 3) (hDegree : degree Z x ≤ 2) (hT : T ⊆ {x}) :
    ¬ IsTransversal Z T := by
  intro hTransversal
  have hxAll : ∀ R ∈ Z, x ∈ R := by
    intro R hR
    obtain ⟨y, hyT, hyR⟩ := hTransversal R hR
    have hyx : y = x := by simpa using hT hyT
    exact hyx ▸ hyR
  have hFilter : Z.filter (fun R ↦ x ∈ R) = Z := Finset.filter_eq_self.mpr hxAll
  have hDegreeEq : degree Z x = 3 := by rw [degree, hFilter, hZcard]
  omega

theorem degree_ge_two_of_two_rows {α : Type*} [DecidableEq α]
    {Z : Hypergraph α} {R S : Row α} {x : α}
    (hR : R ∈ Z) (hS : S ∈ Z) (hRS : R ≠ S) (hxR : x ∈ R) (hxS : x ∈ S) :
    2 ≤ degree Z x := by
  have hPairSubset : ({R, S} : Hypergraph α) ⊆ Z.filter (fun T ↦ x ∈ T) := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hR, hxR⟩
    · exact Finset.mem_filter.mpr ⟨hS, hxS⟩
  have hPairCard : ({R, S} : Hypergraph α).card = 2 := by simp [hRS]
  simpa [degree, hPairCard] using Finset.card_le_card hPairSubset

theorem degree_ge_three_of_three_rows {α : Type*} [DecidableEq α]
    {Z : Hypergraph α} {R S T : Row α} {x : α}
    (hR : R ∈ Z) (hS : S ∈ Z) (hT : T ∈ Z)
    (hRS : R ≠ S) (hRT : R ≠ T) (hST : S ≠ T)
    (hxR : x ∈ R) (hxS : x ∈ S) (hxT : x ∈ T) :
    3 ≤ degree Z x := by
  have hTripleSubset : ({R, S, T} : Hypergraph α) ⊆ Z.filter (fun U ↦ x ∈ U) := by
    intro U hU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hR, hxR⟩
    · exact Finset.mem_filter.mpr ⟨hS, hxS⟩
    · exact Finset.mem_filter.mpr ⟨hT, hxT⟩
  have hTripleCard : ({R, S, T} : Hypergraph α).card = 3 := by
    simp [hRS, hRT, hST]
  simpa [degree, hTripleCard] using Finset.card_le_card hTripleSubset

theorem row_has_trace {α : Type*} [DecidableEq α]
    {a b : α} {C E R : Row α}
    (hC : b ∈ R ∨ C ⊆ R) (hE : a ∈ R ∨ E ⊆ R) :
    HasTraceA a b R ∨ HasTraceC a b C R ∨
      HasTraceE a b E R ∨ HasTraceN a b C E R := by
  by_cases haR : a ∈ R
  · by_cases hbR : b ∈ R
    · exact Or.inl ⟨haR, hbR⟩
    · exact Or.inr (Or.inl ⟨haR, hbR, hC.resolve_left hbR⟩)
  · by_cases hbR : b ∈ R
    · exact Or.inr (Or.inr (Or.inl ⟨haR, hbR, hE.resolve_left haR⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨haR, hbR, hC.resolve_left hbR, hE.resolve_left haR⟩))

theorem trace_A_A_N_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {R₁ R₂ R₃ : Row α}
    {a b c d : α} {C E : Row α}
    (hZcard : Z.card = 3) (hZ : Z = {R₁, R₂, R₃})
    (hA₁ : HasTraceA a b R₁) (hA₂ : HasTraceA a b R₂)
    (hN₃ : HasTraceN a b C E R₃)
    (hcC : c ∈ C) (hdC : d ∈ C)
    (haE : a ∉ E) (hcE : c ∉ E) (hdE : d ∉ E)
    (hab : a ≠ b) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haDegree : degree Z a ≤ 2) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have hU : IsTransversal Z {a, c} := by
    intro R hR
    rw [hZ] at hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨a, by simp, hA₁.1⟩
    · exact ⟨a, by simp, hA₂.1⟩
    · exact ⟨c, by simp, hN₃.2.2.1 hcC⟩
  have hV : IsTransversal Z {a, d} := by
    intro R hR
    rw [hZ] at hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨a, by simp, hA₁.1⟩
    · exact ⟨a, by simp, hA₂.1⟩
    · exact ⟨d, by simp, hN₃.2.2.1 hdC⟩
  have hUGood : IsGoodTraceBlocker a b C E {a, c} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haE, hcE, hab.symm, hbc]
  have hVGood : IsGoodTraceBlocker a b C E {a, d} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haE, hdE, hab.symm, hbd]
  have hSubset : ({a, c} : Row α) ∩ {a, d} ⊆ {a} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxa | hxc, hxa' | hxd⟩
    · exact hxa
    · exact hxa
    · exact hxa'
    · exact (hcd (hxc.symm.trans hxd)).elim
  exact two_good_blockers_of_transversals hU hV hUGood hVGood
    (not_transversal_of_subset_singleton_of_degree_le_two
      hZcard haDegree hSubset)

theorem endpoint_or_pair_cover_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b c d : α} {C E : Row α}
    (hZcard : Z.card = 3)
    (hCover : ∀ R ∈ Z, a ∈ R ∨ C ⊆ R)
    (hcC : c ∈ C) (hdC : d ∈ C)
    (haE : a ∉ E) (hcE : c ∉ E) (hdE : d ∉ E)
    (hba : b ≠ a) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haDegree : degree Z a ≤ 2) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have hU : IsTransversal Z {a, c} := by
    intro R hR
    rcases hCover R hR with haR | hCR
    · exact ⟨a, by simp, haR⟩
    · exact ⟨c, by simp, hCR hcC⟩
  have hV : IsTransversal Z {a, d} := by
    intro R hR
    rcases hCover R hR with haR | hCR
    · exact ⟨a, by simp, haR⟩
    · exact ⟨d, by simp, hCR hdC⟩
  have hUGood : IsGoodTraceBlocker a b C E {a, c} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haE, hcE, hba, hbc]
  have hVGood : IsGoodTraceBlocker a b C E {a, d} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haE, hdE, hba, hbd]
  have hSubset : ({a, c} : Row α) ∩ {a, d} ⊆ {a} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxa | hxc, hxa' | hxd⟩
    · exact hxa
    · exact hxa
    · exact hxa'
    · exact (hcd (hxc.symm.trans hxd)).elim
  exact two_good_blockers_of_transversals hU hV hUGood hVGood
    (not_transversal_of_subset_singleton_of_degree_le_two
      hZcard haDegree hSubset)

theorem endpoint_cross_cover_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b c e : α} {C E : Row α}
    (hZcard : Z.card = 3)
    (hEndpointCover : ∀ R ∈ Z, a ∈ R ∨ b ∈ R)
    (hCrossCover : ∀ R ∈ Z, c ∈ R ∨ e ∈ R)
    (haC : a ∉ C) (hbC : b ∉ C) (haE : a ∉ E) (hbE : b ∉ E)
    (hca : c ≠ a) (hcb : c ≠ b) (hea : e ≠ a) (heb : e ≠ b)
    (hDegree : degree Z a ≤ 2) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have hU : IsTransversal Z {a, b} := by
    intro R hR
    rcases hEndpointCover R hR with haR | hbR
    · exact ⟨a, by simp, haR⟩
    · exact ⟨b, by simp, hbR⟩
  have hV : IsTransversal Z {c, e} := by
    intro R hR
    rcases hCrossCover R hR with hcR | heR
    · exact ⟨c, by simp, hcR⟩
    · exact ⟨e, by simp, heR⟩
  have hUGood : IsGoodTraceBlocker a b C E {a, b} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haC, hbC, haE, hbE]
  have hVGood : IsGoodTraceBlocker a b C E {c, e} := by
    simp [IsGoodTraceBlocker, hca.symm, hcb.symm, hea.symm, heb.symm]
  have hSubset : ({a, b} : Row α) ∩ {c, e} ⊆ {a} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxa | hxb, hxc | hxe⟩
    · exact (hca (hxc.symm.trans hxa)).elim
    · exact (hea (hxe.symm.trans hxa)).elim
    · exact (hcb (hxc.symm.trans hxb)).elim
    · exact (heb (hxe.symm.trans hxb)).elim
  exact two_good_blockers_of_transversals hU hV hUGood hVGood
    (not_transversal_of_subset_singleton_of_degree_le_two
      hZcard hDegree hSubset)

theorem pair_cross_cover_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b c e f : α} {C E : Row α}
    (hZcard : Z.card = 3)
    (hFirstCover : ∀ R ∈ Z, c ∈ R ∨ e ∈ R)
    (hSecondCover : ∀ R ∈ Z, c ∈ R ∨ f ∈ R)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hea : e ≠ a) (heb : e ≠ b) (hfa : f ≠ a) (hfb : f ≠ b)
    (hef : e ≠ f) (hcDegree : degree Z c ≤ 2) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have hU : IsTransversal Z {c, e} := by
    intro R hR
    rcases hFirstCover R hR with hcR | heR
    · exact ⟨c, by simp, hcR⟩
    · exact ⟨e, by simp, heR⟩
  have hV : IsTransversal Z {c, f} := by
    intro R hR
    rcases hSecondCover R hR with hcR | hfR
    · exact ⟨c, by simp, hcR⟩
    · exact ⟨f, by simp, hfR⟩
  have hUGood : IsGoodTraceBlocker a b C E {c, e} := by
    simp [IsGoodTraceBlocker, hca.symm, hcb.symm, hea.symm, heb.symm]
  have hVGood : IsGoodTraceBlocker a b C E {c, f} := by
    simp [IsGoodTraceBlocker, hca.symm, hcb.symm, hfa.symm, hfb.symm]
  have hSubset : ({c, e} : Row α) ∩ {c, f} ⊆ {c} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxc | hxe, hxc' | hxf⟩
    · exact hxc
    · exact hxc
    · exact hxc'
    · exact (hef (hxe.symm.trans hxf)).elim
  exact two_good_blockers_of_transversals hU hV hUGood hVGood
    (not_transversal_of_subset_singleton_of_degree_le_two
      hZcard hcDegree hSubset)

theorem trace_A_C_E_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {RA RC RE : Row α}
    {a b c e : α} {C E : Row α}
    (hZcard : Z.card = 3) (hZ : Z = {RA, RC, RE})
    (hRows : RowsCardAtLeast Z 3)
    (hA : HasTraceA a b RA)
    (hC : HasTraceC a b C RC)
    (hE : HasTraceE a b E RE)
    (hcC : c ∈ C) (heE : e ∈ E)
    (haC : a ∉ C) (hbC : b ∉ C) (heC : e ∉ C)
    (haE : a ∉ E) (hbE : b ∉ E) (hcE : c ∉ E)
    (haDegree : degree Z a ≤ 2) (hbDegree : degree Z b ≤ 2) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have hab : a ≠ b := fun hab ↦ hC.2.1 (hab ▸ hC.1)
  have hPairCard : ({a, b} : Row α).card = 2 := by simp [hab]
  have hPairLt : ({a, b} : Row α).card < RA.card := by
    have hRAZ : RA ∈ Z := by simp [hZ]
    have hRACard := hRows RA hRAZ
    omega
  obtain ⟨z, hzRA, hzPair⟩ := Finset.exists_mem_notMem_of_card_lt_card hPairLt
  have hza : z ≠ a := by
    intro hza
    exact hzPair (hza ▸ by simp)
  have hzb : z ≠ b := by
    intro hzb
    exact hzPair (hzb ▸ by simp)
  have hca : c ≠ a := fun hca ↦ haC (hca ▸ hcC)
  have hcb : c ≠ b := fun hcb ↦ hbC (hcb ▸ hcC)
  have hea : e ≠ a := fun hea ↦ haE (hea ▸ heE)
  have heb : e ≠ b := fun heb ↦ hbE (heb ▸ heE)
  have hce : c ≠ e := fun hce ↦ hcE (hce ▸ heE)
  have hU : IsTransversal Z {a, b} := by
    intro R hR
    rw [hZ] at hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨a, by simp, hA.1⟩
    · exact ⟨a, by simp, hC.1⟩
    · exact ⟨b, by simp, hE.2.1⟩
  have hUGood : IsGoodTraceBlocker a b C E {a, b} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haC, hbC, haE, hbE]
  have finish {V : Row α} {x : α}
      (hV : IsTransversal Z V)
      (hVGood : IsGoodTraceBlocker a b C E V)
      (hDegree : degree Z x ≤ 2)
      (hInterSubset : ({a, b} : Row α) ∩ V ⊆ {x}) :
      ∃ S T,
        S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
        IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
    exact two_good_blockers_of_transversals hU hV hUGood hVGood
      (not_transversal_of_subset_singleton_of_degree_le_two
        hZcard hDegree hInterSubset)
  by_cases hzC : z ∈ C
  · have hV : IsTransversal Z {z, e} := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact ⟨z, by simp, hzRA⟩
      · exact ⟨z, by simp, hC.2.2 hzC⟩
      · exact ⟨e, by simp, hE.2.2 heE⟩
    have hVGood : IsGoodTraceBlocker a b C E {z, e} := by
      simp [IsGoodTraceBlocker, hza.symm, hzb.symm, hea.symm, heb.symm]
    apply finish hV hVGood haDegree
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxa | hxb, hxz | hxe⟩
    · exact (hza (hxz.symm.trans hxa)).elim
    · exact (hea (hxe.symm.trans hxa)).elim
    · exact (hzb (hxz.symm.trans hxb)).elim
    · exact (heb (hxe.symm.trans hxb)).elim
  · by_cases hzE : z ∈ E
    · have hV : IsTransversal Z {c, z} := by
        intro R hR
        rw [hZ] at hR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hR
        rcases hR with rfl | rfl | rfl
        · exact ⟨z, by simp, hzRA⟩
        · exact ⟨c, by simp, hC.2.2 hcC⟩
        · exact ⟨z, by simp, hE.2.2 hzE⟩
      have hVGood : IsGoodTraceBlocker a b C E {c, z} := by
        simp [IsGoodTraceBlocker, hca.symm, hcb.symm, hza.symm, hzb.symm]
      apply finish hV hVGood haDegree
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_singleton]
      rcases hx with ⟨hxa | hxb, hxc | hxz⟩
      · exact (hca (hxc.symm.trans hxa)).elim
      · exact (hza (hxz.symm.trans hxa)).elim
      · exact (hcb (hxc.symm.trans hxb)).elim
      · exact (hzb (hxz.symm.trans hxb)).elim
    · by_cases hzRC : z ∈ RC
      · by_cases hzRE : z ∈ RE
        · have hV : IsTransversal Z {z} := by
            intro R hR
            rw [hZ] at hR
            simp only [Finset.mem_insert, Finset.mem_singleton] at hR
            rcases hR with rfl | rfl | rfl
            · exact ⟨z, by simp, hzRA⟩
            · exact ⟨z, by simp, hzRC⟩
            · exact ⟨z, by simp, hzRE⟩
          have hVGood : IsGoodTraceBlocker a b C E {z} := by
            simp [IsGoodTraceBlocker, hza.symm, hzb.symm]
          apply finish hV hVGood haDegree
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with ⟨hxa | hxb, hxz⟩
          · exact (hza (hxz.symm.trans hxa)).elim
          · exact (hzb (hxz.symm.trans hxb)).elim
        · have hV : IsTransversal Z {z, b} := by
            intro R hR
            rw [hZ] at hR
            simp only [Finset.mem_insert, Finset.mem_singleton] at hR
            rcases hR with rfl | rfl | rfl
            · exact ⟨z, by simp, hzRA⟩
            · exact ⟨z, by simp, hzRC⟩
            · exact ⟨b, by simp, hE.2.1⟩
          have hVGood : IsGoodTraceBlocker a b C E {z, b} := by
            simp [IsGoodTraceBlocker, Finset.disjoint_left, hza.symm, hzb,
              hzC, hbC, hab]
          apply finish hV hVGood hbDegree
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_singleton]
          rcases hx with ⟨hxa | hxb, hxz | hxb'⟩
          · exact (hza (hxz.symm.trans hxa)).elim
          · exact (hab (hxb'.symm.trans hxa).symm).elim
          · exact (hzb (hxz.symm.trans hxb)).elim
          · exact hxb
      · by_cases hzRE : z ∈ RE
        · have hV : IsTransversal Z {z, a} := by
            intro R hR
            rw [hZ] at hR
            simp only [Finset.mem_insert, Finset.mem_singleton] at hR
            rcases hR with rfl | rfl | rfl
            · exact ⟨z, by simp, hzRA⟩
            · exact ⟨a, by simp, hC.1⟩
            · exact ⟨z, by simp, hzRE⟩
          have hVGood : IsGoodTraceBlocker a b C E {z, a} := by
            simp [IsGoodTraceBlocker, Finset.disjoint_left, hza, hzb.symm,
              hzE, haE, hab.symm]
          apply finish hV hVGood haDegree
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_singleton]
          rcases hx with ⟨hxa | hxb, hxz | hxa'⟩
          · exact hxa
          · exact hxa
          · exact (hzb (hxz.symm.trans hxb)).elim
          · exact (hab (hxa'.symm.trans hxb)).elim
        · have hV : IsTransversal Z {z, c, e} := by
            intro R hR
            rw [hZ] at hR
            simp only [Finset.mem_insert, Finset.mem_singleton] at hR
            rcases hR with rfl | rfl | rfl
            · exact ⟨z, by simp, hzRA⟩
            · exact ⟨c, by simp, hC.2.2 hcC⟩
            · exact ⟨e, by simp, hE.2.2 heE⟩
          have hVGood : IsGoodTraceBlocker a b C E {z, c, e} := by
            simp [IsGoodTraceBlocker, hza.symm, hzb.symm, hca.symm, hcb.symm,
              hea.symm, heb.symm]
          apply finish hV hVGood haDegree
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_singleton]
          rcases hx with ⟨hxa | hxb, hxz | hxc | hxe⟩
          · exact (hza (hxz.symm.trans hxa)).elim
          · exact (hca (hxc.symm.trans hxa)).elim
          · exact (hea (hxe.symm.trans hxa)).elim
          · exact (hzb (hxz.symm.trans hxb)).elim
          · exact (hcb (hxc.symm.trans hxb)).elim
          · exact (heb (hxe.symm.trans hxb)).elim

theorem generalized_trace_two_good_of_disjoint_roles {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E : Row α}
    (hZcard : Z.card = 3) (hRows : RowsCardAtLeast Z 3)
    (hCcard : C.card = 2) (hEcard : E.card = 2)
    (hab : a ≠ b)
    (haC : a ∉ C) (hbC : b ∉ C) (haE : a ∉ E) (hbE : b ∉ E)
    (hCE : Disjoint C E)
    (hTraceC : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R)
    (hTraceE : ∀ R ∈ Z, a ∈ R ∨ E ⊆ R)
    (hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ E then 1 else 0) ≤ 3) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  obtain ⟨c, d, hcd, hC⟩ := Finset.card_eq_two.mp hCcard
  obtain ⟨e, f, hef, hE⟩ := Finset.card_eq_two.mp hEcard
  have hcC : c ∈ C := by simp [hC]
  have hdC : d ∈ C := by simp [hC]
  have heE : e ∈ E := by simp [hE]
  have hfE : f ∈ E := by simp [hE]
  have hca : c ≠ a := fun hca ↦ haC (hca ▸ hcC)
  have hda : d ≠ a := fun hda ↦ haC (hda ▸ hdC)
  have hcb : c ≠ b := fun hcb ↦ hbC (hcb ▸ hcC)
  have hdb : d ≠ b := fun hdb ↦ hbC (hdb ▸ hdC)
  have hea : e ≠ a := fun hea ↦ haE (hea ▸ heE)
  have hfa : f ≠ a := fun hfa ↦ haE (hfa ▸ hfE)
  have heb : e ≠ b := fun heb ↦ hbE (heb ▸ heE)
  have hfb : f ≠ b := fun hfb ↦ hbE (hfb ▸ hfE)
  have hcE : c ∉ E := fun hcE ↦ Finset.disjoint_left.mp hCE hcC hcE
  have hdE : d ∉ E := fun hdE ↦ Finset.disjoint_left.mp hCE hdC hdE
  have heC : e ∉ C := fun heC ↦ Finset.disjoint_left.mp hCE heC heE
  have hfC : f ∉ C := fun hfC ↦ Finset.disjoint_left.mp hCE hfC hfE
  have hce : c ≠ e := fun hce ↦ hcE (hce ▸ heE)
  have hcf : c ≠ f := fun hcf ↦ hcE (hcf ▸ hfE)
  have haDegree : degree Z a ≤ 2 := by
    have h := hBudget a
    simp [hab, haC, haE] at h
    omega
  have hbDegree : degree Z b ≤ 2 := by
    have h := hBudget b
    simp [hab.symm, hbC, hbE] at h
    omega
  have hcDegree : degree Z c ≤ 2 := by
    have h := hBudget c
    simp [hca, hcb, hcC, hcE] at h
    omega
  by_cases hACover : ∀ R ∈ Z, a ∈ R ∨ C ⊆ R
  · exact endpoint_or_pair_cover_two_good hZcard hACover hcC hdC
      haE hcE hdE hab.symm hcb.symm hdb.symm hcd haDegree
  push Not at hACover
  obtain ⟨RE, hREZ, haRE, hCnotRE⟩ := hACover
  have hbRE : b ∈ RE := (hTraceC RE hREZ).resolve_right hCnotRE
  have hESubRE : E ⊆ RE := (hTraceE RE hREZ).resolve_left haRE
  have hREType : HasTraceE a b E RE := ⟨haRE, hbRE, hESubRE⟩
  by_cases hBCover : ∀ R ∈ Z, b ∈ R ∨ E ⊆ R
  · obtain ⟨S, T, hSb, hTb, hST, hSGood, hTGood⟩ :=
      endpoint_or_pair_cover_two_good
        (Z := Z) (a := b) (b := a) (c := e) (d := f) (C := E) (E := C)
        hZcard hBCover heE hfE hbC heC hfC hab hea.symm hfa.symm hef hbDegree
    exact ⟨S, T, hSb, hTb, hST,
      by simpa [IsGoodTraceBlocker, and_comm] using hSGood,
      by simpa [IsGoodTraceBlocker, and_comm] using hTGood⟩
  push Not at hBCover
  obtain ⟨RC, hRCZ, hbRC, hEnotRC⟩ := hBCover
  have haRC : a ∈ RC := (hTraceE RC hRCZ).resolve_right hEnotRC
  have hCSubRC : C ⊆ RC := (hTraceC RC hRCZ).resolve_left hbRC
  have hRCType : HasTraceC a b C RC := ⟨haRC, hbRC, hCSubRC⟩
  have hRCneRE : RC ≠ RE := by
    intro hEq
    exact haRE (hEq ▸ haRC)
  have hREErase : RE ∈ Z.erase RC := Finset.mem_erase.mpr ⟨hRCneRE.symm, hREZ⟩
  have hEraseCard : (Z.erase RC).card = 2 := by
    rw [Finset.card_erase_of_mem hRCZ]
    omega
  have hRestCard : ((Z.erase RC).erase RE).card = 1 := by
    rw [Finset.card_erase_of_mem hREErase, hEraseCard]
  obtain ⟨R0, hRest⟩ := Finset.card_eq_one.mp hRestCard
  have hZ : Z = {RC, RE, R0} := by
    calc
      Z = insert RC (Z.erase RC) := (Finset.insert_erase hRCZ).symm
      _ = insert RC (insert RE ((Z.erase RC).erase RE)) := by
        rw [Finset.insert_erase hREErase]
      _ = {RC, RE, R0} := by rw [hRest]
  have hR0Z : R0 ∈ Z := by simp [hZ]
  rcases row_has_trace (hTraceC R0 hR0Z) (hTraceE R0 hR0Z) with
      hR0A | hR0C | hR0E | hR0N
  · apply trace_A_C_E_two_good hZcard
      (by rw [hZ]; ext R; simp [or_comm, or_left_comm]) hRows hR0A hRCType hREType
      hcC heE haC hbC heC haE hbE hcE haDegree hbDegree
  · have hEndpointCover : ∀ R ∈ Z, a ∈ R ∨ b ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl hRCType.1
      · exact Or.inr hREType.2.1
      · exact Or.inl hR0C.1
    have hCrossCover : ∀ R ∈ Z, c ∈ R ∨ e ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl (hRCType.2.2 hcC)
      · exact Or.inr (hREType.2.2 heE)
      · exact Or.inl (hR0C.2.2 hcC)
    exact endpoint_cross_cover_two_good hZcard hEndpointCover hCrossCover
      haC hbC haE hbE hca hcb hea heb haDegree
  · have hEndpointCover : ∀ R ∈ Z, a ∈ R ∨ b ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl hRCType.1
      · exact Or.inr hREType.2.1
      · exact Or.inr hR0E.2.1
    have hCrossCover : ∀ R ∈ Z, c ∈ R ∨ e ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl (hRCType.2.2 hcC)
      · exact Or.inr (hREType.2.2 heE)
      · exact Or.inr (hR0E.2.2 heE)
    exact endpoint_cross_cover_two_good hZcard hEndpointCover hCrossCover
      haC hbC haE hbE hca hcb hea heb haDegree
  · have hFirstCover : ∀ R ∈ Z, c ∈ R ∨ e ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl (hRCType.2.2 hcC)
      · exact Or.inr (hREType.2.2 heE)
      · exact Or.inl (hR0N.2.2.1 hcC)
    have hSecondCover : ∀ R ∈ Z, c ∈ R ∨ f ∈ R := by
      intro R hR
      rw [hZ] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl | rfl
      · exact Or.inl (hRCType.2.2 hcC)
      · exact Or.inr (hREType.2.2 hfE)
      · exact Or.inl (hR0N.2.2.1 hcC)
    exact pair_cross_cover_two_good hZcard hFirstCover hSecondCover
      hca hcb hea heb hfa hfb hef hcDegree

theorem generalized_trace_two_good_of_endpoint_in_pair {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E : Row α}
    (hZcard : Z.card = 3) (hRows : RowsCardAtLeast Z 3)
    (hCcard : C.card = 2) (hEcard : E.card = 2)
    (hab : a ≠ b) (haC : a ∈ C) (haE : a ∉ E) (hbC : b ∉ C)
    (hTraceC : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R)
    (hTraceE : ∀ R ∈ Z, a ∈ R ∨ E ⊆ R)
    (hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ E then 1 else 0) ≤ 3) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  have haDegree : degree Z a ≤ 1 := by
    have h := hBudget a
    simp [hab, haC, haE] at h
    omega
  have hPartition := card_avoidPoint_add_degree Z a
  have hAvoidCard : 2 ≤ (avoidPoint Z a).card := by omega
  obtain ⟨R₁, hR₁Avoid, R₂, hR₂Avoid, hR₁R₂⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (avoidPoint Z a).card)
  obtain ⟨hR₁Z, haR₁⟩ := mem_avoidPoint.mp hR₁Avoid
  obtain ⟨hR₂Z, haR₂⟩ := mem_avoidPoint.mp hR₂Avoid
  have hbR₁ : b ∈ R₁ := by
    rcases hTraceC R₁ hR₁Z with hbR₁ | hCR₁
    · exact hbR₁
    · exact (haR₁ (hCR₁ haC)).elim
  have hbR₂ : b ∈ R₂ := by
    rcases hTraceC R₂ hR₂Z with hbR₂ | hCR₂
    · exact hbR₂
    · exact (haR₂ (hCR₂ haC)).elim
  have hER₁ : E ⊆ R₁ := (hTraceE R₁ hR₁Z).resolve_left haR₁
  have hER₂ : E ⊆ R₂ := (hTraceE R₂ hR₂Z).resolve_left haR₂
  have hbE : b ∉ E := by
    intro hbE
    have hbDegree : degree Z b ≤ 1 := by
      have h := hBudget b
      simp [hab.symm, hbC, hbE] at h
      omega
    have hTwo := degree_ge_two_of_two_rows hR₁Z hR₂Z hR₁R₂ hbR₁ hbR₂
    omega
  have hCE : Disjoint C E := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxE
    have hxDegree : degree Z x ≤ 1 := by
      have h := hBudget x
      simp [hxC, hxE] at h
      omega
    have hTwo := degree_ge_two_of_two_rows hR₁Z hR₂Z hR₁R₂
      (hER₁ hxE) (hER₂ hxE)
    omega
  have hbDegree : degree Z b ≤ 2 := by
    have h := hBudget b
    simp [hab.symm, hbC, hbE] at h
    omega
  obtain ⟨e, heE⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  have heC : e ∉ C := fun heC ↦ Finset.disjoint_left.mp hCE heC heE
  have heDegree : degree Z e ≤ 2 := by
    have h := hBudget e
    simp [heC, heE] at h
    omega
  have hR₂Erase : R₂ ∈ Z.erase R₁ := Finset.mem_erase.mpr ⟨hR₁R₂.symm, hR₂Z⟩
  have hEraseCard : (Z.erase R₁).card = 2 := by
    rw [Finset.card_erase_of_mem hR₁Z]
    omega
  have hRestCard : ((Z.erase R₁).erase R₂).card = 1 := by
    rw [Finset.card_erase_of_mem hR₂Erase, hEraseCard]
  obtain ⟨R₃, hRest⟩ := Finset.card_eq_one.mp hRestCard
  have hZ : Z = {R₁, R₂, R₃} := by
    calc
      Z = insert R₁ (Z.erase R₁) := (Finset.insert_erase hR₁Z).symm
      _ = insert R₁ (insert R₂ ((Z.erase R₁).erase R₂)) := by
        rw [Finset.insert_erase hR₂Erase]
      _ = {R₁, R₂, R₃} := by rw [hRest]
  have hR₃Z : R₃ ∈ Z := by simp [hZ]
  have hR₁R₃ : R₁ ≠ R₃ := by
    intro hEq
    have hR₃Rest : R₃ ∈ (Z.erase R₁).erase R₂ := by simp [hRest]
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hR₃Rest).2).1 hEq.symm
  have hR₂R₃ : R₂ ≠ R₃ := by
    intro hEq
    have hR₃Rest : R₃ ∈ (Z.erase R₁).erase R₂ := by simp [hRest]
    exact (Finset.mem_erase.mp hR₃Rest).1 hEq.symm
  have hbR₃ : b ∉ R₃ := by
    intro hbR₃
    have hThree := degree_ge_three_of_three_rows hR₁Z hR₂Z hR₃Z
      hR₁R₂ hR₁R₃ hR₂R₃ hbR₁ hbR₂ hbR₃
    omega
  have heR₃ : e ∉ R₃ := by
    intro heR₃
    have hThree := degree_ge_three_of_three_rows hR₁Z hR₂Z hR₃Z
      hR₁R₂ hR₁R₃ hR₂R₃ (hER₁ heE) (hER₂ heE) heR₃
    omega
  have hCR₃ : C ⊆ R₃ := (hTraceC R₃ hR₃Z).resolve_left hbR₃
  obtain ⟨d, hdC, hda⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) a
  have hdR₃ : d ∈ R₃ := hCR₃ hdC
  have hCLtR₃ : C.card < R₃.card := by
    have hR₃Card := hRows R₃ hR₃Z
    omega
  obtain ⟨z, hzR₃, hzC⟩ := Finset.exists_mem_notMem_of_card_lt_card hCLtR₃
  have hdb : d ≠ b := fun hdb ↦ hbC (hdb ▸ hdC)
  have hde : d ≠ e := fun hde ↦ heC (hde ▸ hdC)
  have hea : e ≠ a := fun hea ↦ haE (hea ▸ heE)
  have heb : e ≠ b := fun heb ↦ hbE (heb ▸ heE)
  have hza : z ≠ a := fun hza ↦ hzC (hza ▸ haC)
  have hzb : z ≠ b := fun hzb ↦ hbR₃ (hzb ▸ hzR₃)
  have hU : IsTransversal Z {d, e} := by
    intro R hR
    rw [hZ] at hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨e, by simp, hER₁ heE⟩
    · exact ⟨e, by simp, hER₂ heE⟩
    · exact ⟨d, by simp, hdR₃⟩
  have hV : IsTransversal Z {b, z} := by
    intro R hR
    rw [hZ] at hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨b, by simp, hbR₁⟩
    · exact ⟨b, by simp, hbR₂⟩
    · exact ⟨z, by simp, hzR₃⟩
  have hUGood : IsGoodTraceBlocker a b C E {d, e} := by
    simp [IsGoodTraceBlocker, hda.symm, hdb.symm, hea.symm, heb.symm]
  have hVGood : IsGoodTraceBlocker a b C E {b, z} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, hab, hza.symm, hbC, hzC]
  have hSubset : ({d, e} : Row α) ∩ {b, z} ⊆ {b} := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_singleton]
    rcases hx with ⟨hxd | hxe, hxb | hxz⟩
    · exact (hdb (hxd.symm.trans hxb)).elim
    · exact (hzC (hxz.symm.trans hxd ▸ hdC)).elim
    · exact (hbE (hxe.symm.trans hxb ▸ heE)).elim
    · exact (heR₃ (hxz.symm.trans hxe ▸ hzR₃)).elim
  exact two_good_blockers_of_transversals hU hV hUGood hVGood
    (not_transversal_of_subset_singleton_of_degree_le_two
      hZcard hbDegree hSubset)

theorem generalized_trace_two_good_of_single_overlap {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E : Row α}
    (hZcard : Z.card = 3)
    (hCcard : C.card = 2) (hEcard : E.card = 2)
    (hInterCard : (C ∩ E).card = 1)
    (hab : a ≠ b)
    (haC : a ∉ C) (hbC : b ∉ C) (haE : a ∉ E) (hbE : b ∉ E)
    (hTraceC : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R)
    (hTraceE : ∀ R ∈ Z, a ∈ R ∨ E ⊆ R)
    (hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ E then 1 else 0) ≤ 3) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  obtain ⟨r, hInter⟩ := Finset.card_eq_one.mp hInterCard
  have hrInter : r ∈ C ∩ E := by simp [hInter]
  have hrC := (Finset.mem_inter.mp hrInter).1
  have hrE := (Finset.mem_inter.mp hrInter).2
  obtain ⟨c, hcC, hcr⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) r
  obtain ⟨e, heE, her⟩ := Finset.exists_mem_ne (by omega : 1 < E.card) r
  have hcE : c ∉ E := by
    intro hcE
    have hcInter : c ∈ C ∩ E := Finset.mem_inter.mpr ⟨hcC, hcE⟩
    have hcr' : c = r := by simpa [hInter] using hcInter
    exact hcr hcr'
  have heC : e ∉ C := by
    intro heC
    have heInter : e ∈ C ∩ E := Finset.mem_inter.mpr ⟨heC, heE⟩
    have her' : e = r := by simpa [hInter] using heInter
    exact her her'
  have hca : c ≠ a := fun hca ↦ haC (hca ▸ hcC)
  have hcb : c ≠ b := fun hcb ↦ hbC (hcb ▸ hcC)
  have hea : e ≠ a := fun hea ↦ haE (hea ▸ heE)
  have heb : e ≠ b := fun heb ↦ hbE (heb ▸ heE)
  have hce : c ≠ e := fun hce ↦ hcE (hce ▸ heE)
  have haDegree : degree Z a ≤ 2 := by
    have h := hBudget a
    simp [hab, haC, haE] at h
    omega
  have hbDegree : degree Z b ≤ 2 := by
    have h := hBudget b
    simp [hab.symm, hbC, hbE] at h
    omega
  have hrDegree : degree Z r ≤ 1 := by
    have h := hBudget r
    simp [hrC, hrE] at h
    omega
  have hAvoidANonempty : (avoidPoint Z a).Nonempty := by
    have hPartition := card_avoidPoint_add_degree Z a
    apply Finset.card_pos.mp
    omega
  have hAvoidBNonempty : (avoidPoint Z b).Nonempty := by
    have hPartition := card_avoidPoint_add_degree Z b
    apply Finset.card_pos.mp
    omega
  obtain ⟨RA, hRAAvoid⟩ := hAvoidANonempty
  obtain ⟨RB, hRBAvoid⟩ := hAvoidBNonempty
  obtain ⟨hRAZ, haRA⟩ := mem_avoidPoint.mp hRAAvoid
  obtain ⟨hRBZ, hbRB⟩ := mem_avoidPoint.mp hRBAvoid
  have hERA : E ⊆ RA := (hTraceE RA hRAZ).resolve_left haRA
  have hCRB : C ⊆ RB := (hTraceC RB hRBZ).resolve_left hbRB
  have hrRA : r ∈ RA := hERA hrE
  have hrRB : r ∈ RB := hCRB hrC
  have all_other_contain_a {R : Row α} (hRZ : R ∈ Z) (hRne : R ≠ RA) : a ∈ R := by
    by_contra haR
    have hER : E ⊆ R := (hTraceE R hRZ).resolve_left haR
    have hTwo := degree_ge_two_of_two_rows hRAZ hRZ hRne.symm hrRA (hER hrE)
    omega
  have all_other_contain_b {R : Row α} (hRZ : R ∈ Z) (hRne : R ≠ RB) : b ∈ R := by
    by_contra hbR
    have hCR : C ⊆ R := (hTraceC R hRZ).resolve_left hbR
    have hTwo := degree_ge_two_of_two_rows hRBZ hRZ hRne.symm hrRB (hCR hrC)
    omega
  by_cases hbRA : b ∈ RA
  · have hU : IsTransversal Z {a, b} := by
      intro R hR
      by_cases hRRA : R = RA
      · exact ⟨b, by simp, hRRA ▸ hbRA⟩
      · exact ⟨a, by simp, all_other_contain_a hR hRRA⟩
    have hUGood : IsGoodTraceBlocker a b C E {a, b} := by
      simp [IsGoodTraceBlocker, Finset.disjoint_left, haC, hbC, haE, hbE]
    by_cases haRB : a ∈ RB
    · have hRARBDistinct : RA ≠ RB := by
        intro hEq
        exact hbRB (hEq ▸ hbRA)
      have hTwo := degree_ge_two_of_two_rows hRAZ hRBZ hRARBDistinct hrRA hrRB
      exact (show False by omega).elim
    · have hERB : E ⊆ RB := (hTraceE RB hRBZ).resolve_left haRB
      have hV : IsTransversal Z {b, e} := by
        intro R hR
        by_cases hRRB : R = RB
        · exact ⟨e, by simp, by simpa [hRRB] using hERB heE⟩
        · exact ⟨b, by simp, all_other_contain_b hR hRRB⟩
      have hVGood : IsGoodTraceBlocker a b C E {b, e} := by
        simp [IsGoodTraceBlocker, Finset.disjoint_left, hab, hea.symm, hbC, heC]
      have hSubset : ({a, b} : Row α) ∩ {b, e} ⊆ {b} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_singleton]
        rcases hx with ⟨hxa | hxb, hxb' | hxe⟩
        · exact (hab (hxb'.symm.trans hxa).symm).elim
        · exact (hea (hxe.symm.trans hxa)).elim
        · exact hxb
        · exact (heb (hxe.symm.trans hxb)).elim
      exact two_good_blockers_of_transversals hU hV hUGood hVGood
        (not_transversal_of_subset_singleton_of_degree_le_two
          hZcard hbDegree hSubset)
  · have hCRA : C ⊆ RA := (hTraceC RA hRAZ).resolve_left hbRA
    have hU : IsTransversal Z {a, c} := by
      intro R hR
      by_cases hRRA : R = RA
      · exact ⟨c, by simp, by simpa [hRRA] using hCRA hcC⟩
      · exact ⟨a, by simp, all_other_contain_a hR hRRA⟩
    have hUGood : IsGoodTraceBlocker a b C E {a, c} := by
      simp [IsGoodTraceBlocker, Finset.disjoint_left, haE, hcE, hab.symm, hcb.symm]
    by_cases haRB : a ∈ RB
    · have hV : IsTransversal Z {a, b} := by
        intro R hR
        by_cases hRRB : R = RB
        · exact ⟨a, by simp, hRRB ▸ haRB⟩
        · exact ⟨b, by simp, all_other_contain_b hR hRRB⟩
      have hVGood : IsGoodTraceBlocker a b C E {a, b} := by
        simp [IsGoodTraceBlocker, Finset.disjoint_left, haC, hbC, haE, hbE]
      have hSubset : ({a, c} : Row α) ∩ {a, b} ⊆ {a} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_singleton]
        rcases hx with ⟨hxa | hxc, hxa' | hxb⟩
        · exact hxa
        · exact hxa
        · exact hxa'
        · exact (hcb (hxc.symm.trans hxb)).elim
      exact two_good_blockers_of_transversals hU hV hUGood hVGood
        (not_transversal_of_subset_singleton_of_degree_le_two
          hZcard haDegree hSubset)
    · have hERB : E ⊆ RB := (hTraceE RB hRBZ).resolve_left haRB
      have hV : IsTransversal Z {b, e} := by
        intro R hR
        by_cases hRRB : R = RB
        · exact ⟨e, by simp, by simpa [hRRB] using hERB heE⟩
        · exact ⟨b, by simp, all_other_contain_b hR hRRB⟩
      have hVGood : IsGoodTraceBlocker a b C E {b, e} := by
        simp [IsGoodTraceBlocker, Finset.disjoint_left, hab, hea.symm, hbC, heC]
      have hSubset : ({a, c} : Row α) ∩ {b, e} ⊆ {a} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_singleton]
        rcases hx with ⟨hxa | hxc, hxb | hxe⟩
        · exact (hab (hxb.symm.trans hxa).symm).elim
        · exact (hea (hxe.symm.trans hxa)).elim
        · exact (hcb (hxc.symm.trans hxb)).elim
        · exact (hce (hxc.symm.trans hxe)).elim
      exact two_good_blockers_of_transversals hU hV hUGood hVGood
        (not_transversal_of_subset_singleton_of_degree_le_two
          hZcard haDegree hSubset)

theorem generalized_trace_two_good_of_equal_pairs {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C : Row α}
    (hZ : IsClutter Z) (hZcard : Z.card = 3) (hRows : RowsCardAtLeast Z 3)
    (hCcard : C.card = 2) (hab : a ≠ b) (haC : a ∉ C) (hbC : b ∉ C)
    (hTraceC : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R)
    (hTraceE : ∀ R ∈ Z, a ∈ R ∨ C ⊆ R)
    (hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ C then 1 else 0) ≤ 3) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C C S ∧ IsGoodTraceBlocker a b C C T := by
  have haDegree : degree Z a ≤ 2 := by
    have h := hBudget a
    simp [hab, haC] at h
    omega
  have hbDegree : degree Z b ≤ 2 := by
    have h := hBudget b
    simp [hab.symm, hbC] at h
    omega
  have hAvoidANonempty : (avoidPoint Z a).Nonempty := by
    have hPartition := card_avoidPoint_add_degree Z a
    apply Finset.card_pos.mp
    omega
  have hAvoidBNonempty : (avoidPoint Z b).Nonempty := by
    have hPartition := card_avoidPoint_add_degree Z b
    apply Finset.card_pos.mp
    omega
  obtain ⟨RA, hRAAvoid⟩ := hAvoidANonempty
  obtain ⟨RB, hRBAvoid⟩ := hAvoidBNonempty
  obtain ⟨hRAZ, haRA⟩ := mem_avoidPoint.mp hRAAvoid
  obtain ⟨hRBZ, hbRB⟩ := mem_avoidPoint.mp hRBAvoid
  have hCRA : C ⊆ RA := (hTraceE RA hRAZ).resolve_left haRA
  have hCRB : C ⊆ RB := (hTraceC RB hRBZ).resolve_left hbRB
  obtain ⟨c, hcC⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
  have hcDegree : degree Z c ≤ 1 := by
    have h := hBudget c
    simp [hcC] at h
    omega
  have hRARB : RA = RB := by
    by_contra hne
    have hTwo := degree_ge_two_of_two_rows hRAZ hRBZ hne
      (hCRA hcC) (hCRB hcC)
    omega
  subst RB
  have hbRA : b ∉ RA := hbRB
  have all_other_contain_a {R : Row α} (hRZ : R ∈ Z) (hRne : R ≠ RA) : a ∈ R := by
    by_contra haR
    have hCR : C ⊆ R := (hTraceE R hRZ).resolve_left haR
    have hTwo := degree_ge_two_of_two_rows hRAZ hRZ hRne.symm
      (hCRA hcC) (hCR hcC)
    omega
  have all_other_contain_b {R : Row α} (hRZ : R ∈ Z) (hRne : R ≠ RA) : b ∈ R := by
    by_contra hbR
    have hCR : C ⊆ R := (hTraceC R hRZ).resolve_left hbR
    have hTwo := degree_ge_two_of_two_rows hRAZ hRZ hRne.symm
      (hCRA hcC) (hCR hcC)
    omega
  have hCLtRA : C.card < RA.card := by
    have hRACard := hRows RA hRAZ
    omega
  obtain ⟨z, hzRA, hzC⟩ := Finset.exists_mem_notMem_of_card_lt_card hCLtRA
  have hza : z ≠ a := fun hza ↦ haRA (hza ▸ hzRA)
  have hzb : z ≠ b := fun hzb ↦ hbRA (hzb ▸ hzRA)
  have hU : IsTransversal Z {a, z} := by
    intro R hR
    by_cases hRRA : R = RA
    · exact ⟨z, by simp, by simpa [hRRA] using hzRA⟩
    · exact ⟨a, by simp, all_other_contain_a hR hRRA⟩
  have hV : IsTransversal Z {b, z} := by
    intro R hR
    by_cases hRRA : R = RA
    · exact ⟨z, by simp, by simpa [hRRA] using hzRA⟩
    · exact ⟨b, by simp, all_other_contain_b hR hRRA⟩
  have hUGood : IsGoodTraceBlocker a b C C {a, z} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, haC, hzC, hab.symm, hzb]
  have hVGood : IsGoodTraceBlocker a b C C {b, z} := by
    simp [IsGoodTraceBlocker, Finset.disjoint_left, hab, hza.symm, hbC, hzC]
  have hzDegreeUpper : degree Z z ≤ 3 := by
    calc
      degree Z z ≤ Z.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 3 := hZcard
  by_cases hzDegree : degree Z z ≤ 2
  · have hSubset : ({a, z} : Row α) ∩ {b, z} ⊆ {z} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_singleton]
      rcases hx with ⟨hxa | hxz, hxb | hxz'⟩
      · exact (hab (hxb.symm.trans hxa).symm).elim
      · exact hxz'
      · exact hxz
      · exact hxz
    exact two_good_blockers_of_transversals hU hV hUGood hVGood
      (not_transversal_of_subset_singleton_of_degree_le_two
        hZcard hzDegree hSubset)
  · have hzDegreeEq : degree Z z = 3 := by omega
    have hFilterEq : Z.filter (fun R ↦ z ∈ R) = Z := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [show (Z.filter fun R ↦ z ∈ R).card = degree Z z from rfl,
        hzDegreeEq, hZcard]
    have hzAll : ∀ R ∈ Z, z ∈ R := by
      intro R hR
      have hRFilter : R ∈ Z.filter (fun S ↦ z ∈ S) := hFilterEq.symm ▸ hR
      exact (Finset.mem_filter.mp hRFilter).2
    have hEraseCard : (Z.erase RA).card = 2 := by
      rw [Finset.card_erase_of_mem hRAZ, hZcard]
    obtain ⟨R₁, R₂, hR₁R₂, hErase⟩ := Finset.card_eq_two.mp hEraseCard
    have hR₁Erase : R₁ ∈ Z.erase RA := by simp [hErase]
    have hR₂Erase : R₂ ∈ Z.erase RA := by simp [hErase]
    obtain ⟨hR₁RA, hR₁Z⟩ := Finset.mem_erase.mp hR₁Erase
    obtain ⟨hR₂RA, hR₂Z⟩ := Finset.mem_erase.mp hR₂Erase
    have hR₁notSubset : ¬ R₁ ⊆ R₂ := by
      intro hSub
      exact hR₁R₂ (hZ hR₁Z hR₂Z hSub)
    have hR₂notSubset : ¬ R₂ ⊆ R₁ := by
      intro hSub
      exact hR₁R₂.symm (hZ hR₂Z hR₁Z hSub)
    obtain ⟨x, hxR₁, hxR₂⟩ := Finset.not_subset.mp hR₁notSubset
    obtain ⟨y, hyR₂, hyR₁⟩ := Finset.not_subset.mp hR₂notSubset
    have hcR₁ : c ∉ R₁ := by
      intro hcR₁
      have hTwo := degree_ge_two_of_two_rows hRAZ hR₁Z hR₁RA.symm
        (hCRA hcC) hcR₁
      omega
    have hcR₂ : c ∉ R₂ := by
      intro hcR₂
      have hTwo := degree_ge_two_of_two_rows hRAZ hR₂Z hR₂RA.symm
        (hCRA hcC) hcR₂
      omega
    have hxa : x ≠ a := fun hxa ↦ hxR₂ (hxa ▸ all_other_contain_a hR₂Z hR₂RA)
    have hxb : x ≠ b := fun hxb ↦ hxR₂ (hxb ▸ all_other_contain_b hR₂Z hR₂RA)
    have hxz : x ≠ z := fun hxz ↦ hxR₂ (hxz ▸ hzAll R₂ hR₂Z)
    have hya : y ≠ a := fun hya ↦ hyR₁ (hya ▸ all_other_contain_a hR₁Z hR₁RA)
    have hyb : y ≠ b := fun hyb ↦ hyR₁ (hyb ▸ all_other_contain_b hR₁Z hR₁RA)
    have hyz : y ≠ z := fun hyz ↦ hyR₁ (hyz ▸ hzAll R₁ hR₁Z)
    have hcx : c ≠ x := fun hcx ↦ hcR₁ (hcx ▸ hxR₁)
    have hcy : c ≠ y := fun hcy ↦ hcR₂ (hcy ▸ hyR₂)
    have hxy : x ≠ y := fun hxy ↦ hxR₂ (hxy ▸ hyR₂)
    have hW : IsTransversal Z {c, x, y} := by
      intro R hR
      by_cases hRRA : R = RA
      · exact ⟨c, by simp, by simpa [hRRA] using hCRA hcC⟩
      have hRErase : R ∈ Z.erase RA := Finset.mem_erase.mpr ⟨hRRA, hR⟩
      rw [hErase] at hRErase
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRErase
      rcases hRErase with rfl | rfl
      · exact ⟨x, by simp, hxR₁⟩
      · exact ⟨y, by simp, hyR₂⟩
    have hac : a ≠ c := fun hac ↦ haC (hac ▸ hcC)
    have hbc : b ≠ c := fun hbc ↦ hbC (hbc ▸ hcC)
    have hWGood : IsGoodTraceBlocker a b C C {c, x, y} := by
      simp [IsGoodTraceBlocker, hac, hxa.symm, hya.symm,
        hbc, hxb.symm, hyb.symm]
    have hSubset : ({a, z} : Row α) ∩ {c, x, y} ⊆ {a} := by
      intro u hu
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu
      simp only [Finset.mem_singleton]
      rcases hu with ⟨hua | huz, huc | hux | huy⟩
      · exact (haC (hua.symm.trans huc ▸ hcC)).elim
      · exact (hxa (hux.symm.trans hua)).elim
      · exact (hya (huy.symm.trans hua)).elim
      · exact (hzC (huz.symm.trans huc ▸ hcC)).elim
      · exact (hxz (hux.symm.trans huz)).elim
      · exact (hyz (huy.symm.trans huz)).elim
    exact two_good_blockers_of_transversals hU hW hUGood hWGood
      (not_transversal_of_subset_singleton_of_degree_le_two
        hZcard haDegree hSubset)

theorem generalized_trace_two_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z : Hypergraph α} {a b : α} {C E : Row α}
    (hZ : IsClutter Z) (hZcard : Z.card = 3) (hRows : RowsCardAtLeast Z 3)
    (hCcard : C.card = 2) (hEcard : E.card = 2)
    (hab : a ≠ b) (haE : a ∉ E) (hbC : b ∉ C)
    (hTraceC : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R)
    (hTraceE : ∀ R ∈ Z, a ∈ R ∨ E ⊆ R)
    (hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ E then 1 else 0) ≤ 3) :
    ∃ S T,
      S ∈ blocker Z ∧ T ∈ blocker Z ∧ S ≠ T ∧
      IsGoodTraceBlocker a b C E S ∧ IsGoodTraceBlocker a b C E T := by
  by_cases haC : a ∈ C
  · exact generalized_trace_two_good_of_endpoint_in_pair
      hZcard hRows hCcard hEcard hab haC haE hbC hTraceC hTraceE hBudget
  by_cases hbE : b ∈ E
  · have hBudgetSwapped : ∀ x,
        degree Z x +
          (if x = b then 1 else 0) +
          (if x = a then 1 else 0) +
          (if x ∈ E then 1 else 0) +
          (if x ∈ C then 1 else 0) ≤ 3 := by
      intro x
      have h := hBudget x
      omega
    obtain ⟨S, T, hSb, hTb, hST, hSGood, hTGood⟩ :=
      generalized_trace_two_good_of_endpoint_in_pair
        (Z := Z) (a := b) (b := a) (C := E) (E := C)
        hZcard hRows hEcard hCcard hab.symm hbE hbC haE
        hTraceE hTraceC hBudgetSwapped
    exact ⟨S, T, hSb, hTb, hST,
      by simpa [IsGoodTraceBlocker, and_comm] using hSGood,
      by simpa [IsGoodTraceBlocker, and_comm] using hTGood⟩
  by_cases hCE : Disjoint C E
  · exact generalized_trace_two_good_of_disjoint_roles
      hZcard hRows hCcard hEcard hab haC hbC haE hbE hCE
      hTraceC hTraceE hBudget
  have hInterNonempty : (C ∩ E).Nonempty := by
    obtain ⟨x, hxC, hxE⟩ := Finset.not_disjoint_iff.mp hCE
    exact ⟨x, Finset.mem_inter.mpr ⟨hxC, hxE⟩⟩
  have hInterPos : 0 < (C ∩ E).card := Finset.card_pos.mpr hInterNonempty
  have hInterUpper : (C ∩ E).card ≤ 2 := by
    have h := Finset.card_le_card (Finset.inter_subset_left : C ∩ E ⊆ C)
    omega
  have hInterCard : (C ∩ E).card = 1 ∨ (C ∩ E).card = 2 := by omega
  rcases hInterCard with hInterCard | hInterCard
  · exact generalized_trace_two_good_of_single_overlap
      hZcard hCcard hEcard hInterCard hab haC hbC haE hbE
      hTraceC hTraceE hBudget
  · have hInterEqC : C ∩ E = C :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hCSubE : C ⊆ E := by
      intro x hxC
      have hxInter : x ∈ C ∩ E := hInterEqC.symm ▸ hxC
      exact (Finset.mem_inter.mp hxInter).2
    have hCEq : C = E := Finset.eq_of_subset_of_card_le hCSubE (by omega)
    subst E
    exact generalized_trace_two_good_of_equal_pairs
      hZ hZcard hRows hCcard hab haC hbC hTraceC hTraceE hBudget

end AiMathLab.P0054.G413
