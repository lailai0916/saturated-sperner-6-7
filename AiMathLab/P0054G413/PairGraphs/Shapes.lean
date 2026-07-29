import AiMathLab.P0054G413.PairGraphs.Support
import AiMathLab.P0054G413.PairGraphs.Remaining

namespace AiMathLab.P0054.G413

def HasPairGraphP4 {α : Type*} [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  ∃ a p q b, ({a, p, q, b} : Row α).card = 4 ∧
    pairRows H = {{a, p}, {p, q}, {q, b}}

def HasPairGraphP3K2 {α : Type*} [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  ∃ a p q u v, ({a, p, q, u, v} : Row α).card = 5 ∧
    pairRows H = {{a, p}, {p, q}, {u, v}}

def HasPairGraphThreeK2 {α : Type*} [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  ∃ a b c d e f, ({a, b, c, d, e, f} : Row α).card = 6 ∧
    pairRows H = {{a, b}, {c, d}, {e, f}}

def HasPairGraphK3 {α : Type*} [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  ∃ a b c, ({a, b, c} : Row α).card = 3 ∧
    pairRows H = {{a, b}, {b, c}, {c, a}}

def HasPairGraphK13 {α : Type*} [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  ∃ o a b c, ({o, a, b, c} : Row α).card = 4 ∧
    pairRows H = {{o, a}, {o, b}, {o, c}}

theorem pair_mem_of_mem_pairRows {α : Type*}
    {H : Hypergraph α} {E : Row α} (hE : E ∈ pairRows H) :
    E ∈ H ∧ E.card = 2 :=
  Finset.mem_filter.mp hE

theorem pair_eq_pair_of_mem {α : Type*} [DecidableEq α]
    {E : Row α} {p : α} (hEcard : E.card = 2) (hpE : p ∈ E) :
    ∃ q, p ≠ q ∧ E = {p, q} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hEcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpE
  rcases hpE with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, hab.symm, Finset.pair_comm _ _⟩

theorem pair_eq_of_card_two_of_mem {α : Type*} [DecidableEq α]
    {E : Row α} {p q : α} (hEcard : E.card = 2)
    (hpE : p ∈ E) (hqE : q ∈ E) (hpq : p ≠ q) :
    E = {p, q} := by
  exact (Finset.eq_of_subset_of_card_le (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpE
    · exact hqE)
    (by rw [hEcard]; simp [hpq])).symm

theorem triple_reorder {α : Type*} [DecidableEq α]
    (A B C : Row α) :
    ({A, B, C} : Hypergraph α) = {B, C, A} := by
  ext E
  simp [or_comm, or_left_comm]

theorem pairGraph_threeK2_of_pairwise_disjoint {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {A B C : Row α}
    (hPairs : pairRows H = {A, B, C})
    (hAcard : A.card = 2) (hBcard : B.card = 2) (hCcard : C.card = 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    HasPairGraphThreeK2 H := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hBcard
  obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hCcard
  refine ⟨a, b, c, d, e, f, ?_, hPairs⟩
  simp only [Finset.disjoint_left] at hAB hAC hBC
  simp_all

theorem pairGraph_p3k2_of_one_intersection {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {A B C : Row α}
    (hPairs : pairRows H = {A, B, C})
    (hAcard : A.card = 2) (hBcard : B.card = 2) (hCcard : C.card = 2)
    (hABne : A ≠ B)
    (hAB : ¬Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    HasPairGraphP3K2 H := by
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp hAB
  obtain ⟨a, hpa, rfl⟩ := pair_eq_pair_of_mem hAcard hpA
  obtain ⟨q, hpq, rfl⟩ := pair_eq_pair_of_mem hBcard hpB
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hCcard
  have haq : a ≠ q := by
    intro haq
    subst q
    exact hABne rfl
  refine ⟨a, p, q, u, v, ?_, ?_⟩
  · simp [Finset.disjoint_left] at hAC hBC
    simp [Finset.card_insert_of_notMem, Ne.symm hpa, hpq, haq,
      hAC.1.1, hAC.1.2, hAC.2.1, hAC.2.2, hBC.2, huv]
  · simpa [Finset.pair_comm, or_comm, or_left_comm] using hPairs

theorem pairGraph_p4_of_two_intersections {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {A B C : Row α}
    (hPairs : pairRows H = {A, B, C})
    (hAcard : A.card = 2) (hBcard : B.card = 2) (hCcard : C.card = 2)
    (hAB : ¬Disjoint A B) (hAC : Disjoint A C) (hBC : ¬Disjoint B C) :
    HasPairGraphP4 H := by
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp hAB
  obtain ⟨q, hqB, hqC⟩ := Finset.not_disjoint_iff.mp hBC
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact Finset.disjoint_left.mp hAC hpA hqC
  obtain ⟨a, hpa, rfl⟩ := pair_eq_pair_of_mem hAcard hpA
  obtain ⟨r, hpr, hBeq⟩ := pair_eq_pair_of_mem hBcard hpB
  have hqr : q = r := by
    rw [hBeq] at hqB
    simpa [hpq.symm] using hqB
  subst r
  obtain ⟨b, hqb, rfl⟩ := pair_eq_pair_of_mem hCcard hqC
  refine ⟨a, p, q, b, ?_, ?_⟩
  · simp [Finset.disjoint_left] at hAC
    simp [Finset.card_insert_of_notMem, Ne.symm hpa, hpr, hqb,
      hAC.1, hAC.2.1, hAC.2.2]
  · simpa [hBeq, Finset.pair_comm, or_comm, or_left_comm] using hPairs

theorem pairGraph_k13_of_common_point {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {A B C : Row α} {o : α}
    (hPairs : pairRows H = {A, B, C})
    (hAcard : A.card = 2) (hBcard : B.card = 2) (hCcard : C.card = 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hoA : o ∈ A) (hoB : o ∈ B) (hoC : o ∈ C) :
    HasPairGraphK13 H := by
  obtain ⟨a, hoa, rfl⟩ := pair_eq_pair_of_mem hAcard hoA
  obtain ⟨b, hob, rfl⟩ := pair_eq_pair_of_mem hBcard hoB
  obtain ⟨c, hoc, rfl⟩ := pair_eq_pair_of_mem hCcard hoC
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hAB rfl
  have hac : a ≠ c := by
    intro hac
    subst c
    exact hAC rfl
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact hBC rfl
  refine ⟨o, a, b, c, ?_, ?_⟩
  · simp_all
  · simpa [Finset.pair_comm, or_comm, or_left_comm] using hPairs

theorem pairGraph_k3_or_k13_of_pairwise_intersecting {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α} {A B C : Row α}
    (hPairs : pairRows H = {A, B, C})
    (hAcard : A.card = 2) (hBcard : B.card = 2) (hCcard : C.card = 2)
    (hABne : A ≠ B) (hACne : A ≠ C) (hBCne : B ≠ C)
    (hAB : ¬Disjoint A B) (hAC : ¬Disjoint A C) (hBC : ¬Disjoint B C) :
    HasPairGraphK3 H ∨ HasPairGraphK13 H := by
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp hAB
  obtain ⟨q, hqA, hqC⟩ := Finset.not_disjoint_iff.mp hAC
  by_cases hpq : p = q
  · subst q
    exact Or.inr (pairGraph_k13_of_common_point hPairs hAcard hBcard hCcard
      hABne hACne hBCne hpA hpB hqC)
  obtain ⟨r, hrB, hrC⟩ := Finset.not_disjoint_iff.mp hBC
  by_cases hrp : r = p
  · subst r
    exact Or.inr (pairGraph_k13_of_common_point hPairs hAcard hBcard hCcard
      hABne hACne hBCne hpA hpB hrC)
  by_cases hrq : r = q
  · subst r
    exact Or.inr (pairGraph_k13_of_common_point hPairs hAcard hBcard hCcard
      hABne hACne hBCne hqA hrB hqC)
  have hAeq : A = {p, q} :=
    pair_eq_of_card_two_of_mem hAcard hpA hqA hpq
  have hBeq : B = {p, r} :=
    pair_eq_of_card_two_of_mem hBcard hpB hrB (Ne.symm hrp)
  have hCeq : C = {q, r} :=
    pair_eq_of_card_two_of_mem hCcard hqC hrC (Ne.symm hrq)
  left
  refine ⟨p, q, r, by simp [hpq, Ne.symm hrp, Ne.symm hrq], ?_⟩
  simpa [hAeq, hBeq, hCeq, Finset.pair_comm, or_comm, or_left_comm] using hPairs

theorem three_pair_graph_classification {α : Type*}
    [DecidableEq α]
    {H : Hypergraph α}
    (hPairRowsCard : (pairRows H).card = 3) :
    HasPairGraphP4 H ∨ HasPairGraphP3K2 H ∨
      HasPairGraphThreeK2 H ∨ HasPairGraphK3 H ∨ HasPairGraphK13 H := by
  obtain ⟨A, B, C, hABne, hACne, hBCne, hPairs⟩ :=
    Finset.card_eq_three.mp hPairRowsCard
  have hA : A ∈ pairRows H := by rw [hPairs]; simp
  have hB : B ∈ pairRows H := by rw [hPairs]; simp
  have hC : C ∈ pairRows H := by rw [hPairs]; simp
  have hAcard : A.card = 2 := (pair_mem_of_mem_pairRows hA).2
  have hBcard : B.card = 2 := (pair_mem_of_mem_pairRows hB).2
  have hCcard : C.card = 2 := (pair_mem_of_mem_pairRows hC).2
  by_cases hAB : Disjoint A B
  · by_cases hAC : Disjoint A C
    · by_cases hBC : Disjoint B C
      · exact Or.inr (Or.inr (Or.inl (pairGraph_threeK2_of_pairwise_disjoint
          hPairs hAcard hBcard hCcard hAB hAC hBC)))
      · exact Or.inr (Or.inl (pairGraph_p3k2_of_one_intersection
          (by rw [hPairs, triple_reorder])
          hBcard hCcard hAcard hBCne hBC (Disjoint.symm hAB) (Disjoint.symm hAC)))
    · by_cases hBC : Disjoint B C
      · exact Or.inr (Or.inl (pairGraph_p3k2_of_one_intersection
          (by rw [hPairs]; ext E; simp [or_comm])
          hAcard hCcard hBcard hACne hAC hAB (Disjoint.symm hBC)))
      · exact Or.inl (pairGraph_p4_of_two_intersections
          (by rw [hPairs]; ext E; simp [or_comm])
          hAcard hCcard hBcard hAC hAB (fun h ↦ hBC h.symm))
  · by_cases hAC : Disjoint A C
    · by_cases hBC : Disjoint B C
      · exact Or.inr (Or.inl (pairGraph_p3k2_of_one_intersection
          hPairs hAcard hBcard hCcard hABne hAB hAC hBC))
      · exact Or.inl (pairGraph_p4_of_two_intersections
          hPairs hAcard hBcard hCcard hAB hAC hBC)
    · by_cases hBC : Disjoint B C
      · exact Or.inl (pairGraph_p4_of_two_intersections
          (by rw [hPairs]; ext E; simp [or_left_comm])
          hBcard hAcard hCcard (fun h ↦ hAB h.symm) hBC hAC)
      · rcases pairGraph_k3_or_k13_of_pairwise_intersecting hPairs
          hAcard hBcard hCcard hABne hACne hBCne hAB hAC hBC with hK3 | hK13
        · exact Or.inr (Or.inr (Or.inr (Or.inl hK3)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hK13)))

theorem k3_pairGraph_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hDualCard : (blocker H).card = 5)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphK3 H) :
    False := by
  obtain ⟨a, b, c, -, hPairs⟩ := hShape
  have hAB : ({a, b} : Row α) ∈ H := by
    have hMem : ({a, b} : Row α) ∈ pairRows H := by rw [hPairs]; simp
    exact (pair_mem_of_mem_pairRows hMem).1
  have hBC : ({b, c} : Row α) ∈ H := by
    have hMem : ({b, c} : Row α) ∈ pairRows H := by rw [hPairs]; simp
    exact (pair_mem_of_mem_pairRows hMem).1
  have hCA : ({c, a} : Row α) ∈ H := by
    have hMem : ({c, a} : Row α) ∈ pairRows H := by rw [hPairs]; simp
    exact (pair_mem_of_mem_pairRows hMem).1
  exact triangle_blocker_not_maxDegreeThree hAB hBC hCA hDualCard hDualDegree

theorem k13_pairGraph_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hHRows : RowsCardAtLeast H 2)
    (hHDegree : MaxDegreeAtMost H 3)
    (hPairRowsCard : (pairRows H).card = 3)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphK13 H) :
    False := by
  obtain ⟨o, a, b, c, -, hPairs⟩ := hShape
  have hPairSubset : pairRows H ⊆ H.filter (fun E ↦ o ∈ E) := by
    intro E hE
    have hEH := (pair_mem_of_mem_pairRows hE).1
    rw [hPairs] at hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl <;>
      exact Finset.mem_filter.mpr ⟨hEH, by simp⟩
  have hCenterLower : 3 ≤ degree H o := by
    rw [degree]
    simpa [hPairRowsCard] using Finset.card_le_card hPairSubset
  have hCenterDegree : degree H o = 3 := by
    have hUpper := hHDegree o
    omega
  have hAvoidLarge : ∀ E ∈ H, o ∉ E → 3 ≤ E.card := by
    intro E hEH hoE
    have hLower := hHRows E hEH
    by_contra hnot
    have hEcard : E.card = 2 := by omega
    have hEPair : E ∈ pairRows H := Finset.mem_filter.mpr ⟨hEH, hEcard⟩
    rw [hPairs] at hEPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEPair
    rcases hEPair with rfl | rfl | rfl <;> exact hoE (by simp)
  exact star_branch_impossible hH hHcard hCenterDegree hAvoidLarge
    hDualCard hDualRows hDualDegree

end AiMathLab.P0054.G413
