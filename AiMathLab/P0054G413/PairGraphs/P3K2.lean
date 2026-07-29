import AiMathLab.P0054G413.PairGraphs.Restriction

namespace AiMathLab.P0054.G413

theorem pairwise_ne_of_quint_card_eq_five {α : Type*} [DecidableEq α]
    {a b c d e : α} (hCard : ({a, b, c, d, e} : Row α).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧
      b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  have card_four_ne_five (w x y z : α) : ({w, x, y, z} : Row α).card ≠ 5 := by
    have hUpper : ({w, x, y, z} : Row α).card ≤ 4 := Finset.card_le_four
    omega
  constructor
  · intro hab
    subst b
    exact card_four_ne_five a c d e (by simpa using hCard)
  constructor
  · intro hac
    subst c
    exact card_four_ne_five b a d e (by simpa using hCard)
  constructor
  · intro had
    subst d
    exact card_four_ne_five b c a e (by simpa using hCard)
  constructor
  · intro hae
    subst e
    exact card_four_ne_five b c d a (by simpa using hCard)
  constructor
  · intro hbc
    subst c
    exact card_four_ne_five a b d e (by simpa using hCard)
  constructor
  · intro hbd
    subst d
    exact card_four_ne_five a c b e (by simpa using hCard)
  constructor
  · intro hbe
    subst e
    exact card_four_ne_five a c d b (by simpa using hCard)
  constructor
  · intro hcd
    subst d
    exact card_four_ne_five a b c e (by simpa using hCard)
  constructor
  · intro hce
    subst e
    exact card_four_ne_five a b d c (by simpa using hCard)
  · intro hde
    subst e
    exact card_four_ne_five a b c d (by simpa using hCard)

theorem pair_mem_blocker_of_transversal {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hTransversal : IsTransversal K ({x, y} : Row α)) :
    ({x, y} : Row α) ∈ blocker K := by
  obtain ⟨T, hTSubset, hTMinimal⟩ :=
    exists_minimalTransversal_subset hTransversal
  have hTBlocker : T ∈ blocker K := mem_blocker.mpr hTMinimal
  have hTLower : 2 ≤ T.card := hBRows T hTBlocker
  have hTUpper : T.card ≤ ({x, y} : Row α).card :=
    Finset.card_le_card hTSubset
  have hPairUpper : ({x, y} : Row α).card ≤ 2 := Finset.card_le_two
  have hEq : T = {x, y} :=
    Finset.eq_of_subset_of_card_le hTSubset (by omega)
  exact hEq ▸ hTBlocker

theorem mem_row_of_projection {α : Type*} [DecidableEq α]
    {V B R : Row α} {x : α}
    (hProjection : R ∩ V = B) (hxB : x ∈ B) :
    x ∈ R :=
  (Finset.mem_inter.mp (hProjection ▸ hxB)).1

theorem not_mem_row_of_projection {α : Type*} [DecidableEq α]
    {V B R : Row α} {x : α}
    (hProjection : R ∩ V = B) (hxV : x ∈ V) (hxB : x ∉ B) :
    x ∉ R := by
  intro hxR
  exact hxB (hProjection ▸ Finset.mem_inter.mpr ⟨hxR, hxV⟩)

theorem mem_row_iff_of_pointSupport_eq {α : Type*} [DecidableEq α]
    {K S : Hypergraph α} {R : Row α} {x : α}
    (hRK : R ∈ K) (hSupport : pointSupport K x = S) :
    x ∈ R ↔ R ∈ S := by
  rw [← hSupport, mem_pointSupport]
  simp [hRK]

theorem degree_ge_four_of_four_rows {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {A B C D : Row α}
    (hA : A ∈ H) (hB : B ∈ H) (hC : C ∈ H) (hD : D ∈ H)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxC : x ∈ C) (hxD : x ∈ D) :
    4 ≤ degree H x := by
  let Q : Hypergraph α := {A, B, C, D}
  have hQcard : Q.card = 4 := by
    simp [Q, hAB, hAC, hAD, hBC, hBD, hCD]
  have hQSubset : Q ⊆ pointSupport H x := by
    intro T hT
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact mem_pointSupport.mpr ⟨hA, hxA⟩
    · exact mem_pointSupport.mpr ⟨hB, hxB⟩
    · exact mem_pointSupport.mpr ⟨hC, hxC⟩
    · exact mem_pointSupport.mpr ⟨hD, hxD⟩
  have hCard := Finset.card_le_card hQSubset
  simpa [hQcard, pointSupport_card] using hCard

theorem triple_mem_blocker_of_private_rows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y z : α} {Rx Ry Rz : Row α}
    (hTransversal : IsTransversal K ({x, y, z} : Row α))
    (hRx : Rx ∈ K) (hxRx : x ∈ Rx) (hyRx : y ∉ Rx) (hzRx : z ∉ Rx)
    (hRy : Ry ∈ K) (hyRy : y ∈ Ry) (hxRy : x ∉ Ry) (hzRy : z ∉ Ry)
    (hRz : Rz ∈ K) (hzRz : z ∈ Rz) (hxRz : x ∉ Rz) (hyRz : y ∉ Rz) :
    ({x, y, z} : Row α) ∈ blocker K := by
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨Rx, hRx, by simp, hxRx, ?_⟩
    intro w hwTriple hwRx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple
    rcases hwTriple with hwx | hwy | hwz
    · exact hwx
    · exact (hyRx (hwy ▸ hwRx)).elim
    · exact (hzRx (hwz ▸ hwRx)).elim
  · refine ⟨Ry, hRy, by simp, hyRy, ?_⟩
    intro w hwTriple hwRy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple
    rcases hwTriple with hwx | hwy | hwz
    · exact (hxRy (hwx ▸ hwRy)).elim
    · exact hwy
    · exact (hzRy (hwz ▸ hwRy)).elim
  · refine ⟨Rz, hRz, by simp, hzRz, ?_⟩
    intro w hwTriple hwRz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple
    rcases hwTriple with hwx | hwy | hwz
    · exact (hxRz (hwx ▸ hwRz)).elim
    · exact (hyRz (hwy ▸ hwRz)).elim
    · exact hwz

theorem quad_mem_blocker_of_private_rows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {w x y z : α} {Rw Rx Ry Rz : Row α}
    (hTransversal : IsTransversal K ({w, x, y, z} : Row α))
    (hRwK : Rw ∈ K) (hwRw : w ∈ Rw) (hxRw : x ∉ Rw)
    (hyRw : y ∉ Rw) (hzRw : z ∉ Rw)
    (hRxK : Rx ∈ K) (hxRx : x ∈ Rx) (hwRx : w ∉ Rx)
    (hyRx : y ∉ Rx) (hzRx : z ∉ Rx)
    (hRyK : Ry ∈ K) (hyRy : y ∈ Ry) (hwRy : w ∉ Ry)
    (hxRy : x ∉ Ry) (hzRy : z ∉ Ry)
    (hRzK : Rz ∈ K) (hzRz : z ∈ Rz) (hwRz : w ∉ Rz)
    (hxRz : x ∉ Rz) (hyRz : y ∉ Rz) :
    ({w, x, y, z} : Row α) ∈ blocker K := by
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with htw | htx | hty | htz
  · subst t
    refine ⟨Rw, hRwK, by simp, hwRw, ?_⟩
    intro t htT htRw
    simp only [Finset.mem_insert, Finset.mem_singleton] at htT
    rcases htT with htw | htx | hty | htz
    · exact htw
    · exact (hxRw (htx ▸ htRw)).elim
    · exact (hyRw (hty ▸ htRw)).elim
    · exact (hzRw (htz ▸ htRw)).elim
  · subst t
    refine ⟨Rx, hRxK, by simp, hxRx, ?_⟩
    intro t htT htRx
    simp only [Finset.mem_insert, Finset.mem_singleton] at htT
    rcases htT with htw | htx | hty | htz
    · exact (hwRx (htw ▸ htRx)).elim
    · exact htx
    · exact (hyRx (hty ▸ htRx)).elim
    · exact (hzRx (htz ▸ htRx)).elim
  · subst t
    refine ⟨Ry, hRyK, by simp, hyRy, ?_⟩
    intro t htT htRy
    simp only [Finset.mem_insert, Finset.mem_singleton] at htT
    rcases htT with htw | htx | hty | htz
    · exact (hwRy (htw ▸ htRy)).elim
    · exact (hxRy (htx ▸ htRy)).elim
    · exact hty
    · exact (hzRy (htz ▸ htRy)).elim
  · subst t
    refine ⟨Rz, hRzK, by simp, hzRz, ?_⟩
    intro t htT htRz
    simp only [Finset.mem_insert, Finset.mem_singleton] at htT
    rcases htT with htw | htx | hty | htz
    · exact (hwRz (htw ▸ htRz)).elim
    · exact (hxRz (htx ▸ htRz)).elim
    · exact (hyRz (hty ▸ htRz)).elim
    · exact htz

theorem p3k2_u_pressure_impossible {α : Type*} [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v r s : α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hUV : ({u, v} : Row α) ∈ blocker K)
    (hAUR : ({a, u, r} : Row α) ∈ blocker K)
    (hQUR : ({q, u, r} : Row α) ∈ blocker K)
    (hPUS : ({p, u, s} : Row α) ∈ blocker K)
    (hra : r ≠ a) (hrp : r ≠ p) (hrq : r ≠ q)
    (hru : r ≠ u) (hrv : r ≠ v)
    (hsa : s ≠ a) (hsp : s ≠ p) (hsq : s ≠ q)
    (hsu : s ≠ u) (hsv : s ≠ v) :
    False := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hLower := degree_ge_four_of_four_rows (x := u) hUV hAUR hQUR hPUS
    (by
      intro hEq
      have hvRight : v ∈ ({a, u, r} : Row α) := by rw [← hEq]; simp
      simpa [hav.symm, huv.symm, hrv.symm] using hvRight)
    (by
      intro hEq
      have hvRight : v ∈ ({q, u, r} : Row α) := by rw [← hEq]; simp
      simpa [hqv.symm, huv.symm, hrv.symm] using hvRight)
    (by
      intro hEq
      have hvRight : v ∈ ({p, u, s} : Row α) := by rw [← hEq]; simp
      simpa [hpv.symm, huv.symm, hsv.symm] using hvRight)
    (by
      intro hEq
      have haRight : a ∈ ({q, u, r} : Row α) := by rw [← hEq]; simp
      simpa [haq, hau, hra.symm] using haRight)
    (by
      intro hEq
      have haRight : a ∈ ({p, u, s} : Row α) := by rw [← hEq]; simp
      simpa [hap, hau, hsa.symm] using haRight)
    (by
      intro hEq
      have hqRight : q ∈ ({p, u, s} : Row α) := by rw [← hEq]; simp
      simpa [hpq.symm, hqu, hsq.symm] using hqRight)
    (by simp) (by simp) (by simp) (by simp)
  exact (not_le_of_gt hLower) (hBDegree u)

theorem support_union_ne_of_not_pairRow {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hNotPair : ({x, y} : Row α) ∉ pairRows (blocker K)) :
    pointSupport K x ∪ pointSupport K y ≠ K := by
  intro hUnion
  have hTransversal : IsTransversal K ({x, y} : Row α) := by
    intro R hRK
    have hRSupport : R ∈ pointSupport K x ∪ pointSupport K y := by
      rw [hUnion]
      exact hRK
    rcases Finset.mem_union.mp hRSupport with hxR | hyR
    · exact ⟨x, by simp, (mem_pointSupport.mp hxR).2⟩
    · exact ⟨y, by simp, (mem_pointSupport.mp hyR).2⟩
  have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
  apply hNotPair
  exact Finset.mem_filter.mpr ⟨hPair, by
    have hLower := hBRows {x, y} hPair
    have hUpper : ({x, y} : Row α).card ≤ 2 := Finset.card_le_two
    omega⟩

theorem inter_nonempty_of_cross_union_ne {β : Type*} [DecidableEq β]
    {K A P U V : Finset β}
    (hAP : A ∪ P = K) (hUV : U ∪ V = K)
    (hNe : A ∪ U ≠ K) :
    (P ∩ V).Nonempty := by
  by_contra hEmpty
  apply hNe
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxU
    · rw [← hAP]
      exact Finset.mem_union_left _ hxA
    · rw [← hUV]
      exact Finset.mem_union_left _ hxU
  · intro x hxK
    have hxAP : x ∈ A ∪ P := by rw [hAP]; exact hxK
    rcases Finset.mem_union.mp hxAP with hxA | hxP
    · exact Finset.mem_union_left _ hxA
    · have hxUV : x ∈ U ∪ V := by rw [hUV]; exact hxK
      rcases Finset.mem_union.mp hxUV with hxU | hxV
      · exact Finset.mem_union_right _ hxU
      · exact (hEmpty ⟨x, Finset.mem_inter.mpr ⟨hxP, hxV⟩⟩).elim

theorem inter_union_inter_eq_of_partition {β : Type*} [DecidableEq β]
    {K A U V : Finset β}
    (hUV : U ∪ V = K) (hAK : A ⊆ K) :
    (A ∩ U) ∪ (A ∩ V) = A := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hxAU | hxAV
    · exact (Finset.mem_inter.mp hxAU).1
    · exact (Finset.mem_inter.mp hxAV).1
  · intro x hxA
    have hxK := hAK hxA
    have hxUV : x ∈ U ∪ V := by rw [hUV]; exact hxK
    rcases Finset.mem_union.mp hxUV with hxU | hxV
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxU⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxA, hxV⟩)

theorem card_inter_add_card_inter_of_partition {β : Type*} [DecidableEq β]
    {K A U V : Finset β}
    (hUV : U ∪ V = K) (hDisjoint : Disjoint U V) (hAK : A ⊆ K) :
    (A ∩ U).card + (A ∩ V).card = A.card := by
  have hInterDisjoint : Disjoint (A ∩ U) (A ∩ V) := by
    rw [Finset.disjoint_left]
    intro x hxAU hxAV
    exact Finset.disjoint_left.mp hDisjoint
      (Finset.mem_inter.mp hxAU).2 (Finset.mem_inter.mp hxAV).2
  have hSplit := inter_union_inter_eq_of_partition hUV hAK
  calc
    (A ∩ U).card + (A ∩ V).card = ((A ∩ U) ∪ (A ∩ V)).card :=
      (Finset.card_union_of_disjoint hInterDisjoint).symm
    _ = A.card := by rw [hSplit]

theorem two_three_partitions_normal_form {β : Type*} [DecidableEq β]
    {K A P U V : Finset β}
    (hAP : A ∪ P = K) (hUV : U ∪ V = K)
    (hAPDisjoint : Disjoint A P) (hUVDisjoint : Disjoint U V)
    (hAcard : A.card = 2) (hPcard : P.card = 3)
    (hUcard : U.card = 3) (hVcard : V.card = 2)
    (hAU : A ∪ U ≠ K) (hAV : A ∪ V ≠ K)
    (hPU : P ∪ U ≠ K) (hPV : P ∪ V ≠ K) :
    ∃ R0 R1 R2 R3 R4,
      ({R0, R1, R2, R3, R4} : Finset β).card = 5 ∧
      K = {R0, R1, R2, R3, R4} ∧
      A = {R2, R4} ∧ P = {R0, R1, R3} ∧
      U = {R0, R1, R2} ∧ V = {R3, R4} := by
  have hAK : A ⊆ K := by
    intro x hx
    rw [← hAP]
    exact Finset.mem_union_left _ hx
  have hPK : P ⊆ K := by
    intro x hx
    rw [← hAP]
    exact Finset.mem_union_right _ hx
  have hUK : U ⊆ K := by
    intro x hx
    rw [← hUV]
    exact Finset.mem_union_left _ hx
  have hVK : V ⊆ K := by
    intro x hx
    rw [← hUV]
    exact Finset.mem_union_right _ hx
  have hAUNonempty : (A ∩ U).Nonempty :=
    inter_nonempty_of_cross_union_ne (by simpa [Finset.union_comm] using hAP)
      (by simpa [Finset.union_comm] using hUV) (by simpa [Finset.union_comm] using hPV)
  have hAVNonempty : (A ∩ V).Nonempty :=
    inter_nonempty_of_cross_union_ne (by simpa [Finset.union_comm] using hAP)
      hUV (by simpa [Finset.union_comm] using hPU)
  have hPUNonempty : (P ∩ U).Nonempty :=
    inter_nonempty_of_cross_union_ne hAP
      (by simpa [Finset.union_comm] using hUV) hAV
  have hPVNonempty : (P ∩ V).Nonempty :=
    inter_nonempty_of_cross_union_ne hAP hUV hAU
  have hASplit := card_inter_add_card_inter_of_partition hUV hUVDisjoint hAK
  have hAUCard : (A ∩ U).card = 1 := by
    have hAULower := Finset.card_pos.mpr hAUNonempty
    have hAVLower := Finset.card_pos.mpr hAVNonempty
    omega
  have hAVCard : (A ∩ V).card = 1 := by
    have hAULower := Finset.card_pos.mpr hAUNonempty
    have hAVLower := Finset.card_pos.mpr hAVNonempty
    omega
  have hUSplit := card_inter_add_card_inter_of_partition hAP hAPDisjoint hUK
  have hPUCard : (P ∩ U).card = 2 := by
    have hPUpos := Finset.card_pos.mpr hPUNonempty
    have hUA : U ∩ A = A ∩ U := Finset.inter_comm U A
    have hUP : U ∩ P = P ∩ U := Finset.inter_comm U P
    rw [hUA, hUP, hAUCard, hUcard] at hUSplit
    omega
  have hVSplit := card_inter_add_card_inter_of_partition hAP hAPDisjoint hVK
  have hPVCard : (P ∩ V).card = 1 := by
    have hPVpos := Finset.card_pos.mpr hPVNonempty
    have hVA : V ∩ A = A ∩ V := Finset.inter_comm V A
    have hVP : V ∩ P = P ∩ V := Finset.inter_comm V P
    rw [hVA, hVP, hAVCard, hVcard] at hVSplit
    omega
  obtain ⟨R2, hAUEq⟩ := Finset.card_eq_one.mp hAUCard
  obtain ⟨R4, hAVEq⟩ := Finset.card_eq_one.mp hAVCard
  obtain ⟨R0, R1, hR0R1, hPUEq⟩ := Finset.card_eq_two.mp hPUCard
  obtain ⟨R3, hPVEq⟩ := Finset.card_eq_one.mp hPVCard
  have hAEq : A = {R2, R4} := by
    rw [← inter_union_inter_eq_of_partition hUV hAK, hAUEq, hAVEq]
    simp
  have hPEq : P = {R0, R1, R3} := by
    rw [← inter_union_inter_eq_of_partition hUV hPK, hPUEq, hPVEq]
    simp
  have hUEq : U = {R0, R1, R2} := by
    rw [← inter_union_inter_eq_of_partition hAP hUK]
    rw [Finset.inter_comm U A, Finset.inter_comm U P, hAUEq, hPUEq]
    ext x
    simp [or_comm, or_left_comm]
  have hVEq : V = {R3, R4} := by
    rw [← inter_union_inter_eq_of_partition hAP hVK]
    rw [Finset.inter_comm V A, Finset.inter_comm V P, hAVEq, hPVEq]
    ext x
    simp [or_comm]
  have hKCard : K.card = 5 := by
    rw [← hAP, Finset.card_union_of_disjoint hAPDisjoint, hAcard, hPcard]
  have hKForm : K = {R0, R1, R2, R3, R4} := by
    rw [← hAP, hAEq, hPEq]
    ext x
    simp [or_comm, or_left_comm]
  refine ⟨R0, R1, R2, R3, R4, ?_, hKForm, hAEq, hPEq, hUEq, hVEq⟩
  rw [← hKForm]
  exact hKCard

theorem two_three_single_intersection_normal_form {β : Type*} [DecidableEq β]
    {K A P U V : Finset β}
    (hAP : A ∪ P = K) (hUV : U ∪ V = K)
    (hAPDisjoint : Disjoint A P)
    (hAcard : A.card = 2) (hPcard : P.card = 3)
    (hUcard : U.card = 3) (hVcard : V.card = 3)
    (hUVInter : (U ∩ V).card = 1)
    (hAU : A ∪ U ≠ K) (hAV : A ∪ V ≠ K)
    (hPU : P ∪ U ≠ K) (hPV : P ∪ V ≠ K) :
    ∃ R0 R1 R2 R3 R4,
      ({R0, R1, R2, R3, R4} : Finset β).card = 5 ∧
      K = {R0, R1, R2, R3, R4} ∧
      A = {R1, R3} ∧ P = {R0, R2, R4} ∧
      U = {R0, R1, R4} ∧ V = {R2, R3, R4} := by
  let U0 := U \ V
  let V0 := V \ U
  let W := U ∩ V
  have hKCard : K.card = 5 := by
    rw [← hAP, Finset.card_union_of_disjoint hAPDisjoint, hAcard, hPcard]
  have hU0Card : U0.card = 2 := by
    have hCard := Finset.card_sdiff_add_card_inter U V
    simpa [U0, W, hUVInter, hUcard] using hCard
  have hV0Card : V0.card = 2 := by
    have hCard := Finset.card_sdiff_add_card_inter V U
    have hInterComm : V ∩ U = U ∩ V := Finset.inter_comm V U
    rw [hInterComm, hUVInter, hVcard] at hCard
    simpa [V0] using hCard
  have hVUnionU0 : V ∪ U0 = K := by
    rw [← hUV]
    ext x
    simp [U0, or_comm]
  have hUUnionV0 : U ∪ V0 = K := by
    rw [← hUV]
    ext x
    simp [V0]
  have hA_U0_nonempty : (A ∩ U0).Nonempty :=
    inter_nonempty_of_cross_union_ne (by simpa [Finset.union_comm] using hAP)
      hVUnionU0 hPV
  have hA_V0_nonempty : (A ∩ V0).Nonempty :=
    inter_nonempty_of_cross_union_ne (by simpa [Finset.union_comm] using hAP)
      hUUnionV0 hPU
  have hP_U0_nonempty : (P ∩ U0).Nonempty :=
    inter_nonempty_of_cross_union_ne hAP hVUnionU0 hAV
  have hP_V0_nonempty : (P ∩ V0).Nonempty :=
    inter_nonempty_of_cross_union_ne hAP hUUnionV0 hAU
  have hU0V0Disjoint : Disjoint U0 V0 := by
    rw [Finset.disjoint_left]
    intro x hxU0 hxV0
    exact (Finset.mem_sdiff.mp hxU0).2 (Finset.mem_sdiff.mp hxV0).1
  have hAInterDisjoint : Disjoint (A ∩ U0) (A ∩ V0) := by
    rw [Finset.disjoint_left]
    intro x hxAU hxAV
    exact Finset.disjoint_left.mp hU0V0Disjoint
      (Finset.mem_inter.mp hxAU).2 (Finset.mem_inter.mp hxAV).2
  have hAInterSubset : (A ∩ U0) ∪ (A ∩ V0) ⊆ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxAU | hxAV
    · exact (Finset.mem_inter.mp hxAU).1
    · exact (Finset.mem_inter.mp hxAV).1
  have hAInterCardUpper :
      (A ∩ U0).card + (A ∩ V0).card ≤ 2 := by
    rw [← Finset.card_union_of_disjoint hAInterDisjoint, ← hAcard]
    exact Finset.card_le_card hAInterSubset
  have hA_U0_card : (A ∩ U0).card = 1 := by
    have hLeft := Finset.card_pos.mpr hA_U0_nonempty
    have hRight := Finset.card_pos.mpr hA_V0_nonempty
    omega
  have hA_V0_card : (A ∩ V0).card = 1 := by
    have hLeft := Finset.card_pos.mpr hA_U0_nonempty
    have hRight := Finset.card_pos.mpr hA_V0_nonempty
    omega
  have hU0K : U0 ⊆ K := by
    intro x hx
    rw [← hUV]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
  have hV0K : V0 ⊆ K := by
    intro x hx
    rw [← hUV]
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1
  have hU0Split := card_inter_add_card_inter_of_partition hAP hAPDisjoint hU0K
  have hP_U0_card : (P ∩ U0).card = 1 := by
    have hU0A : U0 ∩ A = A ∩ U0 := Finset.inter_comm U0 A
    have hU0P : U0 ∩ P = P ∩ U0 := Finset.inter_comm U0 P
    rw [hU0A, hU0P, hA_U0_card, hU0Card] at hU0Split
    omega
  have hV0Split := card_inter_add_card_inter_of_partition hAP hAPDisjoint hV0K
  have hP_V0_card : (P ∩ V0).card = 1 := by
    have hV0A : V0 ∩ A = A ∩ V0 := Finset.inter_comm V0 A
    have hV0P : V0 ∩ P = P ∩ V0 := Finset.inter_comm V0 P
    rw [hV0A, hV0P, hA_V0_card, hV0Card] at hV0Split
    omega
  obtain ⟨R1, hA_U0_eq⟩ := Finset.card_eq_one.mp hA_U0_card
  obtain ⟨R3, hA_V0_eq⟩ := Finset.card_eq_one.mp hA_V0_card
  obtain ⟨R0, hP_U0_eq⟩ := Finset.card_eq_one.mp hP_U0_card
  obtain ⟨R2, hP_V0_eq⟩ := Finset.card_eq_one.mp hP_V0_card
  obtain ⟨R4, hWEq⟩ := Finset.card_eq_one.mp (by simpa [W] using hUVInter)
  have hWEq' : W = {R4} := by
    change U ∩ V = {R4}
    exact hWEq
  have hAEq : A = {R1, R3} := by
    have hUnionCard : ((A ∩ U0) ∪ (A ∩ V0)).card = 2 := by
      rw [Finset.card_union_of_disjoint hAInterDisjoint, hA_U0_card, hA_V0_card]
    have hEq : (A ∩ U0) ∪ (A ∩ V0) = A :=
      Finset.eq_of_subset_of_card_le hAInterSubset (by rw [hUnionCard, hAcard])
    rw [hA_U0_eq, hA_V0_eq] at hEq
    simpa using hEq.symm
  have hR0P : R0 ∈ P := by
    have : R0 ∈ P ∩ U0 := by rw [hP_U0_eq]; simp
    exact (Finset.mem_inter.mp this).1
  have hR2P : R2 ∈ P := by
    have : R2 ∈ P ∩ V0 := by rw [hP_V0_eq]; simp
    exact (Finset.mem_inter.mp this).1
  have hR4U : R4 ∈ U := by
    have : R4 ∈ W := by rw [hWEq']; simp
    change R4 ∈ U ∩ V at this
    exact (Finset.mem_inter.mp this).1
  have hR4V : R4 ∈ V := by
    have : R4 ∈ W := by rw [hWEq']; simp
    change R4 ∈ U ∩ V at this
    exact (Finset.mem_inter.mp this).2
  have hR4K : R4 ∈ K := by
    rw [← hUV]
    exact Finset.mem_union_left _ hR4U
  have hR4A : R4 ∉ A := by
    rw [hAEq]
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · have hR1U0 : R1 ∈ U0 := by
        have : R1 ∈ A ∩ U0 := by rw [hA_U0_eq]; simp
        exact (Finset.mem_inter.mp this).2
      exact (Finset.mem_sdiff.mp hR1U0).2 (h ▸ hR4V)
    · have hR3V0 : R3 ∈ V0 := by
        have : R3 ∈ A ∩ V0 := by rw [hA_V0_eq]; simp
        exact (Finset.mem_inter.mp this).2
      exact (Finset.mem_sdiff.mp hR3V0).2 (h ▸ hR4U)
  have hR4P : R4 ∈ P := by
    have hR4AP : R4 ∈ A ∪ P := by rw [hAP]; exact hR4K
    rcases Finset.mem_union.mp hR4AP with h | h
    · exact (hR4A h).elim
    · exact h
  have hR0R2 : R0 ≠ R2 := by
    have hR0U0 : R0 ∈ U0 := by
      have : R0 ∈ P ∩ U0 := by rw [hP_U0_eq]; simp
      exact (Finset.mem_inter.mp this).2
    have hR2V0 : R2 ∈ V0 := by
      have : R2 ∈ P ∩ V0 := by rw [hP_V0_eq]; simp
      exact (Finset.mem_inter.mp this).2
    intro h
    exact Finset.disjoint_left.mp hU0V0Disjoint hR0U0 (h ▸ hR2V0)
  have hR0R4 : R0 ≠ R4 := by
    have hR0U0 : R0 ∈ U0 := by
      have : R0 ∈ P ∩ U0 := by rw [hP_U0_eq]; simp
      exact (Finset.mem_inter.mp this).2
    intro h
    exact (Finset.mem_sdiff.mp hR0U0).2 (h ▸ hR4V)
  have hR2R4 : R2 ≠ R4 := by
    have hR2V0 : R2 ∈ V0 := by
      have : R2 ∈ P ∩ V0 := by rw [hP_V0_eq]; simp
      exact (Finset.mem_inter.mp this).2
    intro h
    exact (Finset.mem_sdiff.mp hR2V0).2 (h ▸ hR4U)
  have hPEq : P = {R0, R2, R4} := by
    have hSubset : ({R0, R2, R4} : Finset β) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hR0P
      · exact hR2P
      · exact hR4P
    have hThreeCard : ({R0, R2, R4} : Finset β).card = 3 := by
      simp [hR0R2, hR0R4, hR2R4]
    exact (Finset.eq_of_subset_of_card_le hSubset (by rw [hPcard, hThreeCard])).symm
  have hU0Eq : U0 = {R0, R1} := by
    rw [← inter_union_inter_eq_of_partition hAP hU0K]
    rw [Finset.inter_comm U0 A, Finset.inter_comm U0 P, hA_U0_eq, hP_U0_eq]
    ext x
    simp [or_comm]
  have hV0Eq : V0 = {R2, R3} := by
    rw [← inter_union_inter_eq_of_partition hAP hV0K]
    rw [Finset.inter_comm V0 A, Finset.inter_comm V0 P, hA_V0_eq, hP_V0_eq]
    ext x
    simp [or_comm]
  have hUEq : U = {R0, R1, R4} := by
    have hUDecomp : U0 ∪ W = U := by
      simpa [U0, W] using Finset.sdiff_union_inter U V
    rw [← hUDecomp, hU0Eq, hWEq']
    ext x
    simp [or_comm, or_left_comm]
  have hVEq : V = {R2, R3, R4} := by
    have hVDecomp : V0 ∪ W = V := by
      simpa [V0, W, Finset.inter_comm] using Finset.sdiff_union_inter V U
    rw [← hVDecomp, hV0Eq, hWEq']
    ext x
    simp [or_comm, or_left_comm]
  have hKForm : K = {R0, R1, R2, R3, R4} := by
    rw [← hUV, hUEq, hVEq]
    ext x
    simp [or_comm, or_left_comm]
  refine ⟨R0, R1, R2, R3, R4, ?_, hKForm, hAEq, hPEq, hUEq, hVEq⟩
  rw [← hKForm]
  exact hKCard

theorem path_endpoint_three_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y z : α} {P Q R : Row α}
    (hP : P ∈ K) (hQ : Q ∈ K) (hR : R ∈ K)
    (hxP : x ∉ P) (hxQ : x ∉ Q) (hxR : x ∈ R)
    (hMiss : ∀ F ∈ K, x ∉ F → F = P ∨ F = Q)
    (hyP : y ∈ P) (hyQ : y ∉ Q) (hyR : y ∉ R)
    (hzP : z ∉ P) (hzQ : z ∈ Q) (hzR : z ∉ R) :
    ({x, y, z} : Row α) ∈ blocker K := by
  have hxy : x ≠ y := fun h ↦ hxP (h ▸ hyP)
  have hxz : x ≠ z := fun h ↦ hxQ (h ▸ hzQ)
  have hyz : y ≠ z := fun h ↦ hyQ (h ▸ hzQ)
  apply mem_blocker.mpr
  have hTransversal : IsTransversal K {x, y, z} := by
    intro F hFK
    by_cases hFx : F = P
    · subst F
      exact ⟨y, by simp, hyP⟩
    by_cases hFQ : F = Q
    · subst F
      exact ⟨z, by simp, hzQ⟩
    by_cases hxF : x ∈ F
    · exact ⟨x, by simp, hxF⟩
    rcases hMiss F hFK hxF with hFP | hFQ'
    · exact (hFx hFP).elim
    · exact (hFQ hFQ').elim
  apply hTransversal.minimal_of_privateRows
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨R, hR, by simp, hxR, ?_⟩
    intro w hwSet hwR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwSet
    rcases hwSet with hwx | hwy | hwz
    · exact hwx
    · exact (hyR (hwy ▸ hwR)).elim
    · exact (hzR (hwz ▸ hwR)).elim
  · refine ⟨P, hP, by simp, hyP, ?_⟩
    intro w hwSet hwP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwSet
    rcases hwSet with hwx | hwy | hwz
    · exact (hxP (hwx ▸ hwP)).elim
    · exact hwy
    · exact (hzP (hwz ▸ hwP)).elim
  · refine ⟨Q, hQ, by simp, hzQ, ?_⟩
    intro w hwSet hwQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwSet
    rcases hwSet with hwx | hwy | hwz
    · exact (hxQ (hwx ▸ hwQ)).elim
    · exact (hyQ (hwy ▸ hwQ)).elim
    · exact hwz

theorem p3k2_path_endpoint_fan_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x p q u v : α} {P Q : Row α}
    (hxp : x ≠ p)
    (hKRows : RowsCardAtLeast K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{x, p}, {p, q}, {u, v}})
    (hP : P ∈ K) (hQ : Q ∈ K)
    (hxP : x ∉ P) (hxQ : x ∉ Q) (hpP : p ∈ P) (hpQ : p ∈ Q)
    (hMiss : ∀ R ∈ K, x ∉ R → R = P ∨ R = Q)
    (hInter : P ∩ Q = {p}) :
    False := by
  let A := P.erase p
  let B := Q.erase p
  have hAcard : 2 ≤ A.card := by
    change 2 ≤ (P.erase p).card
    rw [Finset.card_erase_of_mem hpP]
    have := hKRows P hP
    omega
  have hBcard : 2 ≤ B.card := by
    change 2 ≤ (Q.erase p).card
    rw [Finset.card_erase_of_mem hpQ]
    have := hKRows Q hQ
    omega
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y hyA hyB
    obtain ⟨hyp, hyP⟩ := Finset.mem_erase.mp hyA
    obtain ⟨-, hyQ⟩ := Finset.mem_erase.mp hyB
    have hyInter : y ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hyP, hyQ⟩
    rw [hInter] at hyInter
    exact hyp (by simpa using hyInter)
  let Cross := crossPairRows A B
  have hCrossCard : 4 ≤ Cross.card := by
    have hProduct := card_mul_le_crossPairRows_card_of_disjoint hAB
    calc
      4 = 2 * 2 := rfl
      _ ≤ A.card * B.card := Nat.mul_le_mul hAcard hBcard
      _ ≤ Cross.card := by simpa [Cross] using hProduct
  have hxCross : ∀ D ∈ Cross, x ∉ D := by
    intro D hD hxD
    obtain ⟨y, hyA, z, hzB, hPair⟩ := mem_crossPairRows.mp hD
    rw [← hPair] at hxD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxD
    rcases hxD with hxy | hxz
    · exact hxP (hxy ▸ Finset.mem_of_mem_erase hyA)
    · exact hxQ (hxz ▸ Finset.mem_of_mem_erase hzB)
  have hpCross : ∀ D ∈ Cross, p ∉ D := by
    intro D hD hpD
    obtain ⟨y, hyA, z, hzB, hPair⟩ := mem_crossPairRows.mp hD
    rw [← hPair] at hpD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpD
    rcases hpD with hpy | hpz
    · exact (Finset.mem_erase.mp hyA).1 hpy.symm
    · exact (Finset.mem_erase.mp hzB).1 hpz.symm
  have hPairCrossSubset : Cross ∩ pairRows (blocker K) ⊆ {{u, v}} := by
    intro D hD
    obtain ⟨hDCross, hDPair⟩ := Finset.mem_inter.mp hD
    rw [hPairs] at hDPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hDPair
    rcases hDPair with hEq | hEq | hEq
    · exact (hxCross D hDCross (hEq ▸ by simp)).elim
    · exact (hpCross D hDCross (hEq ▸ by simp)).elim
    · simpa [hEq]
  have hPairCrossCard : (Cross ∩ pairRows (blocker K)).card ≤ 1 :=
    (Finset.card_le_card hPairCrossSubset).trans (by simp)
  have hPairCrossCard' : (pairRows (blocker K) ∩ Cross).card ≤ 1 := by
    simpa [Finset.inter_comm] using hPairCrossCard
  let Good := Cross \ pairRows (blocker K)
  have hGoodCard : 3 ≤ Good.card := by
    change 3 ≤ (Cross \ pairRows (blocker K)).card
    rw [Finset.card_sdiff]
    omega
  have hGoodLift : ∀ D ∈ Good, insert x D ∈ blocker K := by
    intro D hD
    obtain ⟨hDCross, hDNotPair⟩ := Finset.mem_sdiff.mp hD
    obtain ⟨y, hyA, z, hzB, hPair⟩ := mem_crossPairRows.mp hDCross
    have hyP : y ∈ P := Finset.mem_of_mem_erase hyA
    have hzQ : z ∈ Q := Finset.mem_of_mem_erase hzB
    have hyp : y ≠ p := (Finset.mem_erase.mp hyA).1
    have hzp : z ≠ p := (Finset.mem_erase.mp hzB).1
    have hyQ : y ∉ Q := by
      intro hyQ
      have hyInter : y ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hyP, hyQ⟩
      rw [hInter] at hyInter
      exact hyp (by simpa using hyInter)
    have hzP : z ∉ P := by
      intro hzP
      have hzInter : z ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hzP, hzQ⟩
      rw [hInter] at hzInter
      exact hzp (by simpa using hzInter)
    have hyz : y ≠ z := fun h ↦ hyQ (h ▸ hzQ)
    have hDcard : D.card = 2 := by rw [← hPair]; simp [hyz]
    have hDNotBlocker : D ∉ blocker K := by
      intro hDb
      exact hDNotPair (Finset.mem_filter.mpr ⟨hDb, hDcard⟩)
    have hPairNotBlocker : ({y, z} : Row α) ∉ blocker K := by
      rw [hPair]
      exact hDNotBlocker
    obtain ⟨R, hR, hyR, hzR⟩ :=
      exists_row_avoiding_nonblocker_pair hBRows hPairNotBlocker
    have hxR : x ∈ R := by
      by_contra hxR
      rcases hMiss R hR hxR with hRP | hRQ
      · exact hyR (hRP ▸ hyP)
      · exact hzR (hRQ ▸ hzQ)
    have hTriple := path_endpoint_three_blocker hP hQ hR hxP hxQ hxR hMiss
      hyP hyQ hyR hzP hzQ hzR
    simpa [hPair, Finset.insert_comm x y] using hTriple
  let Lifts : Hypergraph α := Good.image (insert x)
  have hLiftInjective : Set.InjOn (insert x) (↑Good : Set (Row α)) := by
    intro D hD E hE hEq
    have hxD : x ∉ D := hxCross D (Finset.mem_sdiff.mp hD).1
    have hxE : x ∉ E := hxCross E (Finset.mem_sdiff.mp hE).1
    simpa [hxD, hxE] using congrArg (Finset.erase · x) hEq
  have hLiftsCard : Lifts.card = Good.card :=
    Finset.card_image_iff.mpr hLiftInjective
  have hFixed : ({x, p} : Row α) ∈ blocker K := by
    have hPairMem : ({x, p} : Row α) ∈ pairRows (blocker K) := by
      rw [hPairs]
      simp
    exact (pair_mem_of_mem_pairRows hPairMem).1
  have hFixedNotLifts : ({x, p} : Row α) ∉ Lifts := by
    intro hMem
    obtain ⟨D, hDGood, hEq⟩ := Finset.mem_image.mp hMem
    have hDCross := (Finset.mem_sdiff.mp hDGood).1
    obtain ⟨y, hyA, z, hzB, hPair⟩ := mem_crossPairRows.mp hDCross
    have hyz : y ≠ z := fun h ↦
      Finset.disjoint_left.mp hAB hyA (h ▸ hzB)
    have hxD : x ∉ D := hxCross D hDCross
    have hLiftCard : (insert x D).card = 3 := by
      rw [Finset.card_insert_of_notMem hxD, ← hPair]
      simp [hyz]
    have hFixedCard : ({x, p} : Row α).card = 2 := by simp [hxp]
    have hEqualCard := congrArg Finset.card hEq
    omega
  have hAllSubset : insert {x, p} Lifts ⊆ pointSupport (blocker K) x := by
    intro T hT
    simp only [Finset.mem_insert] at hT
    rcases hT with rfl | hTLifts
    · exact mem_pointSupport.mpr ⟨hFixed, by simp⟩
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hTLifts
      exact mem_pointSupport.mpr ⟨hGoodLift D hD, by simp⟩
  have hAllCard : 4 ≤ (insert ({x, p} : Row α) Lifts).card := by
    rw [Finset.card_insert_of_notMem hFixedNotLifts, hLiftsCard]
    omega
  have hDegreeLower : 4 ≤ degree (blocker K) x := by
    rw [← pointSupport_card]
    exact hAllCard.trans (Finset.card_le_card hAllSubset)
  exact (by have := hBDegree x; omega)

theorem p3k2_path_endpoint_intersection {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x p q u v : α} {P Q : Row α}
    (hVertices : ({x, p, q, u, v} : Row α).card = 5)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{x, p}, {p, q}, {u, v}})
    (hP : P ∈ K) (hQ : Q ∈ K)
    (hxP : x ∉ P) (hxQ : x ∉ Q) (hpP : p ∈ P) (hpQ : p ∈ Q)
    (hMiss : ∀ R ∈ K, x ∉ R → R = P ∨ R = Q) :
    P ∩ Q = {p} := by
  obtain ⟨hxp, hxq, hxu, hxv, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨hwP, hwQ⟩ := Finset.mem_inter.mp hw
    have hwx : w ≠ x := fun hwx ↦ hxP (hwx ▸ hwP)
    simp only [Finset.mem_singleton]
    by_contra hwp
    have hSingletonNot : ({w} : Row α) ∉ blocker K := by
      intro hwBlocker
      have hLower := hBRows {w} hwBlocker
      simp at hLower
    obtain ⟨R, hR, hwR, -⟩ :=
      exists_row_avoiding_nonblocker_pair hBRows
        (x := w) (y := w) (by simpa using hSingletonNot)
    have hxR : x ∈ R := by
      by_contra hxR
      rcases hMiss R hR hxR with rfl | rfl
      · exact hwR hwP
      · exact hwR hwQ
    have hXW : ({x, w} : Row α) ∈ blocker K := by
      apply mem_blocker.mpr
      have hTransversal : IsTransversal K {x, w} := by
        intro S hSK
        by_cases hxS : x ∈ S
        · exact ⟨x, by simp, hxS⟩
        rcases hMiss S hSK hxS with rfl | rfl
        · exact ⟨w, by simp, hwP⟩
        · exact ⟨w, by simp, hwQ⟩
      apply hTransversal.minimal_of_privateRows
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · refine ⟨R, hR, by simp, hxR, ?_⟩
        intro z hzPair hzR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
        rcases hzPair with hzx | hzw
        · exact hzx
        · exact (hwR (hzw ▸ hzR)).elim
      · refine ⟨P, hP, by simp, hwP, ?_⟩
        intro z hzPair hzP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
        rcases hzPair with hzx | hzw
        · exact (hxP (hzx ▸ hzP)).elim
        · exact hzw
    have hXWPair : ({x, w} : Row α) ∈ pairRows (blocker K) := by
      exact Finset.mem_filter.mpr ⟨hXW, by simp [hwx.symm]⟩
    rw [hPairs] at hXWPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXWPair
    rcases hXWPair with hEq | hEq | hEq
    · have hErase := congrArg (fun S : Row α ↦ S.erase x) hEq
      have hSingletonEq : ({w} : Row α) = {p} := by
        simpa [hwx.symm, hxp] using hErase
      exact hwp (Finset.singleton_inj.mp hSingletonEq)
    · have hxRight : x ∈ ({p, q} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxp hxq
    · have hxRight : x ∈ ({u, v} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxu hxv
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    subst w
    exact Finset.mem_inter.mpr ⟨hpP, hpQ⟩

theorem p3k2_path_endpoint_degree_three_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x p q u v : α}
    (hVertices : ({x, p, q, u, v} : Row α).card = 5)
    (hKcard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{x, p}, {p, q}, {u, v}})
    (hDegree : degree K x = 3) :
    False := by
  obtain ⟨hxp, -, -, -, -, -, -, -, -, -⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hXP : ({x, p} : Row α) ∈ blocker K := by
    have hPair : ({x, p} : Row α) ∈ pairRows (blocker K) := by
      rw [hPairs]
      simp
    exact (pair_mem_of_mem_pairRows hPair).1
  have hAvoidCard : (avoidPoint K x).card = 2 := by
    have hPartition := card_avoidPoint_add_degree K x
    omega
  obtain ⟨P, Q, hPQ, hAvoid⟩ := Finset.card_eq_two.mp hAvoidCard
  have hPavoid : P ∈ avoidPoint K x := by rw [hAvoid]; simp
  have hQavoid : Q ∈ avoidPoint K x := by rw [hAvoid]; simp
  obtain ⟨hP, hxP⟩ := mem_avoidPoint.mp hPavoid
  obtain ⟨hQ, hxQ⟩ := mem_avoidPoint.mp hQavoid
  have hpP : p ∈ P := by
    obtain ⟨z, hzPair, hzP⟩ := (mem_blocker.mp hXP).prop P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with rfl | rfl
    · exact (hxP hzP).elim
    · exact hzP
  have hpQ : p ∈ Q := by
    obtain ⟨z, hzPair, hzQ⟩ := (mem_blocker.mp hXP).prop Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with rfl | rfl
    · exact (hxQ hzQ).elim
    · exact hzQ
  have hMiss : ∀ R ∈ K, x ∉ R → R = P ∨ R = Q := by
    intro R hRK hxR
    have hRAvoid : R ∈ avoidPoint K x := mem_avoidPoint.mpr ⟨hRK, hxR⟩
    rw [hAvoid] at hRAvoid
    simpa [or_comm] using hRAvoid
  have hInter : P ∩ Q = {p} :=
    p3k2_path_endpoint_intersection hVertices hBRows hPairs
      hP hQ hxP hxQ hpP hpQ hMiss
  exact p3k2_path_endpoint_fan_impossible hxp hKRows hBRows hBDegree hPairs
    hP hQ hxP hxQ hpP hpQ hMiss hInter

theorem p3k2_parallel_support {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v : α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKcard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hKDegree : MaxDegreeAtMost K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}}) :
    pointSupport K a = pointSupport K q := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hAP : ({a, p} : Row α) ∈ blocker K := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ blocker K := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have haNotThree : degree K a ≠ 3 := by
    intro haThree
    exact p3k2_path_endpoint_degree_three_impossible hVertices hKcard hKRows
      hBRows hBDegree hPairs haThree
  have hqNotThree : degree K q ≠ 3 := by
    intro hqThree
    have hPairsReverse :
        pairRows (blocker K) = {{q, p}, {p, a}, {u, v}} := by
      rw [hPairs]
      ext E
      simp [Finset.pair_comm, or_comm, or_left_comm]
    have hVerticesReverse : ({q, p, a, u, v} : Row α).card = 5 := by
      rw [show ({q, p, a, u, v} : Row α) = {a, p, q, u, v} by
        ext z
        simp [or_comm, or_left_comm]]
      exact hVertices
    exact p3k2_path_endpoint_degree_three_impossible hVerticesReverse hKcard hKRows
      hBRows hBDegree hPairsReverse hqThree
  obtain hAPType | hAPType | hAPType :=
    pair_blocker_support_type hKcard hKDegree hAP hap
  · obtain ⟨haCard, hpCard, haDisjoint⟩ := hAPType
    obtain hPQType | hPQType | hPQType :=
      pair_blocker_support_type hKcard hKDegree hPQ hpq
    · exact (hqNotThree (by simpa [pointSupport_card] using hPQType.2.1)).elim
    · obtain ⟨-, hqCard, hpqDisjoint⟩ := hPQType
      apply Finset.Subset.antisymm
      · intro R haR
        have hRK : R ∈ K := (mem_pointSupport.mp haR).1
        have hUnion : R ∈ pointSupport K p ∪ pointSupport K q := by
          rw [pair_blocker_support_union hPQ]
          exact hRK
        rcases Finset.mem_union.mp hUnion with hpR | hqR
        · exact (Finset.disjoint_left.mp haDisjoint haR hpR).elim
        · exact hqR
      · intro R hqR
        have hRK : R ∈ K := (mem_pointSupport.mp hqR).1
        have hUnion : R ∈ pointSupport K a ∪ pointSupport K p := by
          rw [pair_blocker_support_union hAP]
          exact hRK
        rcases Finset.mem_union.mp hUnion with haR | hpR
        · exact haR
        · exact (Finset.disjoint_left.mp hpqDisjoint hpR hqR).elim
    · exact (hqNotThree (by simpa [pointSupport_card] using hPQType.2.1)).elim
  · exact (haNotThree (by simpa [pointSupport_card] using hAPType.1)).elim
  · exact (haNotThree (by simpa [pointSupport_card] using hAPType.1)).elim

theorem p3k2_parallel_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v : α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKcard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hKDegree : MaxDegreeAtMost K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}}) :
    ∃ R0 R1 R2 R3 R4,
      ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 ∧
      K = {R0, R1, R2, R3, R4} ∧
      ((pointSupport K a = {R2, R4} ∧
          pointSupport K p = {R0, R1, R3} ∧
          pointSupport K q = {R2, R4} ∧
          pointSupport K u = {R0, R1, R2} ∧
          pointSupport K v = {R3, R4}) ∨
        (pointSupport K a = {R2, R4} ∧
          pointSupport K p = {R0, R1, R3} ∧
          pointSupport K q = {R2, R4} ∧
          pointSupport K u = {R3, R4} ∧
          pointSupport K v = {R0, R1, R2}) ∨
        (pointSupport K a = {R1, R3} ∧
          pointSupport K p = {R0, R2, R4} ∧
          pointSupport K q = {R1, R3} ∧
          pointSupport K u = {R0, R1, R4} ∧
          pointSupport K v = {R2, R3, R4})) := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hAP : ({a, p} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hUV : ({u, v} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have haNotThree : degree K a ≠ 3 := by
    intro haThree
    exact p3k2_path_endpoint_degree_three_impossible hVertices hKcard hKRows
      hBRows hBDegree hPairs haThree
  have hParallel := p3k2_parallel_support hVertices hKcard hKRows hKDegree
    hBRows hBDegree hPairs
  obtain hAPType | hAPType | hAPType :=
    pair_blocker_support_type hKcard hKDegree hAP hap
  · obtain ⟨haCard, hpCard, haPDisjoint⟩ := hAPType
    have haPUnion := pair_blocker_support_union hAP
    have hNotAU : ({a, u} : Row α) ∉ pairRows (blocker K) := by
      rw [hPairs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq | hEq)
      · have huRight : u ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hau.symm, hpu.symm] using huRight
      · have haRight : a ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hap, haq] using haRight
      · have haRight : a ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hau, hav] using haRight
    have hNotAV : ({a, v} : Row α) ∉ pairRows (blocker K) := by
      rw [hPairs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq | hEq)
      · have hvRight : v ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hav.symm, hpv.symm] using hvRight
      · have haRight : a ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hap, haq] using haRight
      · have haRight : a ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hau, hav] using haRight
    have hNotPU : ({p, u} : Row α) ∉ pairRows (blocker K) := by
      rw [hPairs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq | hEq)
      · have huRight : u ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hau.symm, hpu.symm] using huRight
      · have huRight : u ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hpu.symm, hqu.symm] using huRight
      · have hpRight : p ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hpu, hpv] using hpRight
    have hNotPV : ({p, v} : Row α) ∉ pairRows (blocker K) := by
      rw [hPairs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hEq | hEq | hEq)
      · have hvRight : v ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hav.symm, hpv.symm] using hvRight
      · have hvRight : v ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hpv.symm, hqv.symm] using hvRight
      · have hpRight : p ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hpu, hpv] using hpRight
    have hAU := support_union_ne_of_not_pairRow hBRows hNotAU
    have hAV := support_union_ne_of_not_pairRow hBRows hNotAV
    have hPU := support_union_ne_of_not_pairRow hBRows hNotPU
    have hPV := support_union_ne_of_not_pairRow hBRows hNotPV
    obtain hUVType | hUVType | hUVType :=
      pair_blocker_support_type hKcard hKDegree hUV huv
    · obtain ⟨huCard, hvCard, hUVDisjoint⟩ := hUVType
      obtain ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
          haSupport, hpSupport, hvSupport, huSupport⟩ :=
        two_three_partitions_normal_form haPUnion
          (by simpa [Finset.union_comm] using pair_blocker_support_union hUV)
          haPDisjoint (Disjoint.symm hUVDisjoint) haCard hpCard hvCard huCard
          hAV hAU hPV hPU
      exact ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
        Or.inr (Or.inl
          ⟨haSupport, hpSupport, hParallel ▸ haSupport, huSupport, hvSupport⟩)⟩
    · obtain ⟨huCard, hvCard, hUVDisjoint⟩ := hUVType
      obtain ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
          haSupport, hpSupport, huSupport, hvSupport⟩ :=
        two_three_partitions_normal_form haPUnion (pair_blocker_support_union hUV)
          haPDisjoint hUVDisjoint haCard hpCard huCard hvCard hAU hAV hPU hPV
      exact ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
        Or.inl ⟨haSupport, hpSupport, hParallel ▸ haSupport, huSupport, hvSupport⟩⟩
    · obtain ⟨huCard, hvCard, hUVInter⟩ := hUVType
      obtain ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
          haSupport, hpSupport, huSupport, hvSupport⟩ :=
        two_three_single_intersection_normal_form haPUnion
          (pair_blocker_support_union hUV) haPDisjoint haCard hpCard
          huCard hvCard hUVInter hAU hAV hPU hPV
      exact ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
        Or.inr (Or.inr
          ⟨haSupport, hpSupport, hParallel ▸ haSupport, huSupport, hvSupport⟩)⟩
  · exact (haNotThree (by simpa [pointSupport_card] using hAPType.1)).elim
  · exact (haNotThree (by simpa [pointSupport_card] using hAPType.1)).elim

theorem p3k2_parallel_i_combined_witness_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v x : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hxR0 : x ∈ R0) (hxR2 : x ∈ R2) (hxR4 : x ∉ R4) :
    False := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨hR0R1, hR0R2, hR0R3, hR0R4, hR1R2,
      hR1R3, hR1R4, hR2R3, hR2R4, hR3R4⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR1K : R1 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR3K : R3 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have haR0 : a ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K haSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have haR1 : a ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K haSupport).mpr (by simp)
  have haR2 : a ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K haSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have haR3 : a ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K haSupport).mpr (by simp)
  have haR4 : a ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K haSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hqR0 : q ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hqSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have hqR1 : q ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hqSupport).mpr (by simp)
  have hqR2 : q ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hqSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have hqR3 : q ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hqSupport).mpr (by simp)
  have hqR4 : q ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hqSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hpR0 : p ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hpSupport).mpr (by simp)
  have hpR1 : p ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hpSupport).not.mpr
      (by simp [hR0R1.symm, hR1R2, hR1R4])
  have hpR2 : p ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hpSupport).mpr (by simp)
  have hpR3 : p ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hpSupport).not.mpr
      (by simp [hR0R3.symm, hR2R3.symm, hR3R4])
  have hpR4 : p ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hpSupport).mpr (by simp)
  have huR0 : u ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K huSupport).mpr (by simp)
  have huR1 : u ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K huSupport).mpr (by simp)
  have huR2 : u ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K huSupport).not.mpr
      (by simp [hR0R2.symm, hR1R2.symm, hR2R4])
  have huR3 : u ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K huSupport).not.mpr
      (by simp [hR0R3.symm, hR1R3.symm, hR3R4])
  have huR4 : u ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K huSupport).mpr (by simp)
  have hvR0 : v ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hvSupport).not.mpr
      (by simp [hR0R2, hR0R3, hR0R4])
  have hvR1 : v ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hvSupport).not.mpr
      (by simp [hR1R2, hR1R3, hR1R4])
  have hvR2 : v ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hvSupport).mpr (by simp)
  have hvR3 : v ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hvSupport).mpr (by simp)
  have hvR4 : v ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hvSupport).mpr (by simp)
  have hxa : x ≠ a := fun hxa ↦ haR0 (hxa ▸ hxR0)
  have hxp : x ≠ p := fun hxp ↦ hxR4 (hxp ▸ hpR4)
  have hxq : x ≠ q := fun hxq ↦ hqR0 (hxq ▸ hxR0)
  have hxu : x ≠ u := fun hxu ↦ hxR4 (hxu ▸ huR4)
  have hxv : x ≠ v := fun hxv ↦ hxR4 (hxv ▸ hvR4)
  have hxR1 : x ∉ R1 := by
    intro hxR1
    have hTransversal : IsTransversal K ({x, v} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨x, by simp, hxR0⟩
      · exact ⟨x, by simp, hxR1⟩
      · exact ⟨v, by simp, hvR2⟩
      · exact ⟨v, by simp, hvR3⟩
      · exact ⟨v, by simp, hvR4⟩
    have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
    have hPairRow : ({x, v} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPair, by simp [hxv]⟩
    rw [hPairs] at hPairRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPairRow
    rcases hPairRow with hEq | hEq | hEq
    · have hxRight : x ∈ ({a, p} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxa hxp
    · have hxRight : x ∈ ({p, q} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxp hxq
    · have hxRight : x ∈ ({u, v} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxu hxv
  have hxR3 : x ∉ R3 := by
    intro hxR3
    have hTransversal : IsTransversal K ({x, u} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨u, by simp, huR0⟩
      · exact ⟨u, by simp, huR1⟩
      · exact ⟨x, by simp, hxR2⟩
      · exact ⟨x, by simp, hxR3⟩
      · exact ⟨u, by simp, huR4⟩
    have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
    have hPairRow : ({x, u} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPair, by simp [hxu]⟩
    rw [hPairs] at hPairRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPairRow
    rcases hPairRow with hEq | hEq | hEq
    · have hxRight : x ∈ ({a, p} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxa hxp
    · have hxRight : x ∈ ({p, q} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxp hxq
    · have hxRight : x ∈ ({u, v} : Row α) := by rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxRight
      exact hxRight.elim hxu hxv
  have hAUXTrans : IsTransversal K ({a, u, x} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, huR0⟩
    · exact ⟨a, by simp, haR1⟩
    · exact ⟨x, by simp, hxR2⟩
    · exact ⟨a, by simp, haR3⟩
    · exact ⟨u, by simp, huR4⟩
  have hAUX : ({a, u, x} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hAUXTrans
      hR3K haR3 huR3 hxR3
      hR4K huR4 haR4 hxR4
      hR2K hxR2 haR2 huR2
  have hAVXTrans : IsTransversal K ({a, v, x} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨x, by simp, hxR0⟩
    · exact ⟨a, by simp, haR1⟩
    · exact ⟨v, by simp, hvR2⟩
    · exact ⟨a, by simp, haR3⟩
    · exact ⟨v, by simp, hvR4⟩
  have hAVX : ({a, v, x} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hAVXTrans
      hR1K haR1 hvR1 hxR1
      hR4K hvR4 haR4 hxR4
      hR0K hxR0 haR0 hvR0
  have hAUXNeAVX : ({a, u, x} : Row α) ≠ {a, v, x} := by
    intro hEq
    have huRight : u ∈ ({a, v, x} : Row α) := by rw [← hEq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at huRight
    rcases huRight with hua | huv' | hux
    · exact hau hua.symm
    · exact huv huv'
    · exact hxu hux.symm
  have hqAUX : q ∉ ({a, u, x} : Row α) := by simp [haq.symm, hqu, hxq.symm]
  have hqAVX : q ∉ ({a, v, x} : Row α) := by simp [haq.symm, hqv, hxq.symm]
  have hFour := twin_endpoint_amplifier haq hxa.symm
    (haSupport.trans hqSupport.symm) hAUX hAVX hAUXNeAVX
    (by simp) (by simp) hqAUX hqAVX (by simp) (by simp)
  have hUpper := hBDegree x
  omega

theorem p3k2_parallel_i_separate_witnesses_are_pure {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v z w : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hzR0 : z ∈ R0) (hzR2 : z ∉ R2) (hzR4 : z ∉ R4)
    (hwR0 : w ∉ R0) (hwR2 : w ∈ R2) (hwR4 : w ∉ R4) :
    z ∉ R1 ∧ z ∉ R3 ∧ w ∉ R1 ∧ w ∉ R3 := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨hR0R1, hR0R2, hR0R3, hR0R4, hR1R2,
      hR1R3, hR1R4, hR2R3, hR2R4, hR3R4⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR1K : R1 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR3K : R3 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have haR0 : a ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K haSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have haR1 : a ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K haSupport).mpr (by simp)
  have haR2 : a ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K haSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have haR3 : a ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K haSupport).mpr (by simp)
  have haR4 : a ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K haSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hqR0 : q ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hqSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have hqR1 : q ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hqSupport).mpr (by simp)
  have hqR2 : q ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hqSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have hqR3 : q ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hqSupport).mpr (by simp)
  have hqR4 : q ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hqSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hpR0 : p ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hpSupport).mpr (by simp)
  have hpR1 : p ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hpSupport).not.mpr
      (by simp [hR0R1.symm, hR1R2, hR1R4])
  have hpR2 : p ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hpSupport).mpr (by simp)
  have hpR3 : p ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hpSupport).not.mpr
      (by simp [hR0R3.symm, hR2R3.symm, hR3R4])
  have hpR4 : p ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hpSupport).mpr (by simp)
  have huR0 : u ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K huSupport).mpr (by simp)
  have huR1 : u ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K huSupport).mpr (by simp)
  have huR2 : u ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K huSupport).not.mpr
      (by simp [hR0R2.symm, hR1R2.symm, hR2R4])
  have huR3 : u ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K huSupport).not.mpr
      (by simp [hR0R3.symm, hR1R3.symm, hR3R4])
  have huR4 : u ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K huSupport).mpr (by simp)
  have hvR0 : v ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hvSupport).not.mpr
      (by simp [hR0R2, hR0R3, hR0R4])
  have hvR1 : v ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hvSupport).not.mpr
      (by simp [hR1R2, hR1R3, hR1R4])
  have hvR2 : v ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hvSupport).mpr (by simp)
  have hvR3 : v ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hvSupport).mpr (by simp)
  have hvR4 : v ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hvSupport).mpr (by simp)
  have hza : z ≠ a := fun hza ↦ haR0 (hza ▸ hzR0)
  have hzp : z ≠ p := fun hzp ↦ hzR4 (hzp ▸ hpR4)
  have hzq : z ≠ q := fun hzq ↦ hqR0 (hzq ▸ hzR0)
  have hzu : z ≠ u := fun hzu ↦ hzR4 (hzu ▸ huR4)
  have hzv : z ≠ v := fun hzv ↦ hvR0 (hzv ▸ hzR0)
  have hwa : w ≠ a := fun hwa ↦ haR2 (hwa ▸ hwR2)
  have hwp : w ≠ p := fun hwp ↦ hwR4 (hwp ▸ hpR4)
  have hwq : w ≠ q := fun hwq ↦ hqR2 (hwq ▸ hwR2)
  have hwu : w ≠ u := fun hwu ↦ huR2 (hwu ▸ hwR2)
  have hwv : w ≠ v := fun hwv ↦ hwR4 (hwv ▸ hvR4)
  have hzw : z ≠ w := fun hzw ↦ hzR2 (hzw ▸ hwR2)
  have hzR1 : z ∉ R1 := by
    intro hzR1
    have hTransversal : IsTransversal K ({z, v} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨z, by simp, hzR0⟩
      · exact ⟨z, by simp, hzR1⟩
      · exact ⟨v, by simp, hvR2⟩
      · exact ⟨v, by simp, hvR3⟩
      · exact ⟨v, by simp, hvR4⟩
    have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
    have hPairRow : ({z, v} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPair, by simp [hzv]⟩
    rw [hPairs] at hPairRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPairRow
    rcases hPairRow with hEq | hEq | hEq
    · have hzRight : z ∈ ({a, p} : Row α) := by rw [← hEq]; simp
      simpa [hza, hzp] using hzRight
    · have hzRight : z ∈ ({p, q} : Row α) := by rw [← hEq]; simp
      simpa [hzp, hzq] using hzRight
    · have hzRight : z ∈ ({u, v} : Row α) := by rw [← hEq]; simp
      simpa [hzu, hzv] using hzRight
  have hwR3 : w ∉ R3 := by
    intro hwR3
    have hTransversal : IsTransversal K ({w, u} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨u, by simp, huR0⟩
      · exact ⟨u, by simp, huR1⟩
      · exact ⟨w, by simp, hwR2⟩
      · exact ⟨w, by simp, hwR3⟩
      · exact ⟨u, by simp, huR4⟩
    have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
    have hPairRow : ({w, u} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPair, by simp [hwu]⟩
    rw [hPairs] at hPairRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPairRow
    rcases hPairRow with hEq | hEq | hEq
    · have hwRight : w ∈ ({a, p} : Row α) := by rw [← hEq]; simp
      simpa [hwa, hwp] using hwRight
    · have hwRight : w ∈ ({p, q} : Row α) := by rw [← hEq]; simp
      simpa [hwp, hwq] using hwRight
    · have hwRight : w ∈ ({u, v} : Row α) := by rw [← hEq]; simp
      simpa [hwu, hwv] using hwRight
  have hAP : ({a, p} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hUV : ({u, v} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  by_cases hzR3 : z ∈ R3
  · by_cases hwR1 : w ∈ R1
    · have hPVWTrans : IsTransversal K ({p, v, w} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpR0⟩
        · exact ⟨w, by simp, hwR1⟩
        · exact ⟨p, by simp, hpR2⟩
        · exact ⟨v, by simp, hvR3⟩
        · exact ⟨p, by simp, hpR4⟩
      have hPVW : ({p, v, w} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hPVWTrans
          hR0K hpR0 hvR0 hwR0
          hR3K hvR3 hpR3 hwR3
          hR1K hwR1 hpR1 hvR1
      have hPUZTrans : IsTransversal K ({p, u, z} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpR0⟩
        · exact ⟨u, by simp, huR1⟩
        · exact ⟨p, by simp, hpR2⟩
        · exact ⟨z, by simp, hzR3⟩
        · exact ⟨p, by simp, hpR4⟩
      have hPUZ : ({p, u, z} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hPUZTrans
          hR2K hpR2 huR2 hzR2
          hR1K huR1 hpR1 hzR1
          hR3K hzR3 hpR3 huR3
      have hFour := degree_ge_four_of_four_rows (x := p) hAP hPQ hPVW hPUZ
        (by
          intro hEq
          have haRight : a ∈ ({p, q} : Row α) := by rw [← hEq]; simp
          simpa [hap, haq] using haRight)
        (by
          intro hEq
          have haRight : a ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
          simpa [hap, hav, hwa.symm] using haRight)
        (by
          intro hEq
          have haRight : a ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hap, hau, hza.symm] using haRight)
        (by
          intro hEq
          have hqRight : q ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
          simpa [hpq.symm, hqv, hwq.symm] using hqRight)
        (by
          intro hEq
          have hqRight : q ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hpq.symm, hqu, hzq.symm] using hqRight)
        (by
          intro hEq
          have hvRight : v ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hpv.symm, huv.symm, hzv.symm] using hvRight)
        (by simp) (by simp) (by simp) (by simp)
      have hUpper := hBDegree p
      omega
    · have hAUWTrans : IsTransversal K ({a, u, w} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨u, by simp, huR0⟩
        · exact ⟨a, by simp, haR1⟩
        · exact ⟨w, by simp, hwR2⟩
        · exact ⟨a, by simp, haR3⟩
        · exact ⟨u, by simp, huR4⟩
      have hAUW : ({a, u, w} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hAUWTrans
          hR3K haR3 huR3 hwR3
          hR0K huR0 haR0 hwR0
          hR2K hwR2 haR2 huR2
      have hQUWTrans : IsTransversal K ({q, u, w} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨u, by simp, huR0⟩
        · exact ⟨q, by simp, hqR1⟩
        · exact ⟨w, by simp, hwR2⟩
        · exact ⟨q, by simp, hqR3⟩
        · exact ⟨u, by simp, huR4⟩
      have hQUW : ({q, u, w} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hQUWTrans
          hR3K hqR3 huR3 hwR3
          hR0K huR0 hqR0 hwR0
          hR2K hwR2 hqR2 huR2
      have hPUZTrans : IsTransversal K ({p, u, z} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpR0⟩
        · exact ⟨u, by simp, huR1⟩
        · exact ⟨p, by simp, hpR2⟩
        · exact ⟨z, by simp, hzR3⟩
        · exact ⟨p, by simp, hpR4⟩
      have hPUZ : ({p, u, z} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hPUZTrans
          hR2K hpR2 huR2 hzR2
          hR1K huR1 hpR1 hzR1
          hR3K hzR3 hpR3 huR3
      have hFour := degree_ge_four_of_four_rows (x := u) hUV hAUW hQUW hPUZ
        (by
          intro hEq
          have hvRight : v ∈ ({a, u, w} : Row α) := by rw [← hEq]; simp
          simpa [hav.symm, huv.symm, hwv.symm] using hvRight)
        (by
          intro hEq
          have hvRight : v ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
          simpa [hqv.symm, huv.symm, hwv.symm] using hvRight)
        (by
          intro hEq
          have hvRight : v ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hpv.symm, huv.symm, hzv.symm] using hvRight)
        (by
          intro hEq
          have haRight : a ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
          simpa [haq, hau, hwa.symm] using haRight)
        (by
          intro hEq
          have haRight : a ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hap, hau, hza.symm] using haRight)
        (by
          intro hEq
          have hqRight : q ∈ ({p, u, z} : Row α) := by rw [← hEq]; simp
          simpa [hpq.symm, hqu, hzq.symm] using hqRight)
        (by simp) (by simp) (by simp) (by simp)
      have hUpper := hBDegree u
      omega
  · by_cases hwR1 : w ∈ R1
    · have hAVZTrans : IsTransversal K ({a, v, z} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨z, by simp, hzR0⟩
        · exact ⟨a, by simp, haR1⟩
        · exact ⟨v, by simp, hvR2⟩
        · exact ⟨a, by simp, haR3⟩
        · exact ⟨v, by simp, hvR4⟩
      have hAVZ : ({a, v, z} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hAVZTrans
          hR1K haR1 hvR1 hzR1
          hR2K hvR2 haR2 hzR2
          hR0K hzR0 haR0 hvR0
      have hQVZTrans : IsTransversal K ({q, v, z} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨z, by simp, hzR0⟩
        · exact ⟨q, by simp, hqR1⟩
        · exact ⟨v, by simp, hvR2⟩
        · exact ⟨q, by simp, hqR3⟩
        · exact ⟨v, by simp, hvR4⟩
      have hQVZ : ({q, v, z} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hQVZTrans
          hR1K hqR1 hvR1 hzR1
          hR2K hvR2 hqR2 hzR2
          hR0K hzR0 hqR0 hvR0
      have hPVWTrans : IsTransversal K ({p, v, w} : Row α) := by
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpR0⟩
        · exact ⟨w, by simp, hwR1⟩
        · exact ⟨p, by simp, hpR2⟩
        · exact ⟨v, by simp, hvR3⟩
        · exact ⟨p, by simp, hpR4⟩
      have hPVW : ({p, v, w} : Row α) ∈ blocker K :=
        triple_mem_blocker_of_private_rows hPVWTrans
          hR0K hpR0 hvR0 hwR0
          hR3K hvR3 hpR3 hwR3
          hR1K hwR1 hpR1 hvR1
      have hFour := degree_ge_four_of_four_rows (x := v) hUV hAVZ hQVZ hPVW
        (by
          intro hEq
          have huRight : u ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
          simpa [hau.symm, huv, hzu.symm] using huRight)
        (by
          intro hEq
          have huRight : u ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
          simpa [hqu.symm, huv, hzu.symm] using huRight)
        (by
          intro hEq
          have huRight : u ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
          simpa [hpu.symm, huv, hwu.symm] using huRight)
        (by
          intro hEq
          have haRight : a ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
          simpa [haq, hav, hza.symm] using haRight)
        (by
          intro hEq
          have haRight : a ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
          simpa [hap, hav, hwa.symm] using haRight)
        (by
          intro hEq
          have hqRight : q ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
          simpa [hpq.symm, hqv, hwq.symm] using hqRight)
        (by simp) (by simp) (by simp) (by simp)
      have hUpper := hBDegree v
      omega
    · exact ⟨hzR1, hzR3, hwR1, hwR3⟩

theorem p3k2_parallel_i_exists_pure_witnesses {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKClutter : IsClutter K)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4}) :
    ∃ z w,
      z ∈ R0 ∧ z ∉ R1 ∧ z ∉ R2 ∧ z ∉ R3 ∧ z ∉ R4 ∧
      w ∉ R0 ∧ w ∉ R1 ∧ w ∈ R2 ∧ w ∉ R3 ∧ w ∉ R4 := by
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨-, -, -, hR0R4, -, -, -, -, hR2R4, -⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have hR0NotSubset : ¬ R0 ⊆ R4 := by
    intro hSubset
    exact hR0R4 (hKClutter hR0K hR4K hSubset)
  have hR2NotSubset : ¬ R2 ⊆ R4 := by
    intro hSubset
    exact hR2R4 (hKClutter hR2K hR4K hSubset)
  obtain ⟨z, hzR0, hzR4⟩ := Finset.not_subset.mp hR0NotSubset
  obtain ⟨w, hwR2, hwR4⟩ := Finset.not_subset.mp hR2NotSubset
  have hzR2 : z ∉ R2 := by
    intro hzR2
    exact p3k2_parallel_i_combined_witness_impossible hVertices hK hKcard
      hBRows hBDegree hPairs haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR2 hzR4
  have hwR0 : w ∉ R0 := by
    intro hwR0
    exact p3k2_parallel_i_combined_witness_impossible hVertices hK hKcard
      hBRows hBDegree hPairs haSupport hpSupport hqSupport huSupport hvSupport
      hwR0 hwR2 hwR4
  obtain ⟨hzR1, hzR3, hwR1, hwR3⟩ :=
    p3k2_parallel_i_separate_witnesses_are_pure hVertices hK hKcard
      hBRows hBDegree hPairs haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR2 hzR4 hwR0 hwR2 hwR4
  exact ⟨z, w, hzR0, hzR1, hzR2, hzR3, hzR4,
    hwR0, hwR1, hwR2, hwR3, hwR4⟩

theorem pointSupport_eq_of_three_rows {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {A B C : Row α}
    (hDegree : degree H x = 3)
    (hA : A ∈ H) (hB : B ∈ H) (hC : C ∈ H)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxC : x ∈ C) :
    pointSupport H x = {A, B, C} := by
  have hSubset : ({A, B, C} : Hypergraph α) ⊆ pointSupport H x := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact mem_pointSupport.mpr ⟨hA, hxA⟩
    · exact mem_pointSupport.mpr ⟨hB, hxB⟩
    · exact mem_pointSupport.mpr ⟨hC, hxC⟩
  have hFamilyCard : ({A, B, C} : Hypergraph α).card = 3 := by
    simp [hAB, hAC, hBC]
  have hSupportCard : (pointSupport H x).card = 3 := by
    simpa [pointSupport_card] using hDegree
  exact (Finset.eq_of_subset_of_card_le hSubset (by rw [hFamilyCard, hSupportCard])).symm

theorem p3k2_parallel_i_seven_blockers {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v z w : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hzR0 : z ∈ R0) (hzR1 : z ∉ R1) (hzR2 : z ∉ R2)
    (hzR3 : z ∉ R3) (hzR4 : z ∉ R4)
    (hwR0 : w ∉ R0) (hwR1 : w ∉ R1) (hwR2 : w ∈ R2)
    (hwR3 : w ∉ R3) (hwR4 : w ∉ R4) :
    ({a, p} : Row α) ∈ blocker K ∧
      ({p, q} : Row α) ∈ blocker K ∧
      ({u, v} : Row α) ∈ blocker K ∧
      ({a, u, w} : Row α) ∈ blocker K ∧
      ({q, u, w} : Row α) ∈ blocker K ∧
      ({a, v, z} : Row α) ∈ blocker K ∧
      ({q, v, z} : Row α) ∈ blocker K ∧
      degree (blocker K) a = 3 ∧ degree (blocker K) q = 3 ∧
      degree (blocker K) u = 3 ∧ degree (blocker K) v = 3 ∧
      pointSupport (blocker K) a = {{a, p}, {a, u, w}, {a, v, z}} ∧
      pointSupport (blocker K) q = {{p, q}, {q, u, w}, {q, v, z}} ∧
      pointSupport (blocker K) u = {{u, v}, {a, u, w}, {q, u, w}} ∧
      pointSupport (blocker K) v = {{u, v}, {a, v, z}, {q, v, z}} := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨hR0R1, hR0R2, hR0R3, hR0R4, hR1R2,
      hR1R3, hR1R4, hR2R3, hR2R4, hR3R4⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR1K : R1 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR3K : R3 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have haR0 : a ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K haSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have haR1 : a ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K haSupport).mpr (by simp)
  have haR2 : a ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K haSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have haR3 : a ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K haSupport).mpr (by simp)
  have haR4 : a ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K haSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hqR0 : q ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hqSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have hqR1 : q ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hqSupport).mpr (by simp)
  have hqR2 : q ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hqSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have hqR3 : q ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hqSupport).mpr (by simp)
  have hqR4 : q ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hqSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hpR0 : p ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hpSupport).mpr (by simp)
  have hpR1 : p ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hpSupport).not.mpr
      (by simp [hR0R1.symm, hR1R2, hR1R4])
  have hpR2 : p ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hpSupport).mpr (by simp)
  have hpR3 : p ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hpSupport).not.mpr
      (by simp [hR0R3.symm, hR2R3.symm, hR3R4])
  have hpR4 : p ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hpSupport).mpr (by simp)
  have huR0 : u ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K huSupport).mpr (by simp)
  have huR1 : u ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K huSupport).mpr (by simp)
  have huR2 : u ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K huSupport).not.mpr
      (by simp [hR0R2.symm, hR1R2.symm, hR2R4])
  have huR3 : u ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K huSupport).not.mpr
      (by simp [hR0R3.symm, hR1R3.symm, hR3R4])
  have huR4 : u ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K huSupport).mpr (by simp)
  have hvR0 : v ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hvSupport).not.mpr
      (by simp [hR0R2, hR0R3, hR0R4])
  have hvR1 : v ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hvSupport).not.mpr
      (by simp [hR1R2, hR1R3, hR1R4])
  have hvR2 : v ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hvSupport).mpr (by simp)
  have hvR3 : v ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hvSupport).mpr (by simp)
  have hvR4 : v ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hvSupport).mpr (by simp)
  have hza : z ≠ a := fun hza ↦ haR0 (hza ▸ hzR0)
  have hzp : z ≠ p := fun hzp ↦ hzR4 (hzp ▸ hpR4)
  have hzq : z ≠ q := fun hzq ↦ hqR0 (hzq ▸ hzR0)
  have hzu : z ≠ u := fun hzu ↦ hzR4 (hzu ▸ huR4)
  have hzv : z ≠ v := fun hzv ↦ hvR0 (hzv ▸ hzR0)
  have hwa : w ≠ a := fun hwa ↦ haR2 (hwa ▸ hwR2)
  have hwp : w ≠ p := fun hwp ↦ hwR4 (hwp ▸ hpR4)
  have hwq : w ≠ q := fun hwq ↦ hqR2 (hwq ▸ hwR2)
  have hwu : w ≠ u := fun hwu ↦ huR2 (hwu ▸ hwR2)
  have hwv : w ≠ v := fun hwv ↦ hwR4 (hwv ▸ hvR4)
  have hzw : z ≠ w := fun hzw ↦ hwR0 (hzw ▸ hzR0)
  have hAP : ({a, p} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hUV : ({u, v} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hAUWTrans : IsTransversal K ({a, u, w} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, huR0⟩
    · exact ⟨a, by simp, haR1⟩
    · exact ⟨w, by simp, hwR2⟩
    · exact ⟨a, by simp, haR3⟩
    · exact ⟨u, by simp, huR4⟩
  have hAUW : ({a, u, w} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hAUWTrans
      hR3K haR3 huR3 hwR3 hR0K huR0 haR0 hwR0 hR2K hwR2 haR2 huR2
  have hQUWTrans : IsTransversal K ({q, u, w} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, huR0⟩
    · exact ⟨q, by simp, hqR1⟩
    · exact ⟨w, by simp, hwR2⟩
    · exact ⟨q, by simp, hqR3⟩
    · exact ⟨u, by simp, huR4⟩
  have hQUW : ({q, u, w} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hQUWTrans
      hR3K hqR3 huR3 hwR3 hR0K huR0 hqR0 hwR0 hR2K hwR2 hqR2 huR2
  have hAVZTrans : IsTransversal K ({a, v, z} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨z, by simp, hzR0⟩
    · exact ⟨a, by simp, haR1⟩
    · exact ⟨v, by simp, hvR2⟩
    · exact ⟨a, by simp, haR3⟩
    · exact ⟨v, by simp, hvR4⟩
  have hAVZ : ({a, v, z} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hAVZTrans
      hR1K haR1 hvR1 hzR1 hR2K hvR2 haR2 hzR2 hR0K hzR0 haR0 hvR0
  have hQVZTrans : IsTransversal K ({q, v, z} : Row α) := by
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨z, by simp, hzR0⟩
    · exact ⟨q, by simp, hqR1⟩
    · exact ⟨v, by simp, hvR2⟩
    · exact ⟨q, by simp, hqR3⟩
    · exact ⟨v, by simp, hvR4⟩
  have hQVZ : ({q, v, z} : Row α) ∈ blocker K :=
    triple_mem_blocker_of_private_rows hQVZTrans
      hR1K hqR1 hvR1 hzR1 hR2K hvR2 hqR2 hzR2 hR0K hzR0 hqR0 hvR0
  have haLower := degree_ge_three_of_three_rows (x := a) hAP hAUW hAVZ
    (by
      intro hEq
      have hpRight : p ∈ ({a, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hap.symm, hpu, hwp.symm] using hpRight)
    (by
      intro hEq
      have hpRight : p ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hap.symm, hpv, hzp.symm] using hpRight)
    (by
      intro hEq
      have huRight : u ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hau.symm, huv, hzu.symm] using huRight)
    (by simp) (by simp) (by simp)
  have hqLower := degree_ge_three_of_three_rows (x := q) hPQ hQUW hQVZ
    (by
      intro hEq
      have hpRight : p ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hpq, hpu, hwp.symm] using hpRight)
    (by
      intro hEq
      have hpRight : p ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hpq, hpv, hzp.symm] using hpRight)
    (by
      intro hEq
      have huRight : u ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hqu.symm, huv, hzu.symm] using huRight)
    (by simp) (by simp) (by simp)
  have huLower := degree_ge_three_of_three_rows (x := u) hUV hAUW hQUW
    (by
      intro hEq
      have hvRight : v ∈ ({a, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hav.symm, huv.symm, hwv.symm] using hvRight)
    (by
      intro hEq
      have hvRight : v ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hqv.symm, huv.symm, hwv.symm] using hvRight)
    (by
      intro hEq
      have haRight : a ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [haq, hau, hwa.symm] using haRight)
    (by simp) (by simp) (by simp)
  have hvLower := degree_ge_three_of_three_rows (x := v) hUV hAVZ hQVZ
    (by
      intro hEq
      have huRight : u ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hau.symm, huv, hzu.symm] using huRight)
    (by
      intro hEq
      have huRight : u ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hqu.symm, huv, hzu.symm] using huRight)
    (by
      intro hEq
      have haRight : a ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [haq, hav, hza.symm] using haRight)
    (by simp) (by simp) (by simp)
  have haDegree : degree (blocker K) a = 3 := by have := hBDegree a; omega
  have hqDegree : degree (blocker K) q = 3 := by have := hBDegree q; omega
  have huDegree : degree (blocker K) u = 3 := by have := hBDegree u; omega
  have hvDegree : degree (blocker K) v = 3 := by have := hBDegree v; omega
  have haSupportBlocker := pointSupport_eq_of_three_rows haDegree hAP hAUW hAVZ
    (by
      intro hEq
      have hpRight : p ∈ ({a, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hap.symm, hpu, hwp.symm] using hpRight)
    (by
      intro hEq
      have hpRight : p ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hap.symm, hpv, hzp.symm] using hpRight)
    (by
      intro hEq
      have huRight : u ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hau.symm, huv, hzu.symm] using huRight)
    (by simp) (by simp) (by simp)
  have hqSupportBlocker := pointSupport_eq_of_three_rows hqDegree hPQ hQUW hQVZ
    (by
      intro hEq
      have hpRight : p ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hpq, hpu, hwp.symm] using hpRight)
    (by
      intro hEq
      have hpRight : p ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hpq, hpv, hzp.symm] using hpRight)
    (by
      intro hEq
      have huRight : u ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hqu.symm, huv, hzu.symm] using huRight)
    (by simp) (by simp) (by simp)
  have huSupportBlocker := pointSupport_eq_of_three_rows huDegree hUV hAUW hQUW
    (by
      intro hEq
      have hvRight : v ∈ ({a, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hav.symm, huv.symm, hwv.symm] using hvRight)
    (by
      intro hEq
      have hvRight : v ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [hqv.symm, huv.symm, hwv.symm] using hvRight)
    (by
      intro hEq
      have haRight : a ∈ ({q, u, w} : Row α) := by rw [← hEq]; simp
      simpa [haq, hau, hwa.symm] using haRight)
    (by simp) (by simp) (by simp)
  have hvSupportBlocker := pointSupport_eq_of_three_rows hvDegree hUV hAVZ hQVZ
    (by
      intro hEq
      have huRight : u ∈ ({a, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hau.symm, huv, hzu.symm] using huRight)
    (by
      intro hEq
      have huRight : u ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [hqu.symm, huv, hzu.symm] using huRight)
    (by
      intro hEq
      have haRight : a ∈ ({q, v, z} : Row α) := by rw [← hEq]; simp
      simpa [haq, hav, hza.symm] using haRight)
    (by simp) (by simp) (by simp)
  exact ⟨hAP, hPQ, hUV, hAUW, hQUW, hAVZ, hQVZ,
    haDegree, hqDegree, huDegree, hvDegree,
    haSupportBlocker, hqSupportBlocker, huSupportBlocker, hvSupportBlocker⟩

theorem restrictRows_insert_isClutter_of_uniform_injective {α : Type*}
    [DecidableEq α]
    {K : Hypergraph α} {V : Row α} {t : α} {n : ℕ}
    (htV : t ∉ V)
    (hCard : ∀ R ∈ K, (R ∩ V).card = n)
    (hInj : ∀ R ∈ K, ∀ S ∈ K, R ∩ V = S ∩ V → R = S) :
    IsClutter (restrictRows K (insert t V)) := by
  intro P hP Q hQ hPQ
  obtain ⟨R, hRK, hRP⟩ := mem_restrictRows.mp hP
  obtain ⟨S, hSK, hSQ⟩ := mem_restrictRows.mp hQ
  have hEraseR : (R ∩ insert t V).erase t = R ∩ V := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hxt, hxR, hxt' | hxV⟩
      · exact (hxt hxt').elim
      · exact ⟨hxR, hxV⟩
    · rintro ⟨hxR, hxV⟩
      exact ⟨fun hxt ↦ htV (hxt ▸ hxV), hxR, Or.inr hxV⟩
  have hEraseS : (S ∩ insert t V).erase t = S ∩ V := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hxt, hxS, hxt' | hxV⟩
      · exact (hxt hxt').elim
      · exact ⟨hxS, hxV⟩
    · rintro ⟨hxS, hxV⟩
      exact ⟨fun hxt ↦ htV (hxt ▸ hxV), hxS, Or.inr hxV⟩
  have hBaseSubset : R ∩ V ⊆ S ∩ V := by
    rw [← hEraseR, ← hEraseS, hRP, hSQ]
    exact Finset.erase_subset_erase t hPQ
  have hBaseEq : R ∩ V = S ∩ V :=
    Finset.eq_of_subset_of_card_le hBaseSubset (by rw [hCard R hRK, hCard S hSK])
  have hRS : R = S := hInj R hRK S hSK hBaseEq
  rw [← hRP, ← hSQ, hRS]

theorem p3k2_parallel_i_base_projections {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v z w : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hzR0 : z ∈ R0) (hzR1 : z ∉ R1) (hzR2 : z ∉ R2)
    (hzR3 : z ∉ R3) (hzR4 : z ∉ R4)
    (hwR0 : w ∉ R0) (hwR1 : w ∉ R1) (hwR2 : w ∈ R2)
    (hwR3 : w ∉ R3) (hwR4 : w ∉ R4) :
    let V0 : Row α := {a, p, q, u, v, z, w}
    R0 ∩ V0 = {p, u, z} ∧
      R1 ∩ V0 = {a, q, u} ∧
      R2 ∩ V0 = {p, v, w} ∧
      R3 ∩ V0 = {a, q, v} ∧
      R4 ∩ V0 = {p, u, v} := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨hR0R1, hR0R2, hR0R3, hR0R4, hR1R2,
      hR1R3, hR1R4, hR2R3, hR2R4, hR3R4⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR1K : R1 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR3K : R3 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have haR0 : a ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K haSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have haR1 : a ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K haSupport).mpr (by simp)
  have haR2 : a ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K haSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have haR3 : a ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K haSupport).mpr (by simp)
  have haR4 : a ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K haSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hqR0 : q ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hqSupport).not.mpr
      (by simp [hR0R1, hR0R3])
  have hqR1 : q ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hqSupport).mpr (by simp)
  have hqR2 : q ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hqSupport).not.mpr
      (by simp [hR1R2.symm, hR2R3])
  have hqR3 : q ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hqSupport).mpr (by simp)
  have hqR4 : q ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hqSupport).not.mpr
      (by simp [hR1R4.symm, hR3R4.symm])
  have hpR0 : p ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hpSupport).mpr (by simp)
  have hpR1 : p ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hpSupport).not.mpr
      (by simp [hR0R1.symm, hR1R2, hR1R4])
  have hpR2 : p ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hpSupport).mpr (by simp)
  have hpR3 : p ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hpSupport).not.mpr
      (by simp [hR0R3.symm, hR2R3.symm, hR3R4])
  have hpR4 : p ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hpSupport).mpr (by simp)
  have huR0 : u ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K huSupport).mpr (by simp)
  have huR1 : u ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K huSupport).mpr (by simp)
  have huR2 : u ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K huSupport).not.mpr
      (by simp [hR0R2.symm, hR1R2.symm, hR2R4])
  have huR3 : u ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K huSupport).not.mpr
      (by simp [hR0R3.symm, hR1R3.symm, hR3R4])
  have huR4 : u ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K huSupport).mpr (by simp)
  have hvR0 : v ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hvSupport).not.mpr
      (by simp [hR0R2, hR0R3, hR0R4])
  have hvR1 : v ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hvSupport).not.mpr
      (by simp [hR1R2, hR1R3, hR1R4])
  have hvR2 : v ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hvSupport).mpr (by simp)
  have hvR3 : v ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hvSupport).mpr (by simp)
  have hvR4 : v ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hvSupport).mpr (by simp)
  dsimp
  constructor
  · ext x
    simp [haR0, hpR0, hqR0, huR0, hvR0, hzR0, hwR0]
  constructor
  · ext x
    simp [haR1, hpR1, hqR1, huR1, hvR1, hzR1, hwR1]
  constructor
  · ext x
    simp [haR2, hpR2, hqR2, huR2, hvR2, hzR2, hwR2]
  constructor
  · ext x
    simp [haR3, hpR3, hqR3, huR3, hvR3, hzR3, hwR3]
  · ext x
    simp [haR4, hpR4, hqR4, huR4, hvR4, hzR4, hwR4]

theorem p3k2_parallel_i_single_point_restriction_isClutter {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v z w t : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hzR0 : z ∈ R0) (hzR1 : z ∉ R1) (hzR2 : z ∉ R2)
    (hzR3 : z ∉ R3) (hzR4 : z ∉ R4)
    (hwR0 : w ∉ R0) (hwR1 : w ∉ R1) (hwR2 : w ∈ R2)
    (hwR3 : w ∉ R3) (hwR4 : w ∉ R4)
    (hta : t ≠ a) (htp : t ≠ p) (htq : t ≠ q)
    (htu : t ≠ u) (htv : t ≠ v) (htz : t ≠ z) (htw : t ≠ w) :
    IsClutter (restrictRows K {t, a, p, q, u, v, z, w}) := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hza : z ≠ a := by
    intro hza
    have haR0 : a ∉ R0 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨hR0R1, -, hR0R3, -, -, -, -, -, -, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) haSupport).not.mpr
        (by simp [hR0R1, hR0R3])
    exact haR0 (hza ▸ hzR0)
  have hzp : z ≠ p := by
    intro hzp
    have hpR4 : p ∈ R4 :=
      (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hpSupport).mpr (by simp)
    exact hzR4 (hzp ▸ hpR4)
  have hzq : z ≠ q := by
    intro hzq
    have hqR0 : q ∉ R0 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨hR0R1, -, hR0R3, -, -, -, -, -, -, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hqSupport).not.mpr
        (by simp [hR0R1, hR0R3])
    exact hqR0 (hzq ▸ hzR0)
  have hzu : z ≠ u := by
    intro hzu
    have huR4 : u ∈ R4 :=
      (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) huSupport).mpr (by simp)
    exact hzR4 (hzu ▸ huR4)
  have hzv : z ≠ v := by
    intro hzv
    have hvR0 : v ∉ R0 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨-, hR0R2, hR0R3, hR0R4, -, -, -, -, -, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hvSupport).not.mpr
        (by simp [hR0R2, hR0R3, hR0R4])
    exact hvR0 (hzv ▸ hzR0)
  have hwa : w ≠ a := by
    intro hwa
    have haR2 : a ∉ R2 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨-, -, -, -, hR1R2, -, -, hR2R3, -, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) haSupport).not.mpr
        (by simp [hR1R2.symm, hR2R3])
    exact haR2 (hwa ▸ hwR2)
  have hwp : w ≠ p := by
    intro hwp
    have hpR4 : p ∈ R4 :=
      (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hpSupport).mpr (by simp)
    exact hwR4 (hwp ▸ hpR4)
  have hwq : w ≠ q := by
    intro hwq
    have hqR2 : q ∉ R2 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨-, -, -, -, hR1R2, -, -, hR2R3, -, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hqSupport).not.mpr
        (by simp [hR1R2.symm, hR2R3])
    exact hqR2 (hwq ▸ hwR2)
  have hwu : w ≠ u := by
    intro hwu
    have huR2 : u ∉ R2 := by
      have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
        rw [← hK]; exact hKcard
      obtain ⟨-, hR0R2, -, -, hR1R2, -, -, -, hR2R4, -⟩ :=
        pairwise_ne_of_quint_card_eq_five hRowsCard
      exact (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) huSupport).not.mpr
        (by simp [hR0R2.symm, hR1R2.symm, hR2R4])
    exact huR2 (hwu ▸ hwR2)
  have hwv : w ≠ v := by
    intro hwv
    have hvR4 : v ∈ R4 :=
      (mem_row_iff_of_pointSupport_eq (by rw [hK]; simp) hvSupport).mpr (by simp)
    exact hwR4 (hwv ▸ hvR4)
  have hzw : z ≠ w := fun hzw ↦ hwR0 (hzw ▸ hzR0)
  let V0 : Row α := {a, p, q, u, v, z, w}
  obtain ⟨hProj0, hProj1, hProj2, hProj3, hProj4⟩ :=
    p3k2_parallel_i_base_projections hVertices hK hKcard
      haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
  have hB01 : ({p, u, z} : Row α) ≠ {a, q, u} := by
    intro hEq
    have hpRight : p ∈ ({a, q, u} : Row α) := by rw [← hEq]; simp
    simpa [hap.symm, hpq, hpu] using hpRight
  have hB02 : ({p, u, z} : Row α) ≠ {p, v, w} := by
    intro hEq
    have huRight : u ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
    simpa [hpu.symm, huv, hwu.symm] using huRight
  have hB03 : ({p, u, z} : Row α) ≠ {a, q, v} := by
    intro hEq
    have hpRight : p ∈ ({a, q, v} : Row α) := by rw [← hEq]; simp
    simpa [hap.symm, hpq, hpv] using hpRight
  have hB04 : ({p, u, z} : Row α) ≠ {p, u, v} := by
    intro hEq
    have hzRight : z ∈ ({p, u, v} : Row α) := by rw [← hEq]; simp
    simpa [hzp, hzu, hzv] using hzRight
  have hB12 : ({a, q, u} : Row α) ≠ {p, v, w} := by
    intro hEq
    have haRight : a ∈ ({p, v, w} : Row α) := by rw [← hEq]; simp
    simpa [hap, hav, hwa.symm] using haRight
  have hB13 : ({a, q, u} : Row α) ≠ {a, q, v} := by
    intro hEq
    have huRight : u ∈ ({a, q, v} : Row α) := by rw [← hEq]; simp
    simpa [hau.symm, hqu.symm, huv] using huRight
  have hB14 : ({a, q, u} : Row α) ≠ {p, u, v} := by
    intro hEq
    have haRight : a ∈ ({p, u, v} : Row α) := by rw [← hEq]; simp
    simpa [hap, hau, hav] using haRight
  have hB23 : ({p, v, w} : Row α) ≠ {a, q, v} := by
    intro hEq
    have hpRight : p ∈ ({a, q, v} : Row α) := by rw [← hEq]; simp
    simpa [hap.symm, hpq, hpv] using hpRight
  have hB24 : ({p, v, w} : Row α) ≠ {p, u, v} := by
    intro hEq
    have hwRight : w ∈ ({p, u, v} : Row α) := by rw [← hEq]; simp
    simpa [hwp, hwu, hwv] using hwRight
  have hB34 : ({a, q, v} : Row α) ≠ {p, u, v} := by
    intro hEq
    have haRight : a ∈ ({p, u, v} : Row α) := by rw [← hEq]; simp
    simpa [hap, hau, hav] using haRight
  have hProj0' : R0 ∩ V0 = {p, u, z} := by simpa [V0] using hProj0
  have hProj1' : R1 ∩ V0 = {a, q, u} := by simpa [V0] using hProj1
  have hProj2' : R2 ∩ V0 = {p, v, w} := by simpa [V0] using hProj2
  have hProj3' : R3 ∩ V0 = {a, q, v} := by simpa [V0] using hProj3
  have hProj4' : R4 ∩ V0 = {p, u, v} := by simpa [V0] using hProj4
  have hBaseFamilyCard :
      ({{p, u, z}, {a, q, u}, {p, v, w}, {a, q, v}, {p, u, v}} :
        Hypergraph α).card = 5 := by
    simp [hB01, hB02, hB03, hB04, hB12, hB13, hB14, hB23, hB24, hB34]
  have hRestrictEq :
      restrictRows K V0 =
        {{p, u, z}, {a, q, u}, {p, v, w}, {a, q, v}, {p, u, v}} := by
    unfold restrictRows
    rw [hK]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [hProj0', hProj1', hProj2', hProj3', hProj4']
  have hProjectionCard : ∀ R ∈ K, (R ∩ V0).card = 3 := by
    intro R hRK
    have hMem : R ∩ V0 ∈ restrictRows K V0 :=
      mem_restrictRows.mpr ⟨R, hRK, rfl⟩
    rw [hRestrictEq] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with hEq | hEq | hEq | hEq | hEq
    · rw [hEq]
      simp [hpu, hzp.symm, hzu.symm]
    · calc
        (R ∩ V0).card = ({a, q, u} : Row α).card := congrArg Finset.card hEq
        _ = 3 := by simp [haq, hau, hqu]
    · rw [hEq]
      simp [hpv, hwp.symm, hwv.symm]
    · calc
        (R ∩ V0).card = ({a, q, v} : Row α).card := congrArg Finset.card hEq
        _ = 3 := by simp [haq, hav, hqv]
    · calc
        (R ∩ V0).card = ({p, u, v} : Row α).card := congrArg Finset.card hEq
        _ = 3 := by simp [hpu, hpv, huv]
  have hProjectionInj : Set.InjOn (fun R : Row α ↦ R ∩ V0) K := by
    apply Finset.card_image_iff.mp
    change (restrictRows K V0).card = K.card
    rw [hRestrictEq, hBaseFamilyCard, hKcard]
  have htV0 : t ∉ V0 := by simp [V0, hta, htp, htq, htu, htv, htz, htw]
  apply restrictRows_insert_isClutter_of_uniform_injective htV0
  · exact hProjectionCard
  · intro R hRK S hSK hEq
    exact hProjectionInj hRK hSK hEq

theorem p3k2_parallel_i_no_additional_active_point {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v z w t : α}
    {R0 R1 R2 R3 R4 Rt : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKClutter : IsClutter K)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hKDegree : MaxDegreeAtMost K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4})
    (hzR0 : z ∈ R0) (hzR1 : z ∉ R1) (hzR2 : z ∉ R2)
    (hzR3 : z ∉ R3) (hzR4 : z ∉ R4)
    (hwR0 : w ∉ R0) (hwR1 : w ∉ R1) (hwR2 : w ∈ R2)
    (hwR3 : w ∉ R3) (hwR4 : w ∉ R4)
    (hRtK : Rt ∈ K) (htRt : t ∈ Rt)
    (hta : t ≠ a) (htp : t ≠ p) (htq : t ≠ q)
    (htu : t ≠ u) (htv : t ≠ v) (htz : t ≠ z) (htw : t ≠ w) :
    False := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  obtain ⟨hAP, hPQ, hUV, hAUW, hQUW, hAVZ, hQVZ,
      -, -, -, -, haBlockerSupport, hqBlockerSupport,
      huBlockerSupport, hvBlockerSupport⟩ :=
    p3k2_parallel_i_seven_blockers hVertices hK hKcard hBDegree hPairs
      haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
  have no_a (T : Row α) (hT : T ∈ blocker K) (htT : t ∈ T) (haT : a ∈ T) : False := by
    have hSupport : T ∈ pointSupport (blocker K) a :=
      mem_pointSupport.mpr ⟨hT, haT⟩
    rw [haBlockerSupport] at hSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
    rcases hSupport with hEq | hEq | hEq
    · have : t ∈ ({a, p} : Row α) := hEq ▸ htT
      simpa [hta, htp] using this
    · have : t ∈ ({a, u, w} : Row α) := hEq ▸ htT
      simpa [hta, htu, htw] using this
    · have : t ∈ ({a, v, z} : Row α) := hEq ▸ htT
      simpa [hta, htv, htz] using this
  have no_q (T : Row α) (hT : T ∈ blocker K) (htT : t ∈ T) (hqT : q ∈ T) : False := by
    have hSupport : T ∈ pointSupport (blocker K) q :=
      mem_pointSupport.mpr ⟨hT, hqT⟩
    rw [hqBlockerSupport] at hSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
    rcases hSupport with hEq | hEq | hEq
    · have : t ∈ ({p, q} : Row α) := hEq ▸ htT
      simpa [htp, htq] using this
    · have : t ∈ ({q, u, w} : Row α) := hEq ▸ htT
      simpa [htq, htu, htw] using this
    · have : t ∈ ({q, v, z} : Row α) := hEq ▸ htT
      simpa [htq, htv, htz] using this
  have no_u (T : Row α) (hT : T ∈ blocker K) (htT : t ∈ T) (huT : u ∈ T) : False := by
    have hSupport : T ∈ pointSupport (blocker K) u :=
      mem_pointSupport.mpr ⟨hT, huT⟩
    rw [huBlockerSupport] at hSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
    rcases hSupport with hEq | hEq | hEq
    · have : t ∈ ({u, v} : Row α) := hEq ▸ htT
      simpa [htu, htv] using this
    · have : t ∈ ({a, u, w} : Row α) := hEq ▸ htT
      simpa [hta, htu, htw] using this
    · have : t ∈ ({q, u, w} : Row α) := hEq ▸ htT
      simpa [htq, htu, htw] using this
  have no_v (T : Row α) (hT : T ∈ blocker K) (htT : t ∈ T) (hvT : v ∈ T) : False := by
    have hSupport : T ∈ pointSupport (blocker K) v :=
      mem_pointSupport.mpr ⟨hT, hvT⟩
    rw [hvBlockerSupport] at hSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
    rcases hSupport with hEq | hEq | hEq
    · have : t ∈ ({u, v} : Row α) := hEq ▸ htT
      simpa [htu, htv] using this
    · have : t ∈ ({a, v, z} : Row α) := hEq ▸ htT
      simpa [hta, htv, htz] using this
    · have : t ∈ ({q, v, z} : Row α) := hEq ▸ htT
      simpa [htq, htv, htz] using this
  let V0 : Row α := {a, p, q, u, v, z, w}
  let Vt : Row α := insert t V0
  have hRestrictionClutter : IsClutter (restrictRows K Vt) := by
    simpa [Vt, V0] using
      p3k2_parallel_i_single_point_restriction_isClutter hVertices hK hKcard
        haSupport hpSupport hqSupport huSupport hvSupport
        hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
        hta htp htq htu htv htz htw
  have hRtProjection : Rt ∩ Vt ∈ restrictRows K Vt :=
    mem_restrictRows.mpr ⟨Rt, hRtK, rfl⟩
  have htProjection : t ∈ Rt ∩ Vt :=
    Finset.mem_inter.mpr ⟨htRt, by simp [Vt]⟩
  obtain ⟨T, hTRestriction, htT⟩ :=
    point_mem_some_blocker hRestrictionClutter hRtProjection htProjection
  have hTVt : T ⊆ Vt := by
    intro x hxT
    obtain ⟨P, hPPrivate⟩ :=
      (mem_blocker.mp hTRestriction).exists_privateRow hxT
    obtain ⟨R, -, hProjection⟩ := mem_restrictRows.mp hPPrivate.1
    have hxP := hPPrivate.2.2.1
    rw [← hProjection] at hxP
    exact (Finset.mem_inter.mp hxP).2
  have hTFull : T ∈ blocker K := blocker_restrictRows_lift hTVt hTRestriction
  obtain ⟨hProj0, hProj1, hProj2, hProj3, hProj4⟩ :=
    p3k2_parallel_i_base_projections hVertices hK hKcard
      haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
  by_cases htR1 : t ∈ R1
  · by_cases htR3 : t ∈ R3
    · by_cases htR0 : t ∈ R0
      · have hvR2 : v ∈ R2 := mem_row_of_projection hProj2 (by simp)
        have hvR3 : v ∈ R3 := mem_row_of_projection hProj3 (by simp)
        have hvR4 : v ∈ R4 := mem_row_of_projection hProj4 (by simp)
        have hVTTrans : IsTransversal K ({v, t} : Row α) := by
          intro R hRK
          rw [hK] at hRK
          simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
          rcases hRK with rfl | rfl | rfl | rfl | rfl
          · exact ⟨t, by simp, htR0⟩
          · exact ⟨t, by simp, htR1⟩
          · exact ⟨v, by simp, hvR2⟩
          · exact ⟨v, by simp, hvR3⟩
          · exact ⟨v, by simp, hvR4⟩
        have hVT := pair_mem_blocker_of_transversal hBRows hVTTrans
        have hVTPair : ({v, t} : Row α) ∈ pairRows (blocker K) :=
          Finset.mem_filter.mpr ⟨hVT, by simp [htv.symm]⟩
        rw [hPairs] at hVTPair
        simp only [Finset.mem_insert, Finset.mem_singleton] at hVTPair
        rcases hVTPair with hEq | hEq | hEq
        · have htRight : t ∈ ({a, p} : Row α) := by rw [← hEq]; simp
          simpa [hta, htp] using htRight
        · have htRight : t ∈ ({p, q} : Row α) := by rw [← hEq]; simp
          simpa [htp, htq] using htRight
        · have htRight : t ∈ ({u, v} : Row α) := by rw [← hEq]; simp
          simpa [htu, htv] using htRight
      · by_cases htR2 : t ∈ R2
        · have huR0 : u ∈ R0 := mem_row_of_projection hProj0 (by simp)
          have huR1 : u ∈ R1 := mem_row_of_projection hProj1 (by simp)
          have huR4 : u ∈ R4 := mem_row_of_projection hProj4 (by simp)
          have hUTTrans : IsTransversal K ({u, t} : Row α) := by
            intro R hRK
            rw [hK] at hRK
            simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
            rcases hRK with rfl | rfl | rfl | rfl | rfl
            · exact ⟨u, by simp, huR0⟩
            · exact ⟨u, by simp, huR1⟩
            · exact ⟨t, by simp, htR2⟩
            · exact ⟨t, by simp, htR3⟩
            · exact ⟨u, by simp, huR4⟩
          have hUT := pair_mem_blocker_of_transversal hBRows hUTTrans
          have hUTPair : ({u, t} : Row α) ∈ pairRows (blocker K) :=
            Finset.mem_filter.mpr ⟨hUT, by simp [htu.symm]⟩
          rw [hPairs] at hUTPair
          simp only [Finset.mem_insert, Finset.mem_singleton] at hUTPair
          rcases hUTPair with hEq | hEq | hEq
          · have htRight : t ∈ ({a, p} : Row α) := by rw [← hEq]; simp
            simpa [hta, htp] using htRight
          · have htRight : t ∈ ({p, q} : Row α) := by rw [← hEq]; simp
            simpa [htp, htq] using htRight
          · have htRight : t ∈ ({u, v} : Row α) := by rw [← hEq]; simp
            simpa [htu, htv] using htRight
        · have huR0 : u ∈ R0 := mem_row_of_projection hProj0 (by simp)
          have huw : u ≠ w := by
            intro huw
            exact hwR0 (huw ▸ huR0)
          have huR2 : u ∉ R2 :=
            not_mem_row_of_projection hProj2 (by simp) (by simp [hpu.symm, huv, huw])
          have huR3 : u ∉ R3 :=
            not_mem_row_of_projection hProj3 (by simp) (by simp [hau.symm, hqu.symm, huv])
          have hTUWTrans : IsTransversal K ({t, u, w} : Row α) := by
            intro R hRK
            rw [hK] at hRK
            simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
            rcases hRK with rfl | rfl | rfl | rfl | rfl
            · exact ⟨u, by simp, huR0⟩
            · exact ⟨t, by simp, htR1⟩
            · exact ⟨w, by simp, hwR2⟩
            · exact ⟨t, by simp, htR3⟩
            · exact ⟨u, by simp, mem_row_of_projection hProj4 (by simp)⟩
          have hTUW : ({t, u, w} : Row α) ∈ blocker K :=
            triple_mem_blocker_of_private_rows hTUWTrans
              (by rw [hK]; simp) htR3 huR3 hwR3
              (by rw [hK]; simp) huR0 htR0 hwR0
              (by rw [hK]; simp) hwR2 htR2 huR2
          exact no_u {t, u, w} hTUW (by simp) (by simp)
    · have hR3Projection : R3 ∩ Vt ∈ restrictRows K Vt :=
        mem_restrictRows.mpr ⟨R3, by rw [hK]; simp, rfl⟩
      have hR3Form : R3 ∩ Vt = {a, q, v} := by
        calc
          R3 ∩ Vt = R3 ∩ V0 := by ext x; simp [Vt, htR3]
          _ = {a, q, v} := hProj3
      obtain ⟨x, hxT, hxR3⟩ := (mem_blocker.mp hTRestriction).prop _ hR3Projection
      rw [hR3Form] at hxR3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxR3
      rcases hxR3 with rfl | rfl | rfl
      · exact no_a T hTFull htT hxT
      · exact no_q T hTFull htT hxT
      · exact no_v T hTFull htT hxT
  · have hR1Projection : R1 ∩ Vt ∈ restrictRows K Vt :=
      mem_restrictRows.mpr ⟨R1, by rw [hK]; simp, rfl⟩
    have hR1Form : R1 ∩ Vt = {a, q, u} := by
      calc
        R1 ∩ Vt = R1 ∩ V0 := by ext x; simp [Vt, htR1]
        _ = {a, q, u} := hProj1
    obtain ⟨x, hxT, hxR1⟩ := (mem_blocker.mp hTRestriction).prop _ hR1Projection
    rw [hR1Form] at hxR1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxR1
    rcases hxR1 with rfl | rfl | rfl
    · exact no_a T hTFull htT hxT
    · exact no_q T hTFull htT hxT
    · exact no_u T hTFull htT hxT

theorem p3k2_parallel_i_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKClutter : IsClutter K)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hKDegree : MaxDegreeAtMost K 3)
    (hBcard : (blocker K).card = 8)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R1, R3})
    (hpSupport : pointSupport K p = {R0, R2, R4})
    (hqSupport : pointSupport K q = {R1, R3})
    (huSupport : pointSupport K u = {R0, R1, R4})
    (hvSupport : pointSupport K v = {R2, R3, R4}) :
    False := by
  obtain ⟨z, w, hzR0, hzR1, hzR2, hzR3, hzR4,
      hwR0, hwR1, hwR2, hwR3, hwR4⟩ :=
    p3k2_parallel_i_exists_pure_witnesses hVertices hKClutter hK hKcard
      hBRows hBDegree hPairs haSupport hpSupport hqSupport huSupport hvSupport
  obtain ⟨hAP, hPQ, hUV, hAUW, hQUW, hAVZ, hQVZ,
      -, -, -, -, haBlockerSupport, hqBlockerSupport,
      huBlockerSupport, -⟩ :=
    p3k2_parallel_i_seven_blockers hVertices hK hKcard hBDegree hPairs
      haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
  let V0 : Row α := {a, p, q, u, v, z, w}
  have hR1Subset : R1 ⊆ V0 := by
    intro t htR1
    by_contra htV0
    have hta : t ≠ a := fun h ↦ htV0 (h ▸ by simp [V0])
    have htp : t ≠ p := fun h ↦ htV0 (h ▸ by simp [V0])
    have htq : t ≠ q := fun h ↦ htV0 (h ▸ by simp [V0])
    have htu : t ≠ u := fun h ↦ htV0 (h ▸ by simp [V0])
    have htv : t ≠ v := fun h ↦ htV0 (h ▸ by simp [V0])
    have htz : t ≠ z := fun h ↦ htV0 (h ▸ by simp [V0])
    have htw : t ≠ w := fun h ↦ htV0 (h ▸ by simp [V0])
    exact p3k2_parallel_i_no_additional_active_point hVertices hKClutter hK hKcard
      hKDegree hBRows hBDegree hPairs haSupport hpSupport hqSupport huSupport
      hvSupport hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
      (by rw [hK]; simp) htR1 hta htp htq htu htv htz htw
  obtain ⟨-, hProj1, -, -, -⟩ :=
    p3k2_parallel_i_base_projections hVertices hK hKcard
      haSupport hpSupport hqSupport huSupport hvSupport
      hzR0 hzR1 hzR2 hzR3 hzR4 hwR0 hwR1 hwR2 hwR3 hwR4
  have hR1 : R1 = {a, q, u} := by
    rw [← hProj1]
    exact (Finset.inter_eq_left.mpr hR1Subset).symm
  let Seven : Hypergraph α :=
    {{a, p}, {p, q}, {u, v}, {a, u, w}, {q, u, w}, {a, v, z}, {q, v, z}}
  have hSevenSubset : Seven ⊆ blocker K := by
    intro T hT
    simp only [Seven, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAP
    · exact hPQ
    · exact hUV
    · exact hAUW
    · exact hQUW
    · exact hAVZ
    · exact hQVZ
  have hBlockerSubset : blocker K ⊆ Seven := by
    intro T hTK
    obtain ⟨x, hxT, hxR1⟩ := (mem_blocker.mp hTK).prop R1 (by rw [hK]; simp)
    rw [hR1] at hxR1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxR1
    rcases hxR1 with hxa | hxq | hxu
    · have hSupport : T ∈ pointSupport (blocker K) a :=
        mem_pointSupport.mpr ⟨hTK, hxa ▸ hxT⟩
      rw [haBlockerSupport] at hSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
      rcases hSupport with hT | hT | hT <;> subst T <;> simp [Seven]
    · have hSupport : T ∈ pointSupport (blocker K) q :=
        mem_pointSupport.mpr ⟨hTK, hxq ▸ hxT⟩
      rw [hqBlockerSupport] at hSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
      rcases hSupport with hT | hT | hT <;> subst T <;> simp [Seven]
    · have hSupport : T ∈ pointSupport (blocker K) u :=
        mem_pointSupport.mpr ⟨hTK, hxu ▸ hxT⟩
      rw [huBlockerSupport] at hSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hSupport
      rcases hSupport with hT | hT | hT <;> subst T <;> simp [Seven]
  have hEq : blocker K = Seven := Finset.Subset.antisymm hBlockerSubset hSevenSubset
  have hSevenUpper : Seven.card ≤ 7 := by
    calc
      Seven.card ≤
          ({{p, q}, {u, v}, {a, u, w}, {q, u, w}, {a, v, z}, {q, v, z}} :
            Hypergraph α).card + 1 := by
        simpa [Seven] using
          Finset.card_insert_le ({a, p} : Row α)
            ({{p, q}, {u, v}, {a, u, w}, {q, u, w}, {a, v, z}, {q, v, z}} :
              Hypergraph α)
      _ ≤ 6 + 1 := Nat.add_le_add_right Finset.card_le_six 1
      _ = 7 := rfl
  rw [hEq] at hBcard
  omega

theorem p3k2_parallel_d_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q u v : α}
    {R0 R1 R2 R3 R4 : Row α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hKClutter : IsClutter K)
    (hK : K = {R0, R1, R2, R3, R4})
    (hKcard : K.card = 5)
    (hKRows : RowsCardAtLeast K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}})
    (haSupport : pointSupport K a = {R2, R4})
    (hpSupport : pointSupport K p = {R0, R1, R3})
    (hqSupport : pointSupport K q = {R2, R4})
    (huSupport : pointSupport K u = {R0, R1, R2})
    (hvSupport : pointSupport K v = {R3, R4}) :
    False := by
  obtain ⟨hap, haq, hau, hav, hpq, hpu, hpv, hqu, hqv, huv⟩ :=
    pairwise_ne_of_quint_card_eq_five hVertices
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  obtain ⟨hR0R1, hR0R2, hR0R3, hR0R4, hR1R2,
      hR1R3, hR1R4, hR2R3, hR2R4, hR3R4⟩ :=
    pairwise_ne_of_quint_card_eq_five hRowsCard
  have hR0K : R0 ∈ K := by rw [hK]; simp
  have hR1K : R1 ∈ K := by rw [hK]; simp
  have hR2K : R2 ∈ K := by rw [hK]; simp
  have hR3K : R3 ∈ K := by rw [hK]; simp
  have hR4K : R4 ∈ K := by rw [hK]; simp
  have haR0 : a ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K haSupport).not.mpr
      (by simp [hR0R2, hR0R4])
  have haR1 : a ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K haSupport).not.mpr
      (by simp [hR1R2, hR1R4])
  have haR2 : a ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K haSupport).mpr (by simp)
  have haR3 : a ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K haSupport).not.mpr
      (by simp [hR2R3.symm, hR3R4])
  have haR4 : a ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K haSupport).mpr (by simp)
  have hqR0 : q ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hqSupport).not.mpr
      (by simp [hR0R2, hR0R4])
  have hqR1 : q ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hqSupport).not.mpr
      (by simp [hR1R2, hR1R4])
  have hqR2 : q ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hqSupport).mpr (by simp)
  have hqR3 : q ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hqSupport).not.mpr
      (by simp [hR2R3.symm, hR3R4])
  have hqR4 : q ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hqSupport).mpr (by simp)
  have hpR0 : p ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hpSupport).mpr (by simp)
  have hpR1 : p ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hpSupport).mpr (by simp)
  have hpR2 : p ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hpSupport).not.mpr
      (by simp [hR0R2.symm, hR1R2.symm, hR2R3])
  have hpR3 : p ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hpSupport).mpr (by simp)
  have hpR4 : p ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hpSupport).not.mpr
      (by simp [hR0R4.symm, hR1R4.symm, hR3R4.symm])
  have huR0 : u ∈ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K huSupport).mpr (by simp)
  have huR1 : u ∈ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K huSupport).mpr (by simp)
  have huR2 : u ∈ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K huSupport).mpr (by simp)
  have huR3 : u ∉ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K huSupport).not.mpr
      (by simp [hR0R3.symm, hR1R3.symm, hR2R3.symm])
  have huR4 : u ∉ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K huSupport).not.mpr
      (by simp [hR0R4.symm, hR1R4.symm, hR2R4.symm])
  have hvR0 : v ∉ R0 :=
    (mem_row_iff_of_pointSupport_eq hR0K hvSupport).not.mpr
      (by simp [hR0R3, hR0R4])
  have hvR1 : v ∉ R1 :=
    (mem_row_iff_of_pointSupport_eq hR1K hvSupport).not.mpr
      (by simp [hR1R3, hR1R4])
  have hvR2 : v ∉ R2 :=
    (mem_row_iff_of_pointSupport_eq hR2K hvSupport).not.mpr
      (by simp [hR2R3, hR2R4])
  have hvR3 : v ∈ R3 :=
    (mem_row_iff_of_pointSupport_eq hR3K hvSupport).mpr (by simp)
  have hvR4 : v ∈ R4 :=
    (mem_row_iff_of_pointSupport_eq hR4K hvSupport).mpr (by simp)
  have hAP : ({a, p} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hUV : ({u, v} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have no_extra_pair (r s : α) (hrs : r ≠ s)
      (hAPne : ({r, s} : Row α) ≠ {a, p})
      (hPQne : ({r, s} : Row α) ≠ {p, q})
      (hUVne : ({r, s} : Row α) ≠ {u, v})
      (hTransversal : IsTransversal K ({r, s} : Row α)) : False := by
    have hPair := pair_mem_blocker_of_transversal hBRows hTransversal
    have hPairRow : ({r, s} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hPair, by simp [hrs]⟩
    rw [hPairs] at hPairRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPairRow
    exact hPairRow.elim hAPne (fun h ↦ h.elim hPQne hUVne)
  have hR0NotSubset : ¬ R0 ⊆ R1 := by
    intro hSubset
    exact hR0R1 (hKClutter hR0K hR1K hSubset)
  have hR1NotSubset : ¬ R1 ⊆ R0 := by
    intro hSubset
    exact hR0R1.symm (hKClutter hR1K hR0K hSubset)
  obtain ⟨x, hxR0, hxR1⟩ := Finset.not_subset.mp hR0NotSubset
  obtain ⟨y, hyR1, hyR0⟩ := Finset.not_subset.mp hR1NotSubset
  have hxa : x ≠ a := fun h ↦ haR0 (h ▸ hxR0)
  have hxp : x ≠ p := fun h ↦ hxR1 (h ▸ hpR1)
  have hxq : x ≠ q := fun h ↦ hqR0 (h ▸ hxR0)
  have hxu : x ≠ u := fun h ↦ hxR1 (h ▸ huR1)
  have hxv : x ≠ v := fun h ↦ hvR0 (h ▸ hxR0)
  have hya : y ≠ a := fun h ↦ haR1 (h ▸ hyR1)
  have hyp : y ≠ p := fun h ↦ hyR0 (h ▸ hpR0)
  have hyq : y ≠ q := fun h ↦ hqR1 (h ▸ hyR1)
  have hyu : y ≠ u := fun h ↦ hyR0 (h ▸ huR0)
  have hyv : y ≠ v := fun h ↦ hvR1 (h ▸ hyR1)
  have hxy : x ≠ y := fun h ↦ hxR1 (h ▸ hyR1)
  have not_R4_of_R3 (s : α)
      (hsa : s ≠ a) (hsp : s ≠ p) (hsq : s ≠ q)
      (hsu : s ≠ u) (hsv : s ≠ v) (hsR3 : s ∈ R3) : s ∉ R4 := by
    intro hsR4
    apply no_extra_pair u s hsu.symm
      (by
        intro hEq
        have hsRight : s ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hsa, hsp] using hsRight)
      (by
        intro hEq
        have hsRight : s ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hsp, hsq] using hsRight)
      (by
        intro hEq
        have hsRight : s ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hsu, hsv] using hsRight)
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, huR0⟩
    · exact ⟨u, by simp, huR1⟩
    · exact ⟨u, by simp, huR2⟩
    · exact ⟨s, by simp, hsR3⟩
    · exact ⟨s, by simp, hsR4⟩
  have not_R2_of_R4 (s : α)
      (hsa : s ≠ a) (hsp : s ≠ p) (hsq : s ≠ q)
      (hsu : s ≠ u) (hsv : s ≠ v) (hsR4 : s ∈ R4) : s ∉ R2 := by
    intro hsR2
    apply no_extra_pair p s hsp.symm
      (by
        intro hEq
        have hsRight : s ∈ ({a, p} : Row α) := by rw [← hEq]; simp
        simpa [hsa, hsp] using hsRight)
      (by
        intro hEq
        have hsRight : s ∈ ({p, q} : Row α) := by rw [← hEq]; simp
        simpa [hsp, hsq] using hsRight)
      (by
        intro hEq
        have hsRight : s ∈ ({u, v} : Row α) := by rw [← hEq]; simp
        simpa [hsu, hsv] using hsRight)
    intro R hRK
    rw [hK] at hRK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
    rcases hRK with rfl | rfl | rfl | rfl | rfl
    · exact ⟨p, by simp, hpR0⟩
    · exact ⟨p, by simp, hpR1⟩
    · exact ⟨s, by simp, hsR2⟩
    · exact ⟨p, by simp, hpR3⟩
    · exact ⟨s, by simp, hsR4⟩
  have au_blocker (s : α) (hsR3 : s ∈ R3) (hsR4 : s ∉ R4)
      (hsSide : s ∉ R0 ∨ s ∉ R1) :
      ({a, u, s} : Row α) ∈ blocker K := by
    have hTransversal : IsTransversal K ({a, u, s} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨u, by simp, huR0⟩
      · exact ⟨u, by simp, huR1⟩
      · exact ⟨a, by simp, haR2⟩
      · exact ⟨s, by simp, hsR3⟩
      · exact ⟨a, by simp, haR4⟩
    rcases hsSide with hsR0 | hsR1
    · exact triple_mem_blocker_of_private_rows hTransversal
        hR4K haR4 huR4 hsR4 hR0K huR0 haR0 hsR0 hR3K hsR3 haR3 huR3
    · exact triple_mem_blocker_of_private_rows hTransversal
        hR4K haR4 huR4 hsR4 hR1K huR1 haR1 hsR1 hR3K hsR3 haR3 huR3
  have qu_blocker (s : α) (hsR3 : s ∈ R3) (hsR4 : s ∉ R4)
      (hsSide : s ∉ R0 ∨ s ∉ R1) :
      ({q, u, s} : Row α) ∈ blocker K := by
    have hTransversal : IsTransversal K ({q, u, s} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨u, by simp, huR0⟩
      · exact ⟨u, by simp, huR1⟩
      · exact ⟨q, by simp, hqR2⟩
      · exact ⟨s, by simp, hsR3⟩
      · exact ⟨q, by simp, hqR4⟩
    rcases hsSide with hsR0 | hsR1
    · exact triple_mem_blocker_of_private_rows hTransversal
        hR4K hqR4 huR4 hsR4 hR0K huR0 hqR0 hsR0 hR3K hsR3 hqR3 huR3
    · exact triple_mem_blocker_of_private_rows hTransversal
        hR4K hqR4 huR4 hsR4 hR1K huR1 hqR1 hsR1 hR3K hsR3 hqR3 huR3
  have pu_blocker (s : α) (hsR4 : s ∈ R4) (hsR2 : s ∉ R2) (hsR3 : s ∉ R3) :
      ({p, u, s} : Row α) ∈ blocker K := by
    have hTransversal : IsTransversal K ({p, u, s} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨p, by simp, hpR0⟩
      · exact ⟨p, by simp, hpR1⟩
      · exact ⟨u, by simp, huR2⟩
      · exact ⟨p, by simp, hpR3⟩
      · exact ⟨s, by simp, hsR4⟩
    exact triple_mem_blocker_of_private_rows hTransversal
      hR3K hpR3 huR3 hsR3 hR2K huR2 hpR2 hsR2 hR4K hsR4 hpR4 huR4
  have side_blocker (l r : α)
      (hlR0 : l ∈ R0) (hlR1 : l ∉ R1)
      (hrR1 : r ∈ R1) (hrR0 : r ∉ R0)
      (hlR4 : l ∉ R4) (hrR4 : r ∉ R4)
      (hR3Hit : l ∈ R3 ∨ r ∈ R3) :
      ({a, l, r} : Row α) ∈ blocker K := by
    have hTransversal : IsTransversal K ({a, l, r} : Row α) := by
      intro R hRK
      rw [hK] at hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
      rcases hRK with rfl | rfl | rfl | rfl | rfl
      · exact ⟨l, by simp, hlR0⟩
      · exact ⟨r, by simp, hrR1⟩
      · exact ⟨a, by simp, haR2⟩
      · rcases hR3Hit with hlR3 | hrR3
        · exact ⟨l, by simp, hlR3⟩
        · exact ⟨r, by simp, hrR3⟩
      · exact ⟨a, by simp, haR4⟩
    exact triple_mem_blocker_of_private_rows hTransversal
      hR4K haR4 hlR4 hrR4 hR0K hlR0 haR0 hrR0 hR1K hrR1 haR1 hlR1
  have twin_contradiction (s l r : α)
      (hsa : s ≠ a) (hsp : s ≠ p) (hsq : s ≠ q)
      (hsu : s ≠ u) (hsv : s ≠ v)
      (hla : l ≠ a) (hlq : l ≠ q) (hlu : l ≠ u)
      (hra : r ≠ a) (hrq : r ≠ q) (hru : r ≠ u)
      (hS : ({a, u, s} : Row α) ∈ blocker K)
      (hT : ({a, l, r} : Row α) ∈ blocker K)
      (hsT : s ∈ ({a, l, r} : Row α)) : False := by
    have hLower := twin_endpoint_amplifier haq hsa.symm
      (haSupport.trans hqSupport.symm) hS hT
      (by
        intro hEq
        have huRight : u ∈ ({a, l, r} : Row α) := by rw [← hEq]; simp
        simpa [hau.symm, hlu.symm, hru.symm] using huRight)
      (by simp) (by simp)
      (by simp [haq.symm, hqu, hsq.symm])
      (by simp [haq.symm, hlq.symm, hrq.symm])
      (by simp) hsT
    exact (not_le_of_gt hLower) (hBDegree s)
  by_cases hLeft3 : ∃ s ∈ R0, s ∉ R1 ∧ s ∈ R3
  · obtain ⟨s, hsR0, hsR1, hsR3⟩ := hLeft3
    have hsa : s ≠ a := fun h ↦ haR0 (h ▸ hsR0)
    have hsp : s ≠ p := fun h ↦ hsR1 (h ▸ hpR1)
    have hsq : s ≠ q := fun h ↦ hqR0 (h ▸ hsR0)
    have hsu : s ≠ u := fun h ↦ hsR1 (h ▸ huR1)
    have hsv : s ≠ v := fun h ↦ hvR0 (h ▸ hsR0)
    have hsR4 := not_R4_of_R3 s hsa hsp hsq hsu hsv hsR3
    have hAUS := au_blocker s hsR3 hsR4 (Or.inr hsR1)
    by_cases hyR4 : y ∈ R4
    · have hyR2 := not_R2_of_R4 y hya hyp hyq hyu hyv hyR4
      have hyR3 : y ∉ R3 := fun hyR3 ↦
        (not_R4_of_R3 y hya hyp hyq hyu hyv hyR3) hyR4
      have hQUS := qu_blocker s hsR3 hsR4 (Or.inr hsR1)
      have hPUY := pu_blocker y hyR4 hyR2 hyR3
      exact p3k2_u_pressure_impossible hVertices hBDegree hUV hAUS hQUS hPUY
        hsa hsp hsq hsu hsv hya hyp hyq hyu hyv
    · have hASY := side_blocker s y hsR0 hsR1 hyR1 hyR0 hsR4 hyR4 (Or.inl hsR3)
      exact twin_contradiction s s y hsa hsp hsq hsu hsv
        hsa hsq hsu hya hyq hyu hAUS hASY (by simp)
  · by_cases hRight3 : ∃ s ∈ R1, s ∉ R0 ∧ s ∈ R3
    · obtain ⟨s, hsR1, hsR0, hsR3⟩ := hRight3
      have hsa : s ≠ a := fun h ↦ haR1 (h ▸ hsR1)
      have hsp : s ≠ p := fun h ↦ hsR0 (h ▸ hpR0)
      have hsq : s ≠ q := fun h ↦ hqR1 (h ▸ hsR1)
      have hsu : s ≠ u := fun h ↦ hsR0 (h ▸ huR0)
      have hsv : s ≠ v := fun h ↦ hvR1 (h ▸ hsR1)
      have hsR4 := not_R4_of_R3 s hsa hsp hsq hsu hsv hsR3
      have hAUS := au_blocker s hsR3 hsR4 (Or.inl hsR0)
      by_cases hxR4 : x ∈ R4
      · have hxR2 := not_R2_of_R4 x hxa hxp hxq hxu hxv hxR4
        have hxR3 : x ∉ R3 := fun hxR3 ↦
          (not_R4_of_R3 x hxa hxp hxq hxu hxv hxR3) hxR4
        have hQUS := qu_blocker s hsR3 hsR4 (Or.inl hsR0)
        have hPUX := pu_blocker x hxR4 hxR2 hxR3
        exact p3k2_u_pressure_impossible hVertices hBDegree hUV hAUS hQUS hPUX
          hsa hsp hsq hsu hsv hxa hxp hxq hxu hxv
      · have hAXS := side_blocker x s hxR0 hxR1 hsR1 hsR0 hxR4 hsR4 (Or.inr hsR3)
        exact twin_contradiction s x s hsa hsp hsq hsu hsv
          hxa hxq hxu hsa hsq hsu hAUS hAXS (by simp)
    · have hR3NotSubset : ¬ R3 ⊆ ({p, v} : Row α) := by
        intro hSubset
        have hUpper := Finset.card_le_card hSubset
        have hLower := hKRows R3 hR3K
        have hPairUpper : ({p, v} : Row α).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨z, hzR3, hzPair⟩ := Finset.not_subset.mp hR3NotSubset
      have hzp : z ≠ p := by
        intro hzp
        apply hzPair
        simpa [hzp]
      have hzv : z ≠ v := by
        intro hzv
        apply hzPair
        simpa [hzv]
      have hza : z ≠ a := fun h ↦ haR3 (h ▸ hzR3)
      have hzq : z ≠ q := fun h ↦ hqR3 (h ▸ hzR3)
      have hzu : z ≠ u := fun h ↦ huR3 (h ▸ hzR3)
      have hzR0 : z ∉ R0 := by
        intro hzR0
        have hzR1 : z ∈ R1 := by
          by_contra hzR1
          exact hLeft3 ⟨z, hzR0, hzR1, hzR3⟩
        apply no_extra_pair a z hza.symm
          (by
            intro hEq
            have hzRight : z ∈ ({a, p} : Row α) := by rw [← hEq]; simp
            simpa [hza, hzp] using hzRight)
          (by
            intro hEq
            have haRight : a ∈ ({p, q} : Row α) := by rw [← hEq]; simp
            simpa [hap, haq] using haRight)
          (by
            intro hEq
            have haRight : a ∈ ({u, v} : Row α) := by rw [← hEq]; simp
            simpa [hau, hav] using haRight)
        intro R hRK
        rw [hK] at hRK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
        rcases hRK with rfl | rfl | rfl | rfl | rfl
        · exact ⟨z, by simp, hzR0⟩
        · exact ⟨z, by simp, hzR1⟩
        · exact ⟨a, by simp, haR2⟩
        · exact ⟨z, by simp, hzR3⟩
        · exact ⟨a, by simp, haR4⟩
      have hzR1 : z ∉ R1 := by
        intro hzR1
        have hzR0' : z ∈ R0 := by
          by_contra hzR0'
          exact hRight3 ⟨z, hzR1, hzR0', hzR3⟩
        exact hzR0 hzR0'
      have hzR4 := not_R4_of_R3 z hza hzp hzq hzu hzv hzR3
      have hAUZ := au_blocker z hzR3 hzR4 (Or.inl hzR0)
      by_cases hxR4 : x ∈ R4
      · have hxR2 := not_R2_of_R4 x hxa hxp hxq hxu hxv hxR4
        have hxR3 : x ∉ R3 := fun hxR3 ↦
          (not_R4_of_R3 x hxa hxp hxq hxu hxv hxR3) hxR4
        have hQUZ := qu_blocker z hzR3 hzR4 (Or.inl hzR0)
        have hPUX := pu_blocker x hxR4 hxR2 hxR3
        exact p3k2_u_pressure_impossible hVertices hBDegree hUV hAUZ hQUZ hPUX
          hza hzp hzq hzu hzv hxa hxp hxq hxu hxv
      · by_cases hyR4 : y ∈ R4
        · have hyR2 := not_R2_of_R4 y hya hyp hyq hyu hyv hyR4
          have hyR3 : y ∉ R3 := fun hyR3 ↦
            (not_R4_of_R3 y hya hyp hyq hyu hyv hyR3) hyR4
          have hQUZ := qu_blocker z hzR3 hzR4 (Or.inl hzR0)
          have hPUY := pu_blocker y hyR4 hyR2 hyR3
          exact p3k2_u_pressure_impossible hVertices hBDegree hUV hAUZ hQUZ hPUY
            hza hzp hzq hzu hzv hya hyp hyq hyu hyv
        · have hxR3 : x ∉ R3 := fun hxR3 ↦ hLeft3 ⟨x, hxR0, hxR1, hxR3⟩
          have hyR3 : y ∉ R3 := fun hyR3 ↦ hRight3 ⟨y, hyR1, hyR0, hyR3⟩
          have hAXYZ : ({a, x, y, z} : Row α) ∈ blocker K := by
            have hTransversal : IsTransversal K ({a, x, y, z} : Row α) := by
              intro R hRK
              rw [hK] at hRK
              simp only [Finset.mem_insert, Finset.mem_singleton] at hRK
              rcases hRK with rfl | rfl | rfl | rfl | rfl
              · exact ⟨x, by simp, hxR0⟩
              · exact ⟨y, by simp, hyR1⟩
              · exact ⟨a, by simp, haR2⟩
              · exact ⟨z, by simp, hzR3⟩
              · exact ⟨a, by simp, haR4⟩
            exact quad_mem_blocker_of_private_rows hTransversal
              hR4K haR4 hxR4 hyR4 hzR4 hR0K hxR0 haR0 hyR0 hzR0
              hR1K hyR1 haR1 hxR1 hzR1 hR3K hzR3 haR3 hxR3 hyR3
          have hLower := twin_endpoint_amplifier haq hza.symm
            (haSupport.trans hqSupport.symm) hAUZ hAXYZ
            (by
              intro hEq
              have huRight : u ∈ ({a, x, y, z} : Row α) := by rw [← hEq]; simp
              simpa [hau.symm, hxu.symm, hyu.symm, hzu.symm] using huRight)
            (by simp) (by simp)
            (by simp [haq.symm, hqu, hzq.symm])
            (by simp [haq.symm, hxq.symm, hyq.symm, hzq.symm])
            (by simp) (by simp)
          exact (not_le_of_gt hLower) (hBDegree z)

theorem p3k2_pairGraph_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {a p q u v : α}
    (hVertices : ({a, p, q, u, v} : Row α).card = 5)
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hHRows : RowsCardAtLeast H 2)
    (hHDegree : MaxDegreeAtMost H 3)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hPairs : pairRows H = {{a, p}, {p, q}, {u, v}}) :
    False := by
  let K := blocker H
  have hBlockerK : blocker K = H := by
    simpa [K] using blocker_involution hH
  have hKClutter : IsClutter K := blocker_isClutter H
  have hKcard : K.card = 5 := by simpa [K] using hDualCard
  have hKRows : RowsCardAtLeast K 3 := by simpa [K] using hDualRows
  have hKDegree : MaxDegreeAtMost K 3 := by simpa [K] using hDualDegree
  have hBcard : (blocker K).card = 8 := by rw [hBlockerK, hHcard]
  have hBRows : RowsCardAtLeast (blocker K) 2 := by rw [hBlockerK]; exact hHRows
  have hBDegree : MaxDegreeAtMost (blocker K) 3 := by rw [hBlockerK]; exact hHDegree
  have hKPairs : pairRows (blocker K) = {{a, p}, {p, q}, {u, v}} := by
    rw [hBlockerK]
    exact hPairs
  obtain ⟨R0, R1, R2, R3, R4, hRowsCard, hK,
      hD | hD | hI⟩ :=
    p3k2_parallel_normal_form hVertices hKcard hKRows hKDegree
      hBRows hBDegree hKPairs
  · exact p3k2_parallel_d_impossible hVertices hKClutter hK hKcard hKRows
      hBRows hBDegree hKPairs hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2
  · have hVerticesSwap : ({a, p, q, v, u} : Row α).card = 5 := by
      simpa [Finset.pair_comm, or_comm, or_left_comm] using hVertices
    have hPairsSwap : pairRows (blocker K) = {{a, p}, {p, q}, {v, u}} := by
      simpa [Finset.pair_comm] using hKPairs
    exact p3k2_parallel_d_impossible hVerticesSwap hKClutter hK hKcard hKRows
      hBRows hBDegree hPairsSwap hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.2 hD.2.2.2.1
  · exact p3k2_parallel_i_impossible hVertices hKClutter hK hKcard hKDegree
      hBcard hBRows hBDegree hKPairs hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2

end AiMathLab.P0054.G413
