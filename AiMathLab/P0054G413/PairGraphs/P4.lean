import AiMathLab.P0054G413.PairGraphs.Trace

namespace AiMathLab.P0054.G413

theorem pairwise_ne_of_quad_card_eq_four {α : Type*} [DecidableEq α]
    {a b c d : α} (hCard : ({a, b, c, d} : Row α).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have card_three_ne_four (x y z : α) : ({x, y, z} : Row α).card ≠ 4 := by
    have hUpper : ({x, y, z} : Row α).card ≤ 3 := Finset.card_le_three
    omega
  constructor
  · intro hab
    subst b
    exact card_three_ne_four a c d (by simpa using hCard)
  constructor
  · intro hac
    subst c
    exact card_three_ne_four b a d (by simpa using hCard)
  constructor
  · intro had
    subst d
    exact card_three_ne_four b c a (by simpa using hCard)
  constructor
  · intro hbc
    subst c
    exact card_three_ne_four a b d (by simpa using hCard)
  constructor
  · intro hbd
    subst d
    exact card_three_ne_four a c b (by simpa using hCard)
  · intro hcd
    subst d
    exact card_three_ne_four a b c (by simpa using hCard)

theorem two_blocker_trace_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {Z L : Hypergraph α} {P : Row α} {b : α}
    (hZRows : RowsCardAtLeast Z 3) (hPcard : 2 ≤ P.card)
    (hL : L = minimize (insert {b} (insert P Z)))
    (hBcard : (blocker L).card = 2) :
    ∃ c d, c ≠ d ∧ P = {c, d} ∧
      ∀ R ∈ Z, b ∈ R ∨ ({c, d} : Row α) ⊆ R := by
  have hLClutter : IsClutter L := by
    rw [hL]
    exact minimize_isClutter _
  obtain ⟨Q₁, Q₂, hQ₁Q₂, hBQ⟩ := Finset.card_eq_two.mp hBcard
  have hQ₁b : Q₁ ∈ blocker L := by simp [hBQ]
  have hQ₂b : Q₂ ∈ blocker L := by simp [hBQ]
  have hLtwo : L = twoRowBlockers Q₁ Q₂ :=
    family_eq_twoRowBlockers_of_blocker_eq_pair hLClutter hBQ
  have hbL : ({b} : Row α) ∈ L := by
    rw [hL]
    apply mem_minimize.mpr
    refine ⟨by simp, ?_⟩
    intro F hF hFb
    simp only [Finset.mem_insert] at hF
    rcases hF with rfl | rfl | hFZ
    · exact Finset.Subset.rfl
    · have hCard := Finset.card_le_card hFb
      simp at hCard
      omega
    · have hCard := Finset.card_le_card hFb
      have hLarge := hZRows F hFZ
      simp at hCard
      omega
  have hbInter : b ∈ Q₁ ∩ Q₂ := by
    have hbTwo : ({b} : Row α) ∈ twoRowBlockers Q₁ Q₂ := by
      rw [← hLtwo]
      exact hbL
    rcases mem_twoRowBlockers.mp hbTwo with hSingleton | hCross
    · obtain ⟨x, hxInter, hxEq⟩ := hSingleton
      have hxb : x = b := by simpa using hxEq
      simpa [hxb] using hxInter
    · obtain ⟨x, hxQ₁, y, hyQ₂, hxyEq⟩ := hCross
      have hxy : x ≠ y := fun hxy ↦
        (Finset.mem_sdiff.mp hxQ₁).2 (hxy ▸ (Finset.mem_sdiff.mp hyQ₂).1)
      have hCardEq := congrArg Finset.card hxyEq
      simp [hxy] at hCardEq
  have hInterEq : Q₁ ∩ Q₂ = {b} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hbInter, ?_⟩
    intro x hxInter
    have hxL : ({x} : Row α) ∈ L := by
      rw [hLtwo]
      exact mem_twoRowBlockers.mpr (Or.inl ⟨x, hxInter, rfl⟩)
    have hxSource : ({x} : Row α) ∈ insert {b} (insert P Z) := by
      exact minimize_subset _ (by simpa [hL] using hxL)
    simp only [Finset.mem_insert] at hxSource
    rcases hxSource with hxEq | hxEq | hxZ
    · simpa using hxEq
    · have hCardEq := congrArg Finset.card hxEq
      simp at hCardEq
      omega
    · have hxLarge := hZRows {x} hxZ
      simp at hxLarge
  have hQ₁notSubset : ¬ Q₁ ⊆ Q₂ := by
    intro hSubset
    exact hQ₁Q₂ (blocker_isClutter L hQ₁b hQ₂b hSubset)
  have hQ₂notSubset : ¬ Q₂ ⊆ Q₁ := by
    intro hSubset
    exact hQ₁Q₂.symm (blocker_isClutter L hQ₂b hQ₁b hSubset)
  obtain ⟨c, hcQ₁, hcQ₂⟩ := Finset.not_subset.mp hQ₁notSubset
  obtain ⟨d, hdQ₂, hdQ₁⟩ := Finset.not_subset.mp hQ₂notSubset
  have hcd : c ≠ d := fun hcd ↦ hcQ₂ (hcd ▸ hdQ₂)
  have hPairL : ({c, d} : Row α) ∈ L := by
    rw [hLtwo]
    exact mem_twoRowBlockers.mpr (Or.inr
      ⟨c, Finset.mem_sdiff.mpr ⟨hcQ₁, hcQ₂⟩,
        d, Finset.mem_sdiff.mpr ⟨hdQ₂, hdQ₁⟩, rfl⟩)
  have pair_eq_P {E : Row α} (hEL : E ∈ L) (hEcard : E.card = 2) : E = P := by
    have hESource : E ∈ insert {b} (insert P Z) := by
      exact minimize_subset _ (by simpa [hL] using hEL)
    simp only [Finset.mem_insert] at hESource
    rcases hESource with hEq | hEq | hEZ
    · have hCardEq := congrArg Finset.card hEq
      simp [hEcard] at hCardEq
    · exact hEq
    · have hELarge := hZRows E hEZ
      omega
  have hP : P = {c, d} := by
    exact (pair_eq_P hPairL (by simp [hcd])).symm
  refine ⟨c, d, hcd, hP, ?_⟩
  intro R hRZ
  have hRSource : R ∈ insert {b} (insert P Z) := by simp [hRZ]
  obtain ⟨E, hEL, hER⟩ := exists_minimize_subset hRSource
  have hETwo : E ∈ twoRowBlockers Q₁ Q₂ := by
    rw [← hLtwo, hL]
    exact hEL
  rcases mem_twoRowBlockers.mp hETwo with hSingleton | hCross
  · obtain ⟨x, hxInter, hxEq⟩ := hSingleton
    have hxb : x = b := by
      have : x ∈ ({b} : Row α) := hInterEq ▸ hxInter
      simpa using this
    exact Or.inl (hER (by simp [← hxEq, hxb]))
  · obtain ⟨x, hxQ₁, y, hyQ₂, hxyEq⟩ := hCross
    have hxy : x ≠ y := fun hxy ↦
      (Finset.mem_sdiff.mp hxQ₁).2 (hxy ▸ (Finset.mem_sdiff.mp hyQ₂).1)
    have hEcard : E.card = 2 := by rw [← hxyEq]; simp [hxy]
    have hEP : E = P := pair_eq_P (by rw [hL]; exact hEL) hEcard
    exact Or.inr (by simpa [hP, hEP] using hER)

theorem pointSupport_eq_three_of_two_rows {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {A B : Row α}
    (hDegree : degree H x = 3)
    (hAH : A ∈ H) (hBH : B ∈ H) (hAB : A ≠ B)
    (hxA : x ∈ A) (hxB : x ∈ B) :
    ∃ C, C ∈ H ∧ x ∈ C ∧ C ≠ A ∧ C ≠ B ∧
      pointSupport H x = {A, B, C} := by
  have hKnownSubset : ({A, B} : Hypergraph α) ⊆ pointSupport H x := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact mem_pointSupport.mpr ⟨hAH, hxA⟩
    · exact mem_pointSupport.mpr ⟨hBH, hxB⟩
  have hKnownCard : ({A, B} : Hypergraph α).card = 2 := by simp [hAB]
  have hSupportCard : (pointSupport H x).card = 3 := by
    simpa [pointSupport_card] using hDegree
  have hKnownLt : ({A, B} : Hypergraph α).card < (pointSupport H x).card := by
    omega
  obtain ⟨C, hCSupport, hCKnown⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hKnownLt
  obtain ⟨hCH, hxC⟩ := mem_pointSupport.mp hCSupport
  have hCA : C ≠ A := by
    intro hCA
    exact hCKnown (by simp [hCA])
  have hCB : C ≠ B := by
    intro hCB
    exact hCKnown (by simp [hCB])
  have hTripleCard : ({A, B, C} : Hypergraph α).card = 3 := by
    simp [hAB, hCA.symm, hCB.symm]
  have hTripleSubset : ({A, B, C} : Hypergraph α) ⊆ pointSupport H x := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact mem_pointSupport.mpr ⟨hAH, hxA⟩
    · exact mem_pointSupport.mpr ⟨hBH, hxB⟩
    · exact hCSupport
  have hEq : ({A, B, C} : Hypergraph α) = pointSupport H x :=
    Finset.eq_of_subset_of_card_le hTripleSubset (by omega)
  exact ⟨C, hCH, hxC, hCA, hCB, hEq.symm⟩

theorem degree_insert_eq_add_indicator {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {E : Row α} (hEH : E ∉ H) (x : α) :
    degree (insert E H) x = degree H x + (if x ∈ E then 1 else 0) := by
  by_cases hxE : x ∈ E
  · rw [degree_insert_of_notMem hEH hxE]
    simp [hxE]
  · have hFilter :
        (insert E H).filter (fun R ↦ x ∈ R) = H.filter (fun R ↦ x ∈ R) := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hRH, hxR⟩
        · exact (hxE hxR).elim
        · exact ⟨hRH, hxR⟩
      · rintro ⟨hRH, hxR⟩
        exact ⟨Or.inr hRH, hxR⟩
    rw [degree, hFilter]
    simp only [if_neg hxE, Nat.add_zero]
    rfl

theorem pairSide_blocker_erase {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H) (hpq : p ≠ q)
    (hPair : ({p, q} : Row α) ∈ H)
    {T : Row α} (hT : T ∈ blocker H) (hpT : p ∈ T) (hqT : q ∉ T) :
    T.erase p ∈ blocker (pairSide H p q) := by
  rw [pairSide, blocker_residual, blocker_avoidPoint hH]
  apply mem_avoidPoint.mpr
  refine ⟨mem_minimize.mpr ⟨Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩, ?_⟩
  · intro F hF hFD
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hF
    by_cases hpU : p ∈ U
    · have hUT : U ⊆ T := by
        intro x hxU
        by_cases hxp : x = p
        · simpa [hxp] using hpT
        · exact Finset.mem_of_mem_erase (hFD (Finset.mem_erase.mpr ⟨hxp, hxU⟩))
      have hEq : U = T := blocker_isClutter H hU hT hUT
      simpa [hEq]
    · have hPairDual : ({p, q} : Row α) ∈ blocker (blocker H) := by
        rw [blocker_involution hH]
        exact hPair
      obtain ⟨x, hxPair, hxU⟩ := (mem_blocker.mp hPairDual).prop U hU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hxp | hxq
      · exact (hpU (hxp ▸ hxU)).elim
      · have hqU : q ∈ U := hxq ▸ hxU
        have hqErase : q ∈ U.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hqU⟩
        exact (hqT (Finset.mem_of_mem_erase (hFD hqErase))).elim
  · exact fun hqErase ↦ hqT (Finset.mem_of_mem_erase hqErase)

theorem pairSide_blocker_image_eq_support_sdiff {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H) (hpq : p ≠ q)
    (hPair : ({p, q} : Row α) ∈ H) :
    (blocker (pairSide H p q)).image (insert p) =
      pointSupport (blocker H) p \ pointSupport (blocker H) q := by
  ext T
  constructor
  · intro hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    have hLift : insert p D ∈ blocker H := pairSide_blocker_lift hPair hD
    have hqD : q ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H p q)
    exact Finset.mem_sdiff.mpr
      ⟨mem_pointSupport.mpr ⟨hLift, by simp⟩,
        fun h ↦ by
          have hqInsert := (mem_pointSupport.mp h).2
          simp only [Finset.mem_insert] at hqInsert
          rcases hqInsert with hqp | hqD'
          · exact hpq hqp.symm
          · exact hqD hqD'⟩
  · intro hT
    obtain ⟨hpSupport, hqSupport⟩ := Finset.mem_sdiff.mp hT
    obtain ⟨hTb, hpT⟩ := mem_pointSupport.mp hpSupport
    have hqT : q ∉ T := fun hqT ↦ hqSupport (mem_pointSupport.mpr ⟨hTb, hqT⟩)
    have hErase := pairSide_blocker_erase hH hpq hPair hTb hpT hqT
    exact Finset.mem_image.mpr ⟨T.erase p, hErase, Finset.insert_erase hpT⟩

theorem pairSide_blocker_card_eq_support_sdiff {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {p q : α}
    (hH : IsClutter H) (hpq : p ≠ q)
    (hPair : ({p, q} : Row α) ∈ H) :
    (blocker (pairSide H p q)).card =
      (pointSupport (blocker H) p \ pointSupport (blocker H) q).card := by
  have hInjective :
      Set.InjOn (insert p) (↑(blocker (pairSide H p q)) : Set (Row α)) := by
    intro D hD E hE hEq
    have hpD : p ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H p q)
    have hpE : p ∉ E :=
      (mem_blocker.mp hE).avoids_inactive (pairSide_rows_avoid_first H p q)
    simpa [hpD, hpE] using congrArg (Finset.erase · p) hEq
  rw [← pairSide_blocker_image_eq_support_sdiff hH hpq hPair,
    Finset.card_image_iff.mpr hInjective]

theorem pairSide_blocker_card_add_both_le {α : Type*}
    [Fintype α] [DecidableEq α]
    {H C : Hypergraph α} {p q : α}
    (hpq : p ≠ q) (hPair : ({p, q} : Row α) ∈ H)
    (hCH : C ⊆ blocker H)
    (hBoth : ∀ T ∈ C, p ∈ T ∧ q ∈ T) :
    (blocker (pairSide H p q)).card +
        (blocker (pairSide H q p)).card + C.card ≤ (blocker H).card := by
  let liftP : Row α → Row α := insert p
  let liftQ : Row α → Row α := insert q
  let left : Hypergraph α := (blocker (pairSide H p q)).image liftP
  let right : Hypergraph α := (blocker (pairSide H q p)).image liftQ
  let sides : Hypergraph α := left ∪ right
  have hLeftSubset : left ⊆ blocker H := by
    intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    exact pairSide_blocker_lift hPair hD
  have hRightSubset : right ⊆ blocker H := by
    intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    simpa [Finset.pair_comm] using
      (pairSide_blocker_lift (H := H) (p := q) (q := p) (D := D)
        (by simpa [Finset.pair_comm] using hPair) hD)
  have hLiftPInjective :
      Set.InjOn liftP (↑(blocker (pairSide H p q)) : Set (Row α)) := by
    intro D hD F hF hEq
    have hpD : p ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H p q)
    have hpF : p ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_first H p q)
    simpa [liftP, hpD, hpF] using congrArg (Finset.erase · p) hEq
  have hLiftQInjective :
      Set.InjOn liftQ (↑(blocker (pairSide H q p)) : Set (Row α)) := by
    intro D hD F hF hEq
    have hqD : q ∉ D :=
      (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_first H q p)
    have hqF : q ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_first H q p)
    simpa [liftQ, hqD, hqF] using congrArg (Finset.erase · q) hEq
  have hLeftRight : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro T hTLeft hTRight
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hTLeft
    obtain ⟨F, hF, hEq⟩ := Finset.mem_image.mp hTRight
    have hpF : p ∉ F :=
      (mem_blocker.mp hF).avoids_inactive (pairSide_rows_avoid_second H q p)
    have hpRight : p ∈ liftQ F := by
      rw [hEq]
      simp [liftP]
    simp only [liftQ, Finset.mem_insert] at hpRight
    rcases hpRight with hpq' | hpF'
    · exact hpq hpq'
    · exact hpF hpF'
  have hSidesC : Disjoint sides C := by
    apply Finset.disjoint_left.mpr
    intro T hTSides hTC
    obtain ⟨hpT, hqT⟩ := hBoth T hTC
    rcases Finset.mem_union.mp hTSides with hTLeft | hTRight
    · obtain ⟨D, hD, hEq⟩ := Finset.mem_image.mp hTLeft
      have hqD : q ∉ D :=
        (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H p q)
      have hqLift : q ∈ liftP D := hEq ▸ hqT
      simp only [liftP, Finset.mem_insert] at hqLift
      rcases hqLift with hqp | hqD'
      · exact hpq hqp.symm
      · exact hqD hqD'
    · obtain ⟨D, hD, hEq⟩ := Finset.mem_image.mp hTRight
      have hpD : p ∉ D :=
        (mem_blocker.mp hD).avoids_inactive (pairSide_rows_avoid_second H q p)
      have hpLift : p ∈ liftQ D := hEq ▸ hpT
      simp only [liftQ, Finset.mem_insert] at hpLift
      rcases hpLift with hpq' | hpD'
      · exact hpq hpq'
      · exact hpD hpD'
  have hSidesSubset : sides ⊆ blocker H :=
    Finset.union_subset hLeftSubset hRightSubset
  have hAllSubset : sides ∪ C ⊆ blocker H :=
    Finset.union_subset hSidesSubset hCH
  have hSidesCard : sides.card =
      (blocker (pairSide H p q)).card +
        (blocker (pairSide H q p)).card := by
    calc
      sides.card = left.card + right.card := by
        change (left ∪ right).card = left.card + right.card
        exact Finset.card_union_of_disjoint hLeftRight
      _ = (blocker (pairSide H p q)).card +
          (blocker (pairSide H q p)).card := by
        rw [Finset.card_image_iff.mpr hLiftPInjective,
          Finset.card_image_iff.mpr hLiftQInjective]
  calc
    (blocker (pairSide H p q)).card +
          (blocker (pairSide H q p)).card + C.card = sides.card + C.card := by
      rw [hSidesCard]
    _ = (sides ∪ C).card := (Finset.card_union_of_disjoint hSidesC).symm
    _ ≤ (blocker H).card := Finset.card_le_card hAllSubset

theorem p4_good_blocker_lift {α : Type*}
    [Fintype α] [DecidableEq α]
    {H Z : Hypergraph α} {a p q b : α} {C E X Y T : Row α}
    (hDistinct : ({a, p, q, b} : Row α).card = 4)
    (hHdecomp : H = {{a, p}, {p, q}, {q, b}, X, Y} ∪ Z)
    (hX : X = insert p E) (hY : Y = insert q C)
    (hqX : q ∉ X) (hpY : p ∉ Y)
    (hpZ : ∀ R ∈ Z, p ∉ R) (hqZ : ∀ R ∈ Z, q ∉ R)
    (hT : T ∈ blocker Z) (hGood : IsGoodTraceBlocker a b C E T) :
    insert p (insert q T) ∈ blocker H := by
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hpT : p ∉ T :=
    (mem_blocker.mp hT).avoids_inactive hpZ
  have hqT : q ∉ T :=
    (mem_blocker.mp hT).avoids_inactive hqZ
  apply mem_blocker.mpr
  have hTransversal : IsTransversal H (insert p (insert q T)) := by
    intro R hRH
    rw [hHdecomp] at hRH
    rcases Finset.mem_union.mp hRH with hRFixed | hRZ
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hRFixed
      rcases hRFixed with rfl | rfl | rfl | rfl | rfl
      · exact ⟨p, by simp, by simp⟩
      · exact ⟨p, by simp, by simp⟩
      · exact ⟨q, by simp, by simp⟩
      · exact ⟨p, by simp, by rw [hX]; simp⟩
      · exact ⟨q, by simp, by rw [hY]; simp⟩
    · obtain ⟨x, hxT, hxR⟩ := (mem_blocker.mp hT).prop R hRZ
      exact ⟨x, by simp [hxT], hxR⟩
  apply hTransversal.minimal_of_privateRows
  intro x hxU
  simp only [Finset.mem_insert] at hxU
  rcases hxU with hxp | hxq | hxT
  · subst x
    by_cases haT : a ∈ T
    · refine ⟨X, by rw [hHdecomp]; simp, by simp, by rw [hX]; simp, ?_⟩
      intro y hyU hyX
      simp only [Finset.mem_insert] at hyU
      rcases hyU with hyp | hyq | hyT
      · exact hyp
      · exact (hqX (hyq ▸ hyX)).elim
      · rw [hX] at hyX
        simp only [Finset.mem_insert] at hyX
        rcases hyX with hyp | hyE
        · exact hyp
        · exact (Finset.disjoint_left.mp (hGood.1 haT) hyT hyE).elim
    · refine ⟨{a, p}, by rw [hHdecomp]; simp, by simp, by simp, ?_⟩
      intro y hyU hyAP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyU hyAP
      rcases hyU with hyp | hyq | hyT
      · exact hyp
      · rcases hyAP with hya | hyp
        · exact (haq (hyq.symm.trans hya).symm).elim
        · exact (hpq (hyq.symm.trans hyp).symm).elim
      · rcases hyAP with hya | hyp
        · exact (haT (hya ▸ hyT)).elim
        · exact (hpT (hyp ▸ hyT)).elim
  · subst x
    by_cases hbT : b ∈ T
    · refine ⟨Y, by rw [hHdecomp]; simp, by simp, by rw [hY]; simp, ?_⟩
      intro y hyU hyY
      simp only [Finset.mem_insert] at hyU
      rcases hyU with hyp | hyq | hyT
      · exact (hpY (hyp ▸ hyY)).elim
      · exact hyq
      · rw [hY] at hyY
        simp only [Finset.mem_insert] at hyY
        rcases hyY with hyq | hyC
        · exact hyq
        · exact (Finset.disjoint_left.mp (hGood.2 hbT) hyT hyC).elim
    · refine ⟨{q, b}, by rw [hHdecomp]; simp, by simp, by simp, ?_⟩
      intro y hyU hyQB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyU hyQB
      rcases hyU with hyp | hyq | hyT
      · rcases hyQB with hyq | hyb
        · exact (hpq (hyp.symm.trans hyq)).elim
        · exact (hpb (hyp.symm.trans hyb)).elim
      · exact hyq
      · rcases hyQB with hyq | hyb
        · exact (hqT (hyq ▸ hyT)).elim
        · exact (hbT (hyb ▸ hyT)).elim
  · obtain ⟨R, hPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
    refine ⟨R, by rw [hHdecomp]; exact Finset.mem_union_right _ hPrivate.1,
      by simp [hxT], hPrivate.2.2.1, ?_⟩
    intro y hyU hyR
    simp only [Finset.mem_insert] at hyU
    rcases hyU with hyp | hyq | hyT
    · exact (hpZ R hPrivate.1 (hyp ▸ hyR)).elim
    · exact (hqZ R hPrivate.1 (hyq ▸ hyR)).elim
    · exact hPrivate.2.2.2 hyT hyR

theorem path_middle_support_two_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a p q b : α}
    (hKcard : K.card = 5)
    (hKdegree : MaxDegreeAtMost K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hAP : ({a, p} : Row α) ∈ blocker K)
    (hPQ : ({p, q} : Row α) ∈ blocker K)
    (hQB : ({q, b} : Row α) ∈ blocker K)
    (hABnot : ({a, b} : Row α) ∉ blocker K)
    (hap : a ≠ p) (hpq : p ≠ q) (hqb : q ≠ b)
    (hSp : (pointSupport K p).card = 2)
    (hSq : (pointSupport K q).card = 3)
    (hDisjoint : Disjoint (pointSupport K p) (pointSupport K q)) :
    False := by
  have hAPUnion := pair_blocker_support_union hAP
  have hPQUnion := pair_blocker_support_union hPQ
  have hQBUnion := pair_blocker_support_union hQB
  have hSqSa : pointSupport K q ⊆ pointSupport K a := by
    intro E hEq
    have hEK : E ∈ K := (mem_pointSupport.mp hEq).1
    have hEp : E ∉ pointSupport K p :=
      Finset.disjoint_left.mp hDisjoint.symm hEq
    have hUnion : E ∈ pointSupport K a ∪ pointSupport K p := by
      rw [hAPUnion]
      exact hEK
    rcases Finset.mem_union.mp hUnion with hEa | hEp'
    · exact hEa
    · exact (hEp hEp').elim
  have hSaUpper : (pointSupport K a).card ≤ 3 := by
    simpa [pointSupport_card] using hKdegree a
  have hSaEq : pointSupport K a = pointSupport K q :=
    (Finset.eq_of_subset_of_card_le hSqSa (by omega)).symm
  have hSpSb : pointSupport K p ⊆ pointSupport K b := by
    intro E hEp
    have hEK : E ∈ K := (mem_pointSupport.mp hEp).1
    have hEq : E ∉ pointSupport K q :=
      Finset.disjoint_left.mp hDisjoint hEp
    have hUnion : E ∈ pointSupport K q ∪ pointSupport K b := by
      rw [hQBUnion]
      exact hEK
    rcases Finset.mem_union.mp hUnion with hEq' | hEb
    · exact (hEq hEq').elim
    · exact hEb
  obtain ⟨E, hEK, haE, hbE⟩ :=
    exists_row_avoiding_nonblocker_pair hBRows hABnot
  have hEPQ : E ∈ pointSupport K p ∪ pointSupport K q := by
    rw [hPQUnion]
    exact hEK
  rcases Finset.mem_union.mp hEPQ with hEp | hEq
  · exact hbE (mem_pointSupport.mp (hSpSb hEp)).2
  · exact haE (mem_pointSupport.mp (hSaEq.symm ▸ hEq)).2

theorem p4_central_support_type {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (hHRows : RowsCardAtLeast H 2)
    (hDualCard : (blocker H).card = 5)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphP4 H) :
    ∃ a p q b,
      ({a, p, q, b} : Row α).card = 4 ∧
      pairRows H = {{a, p}, {p, q}, {q, b}} ∧
      (pointSupport (blocker H) p).card = 3 ∧
      (pointSupport (blocker H) q).card = 3 ∧
      (pointSupport (blocker H) p ∩ pointSupport (blocker H) q).card = 1 := by
  obtain ⟨a, p, q, b, hDistinct, hPairs⟩ := hShape
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hAP : ({a, p} : Row α) ∈ H := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ H := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hQB : ({q, b} : Row α) ∈ H := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hAPDual : ({a, p} : Row α) ∈ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hAP
  have hPQDual : ({p, q} : Row α) ∈ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hPQ
  have hQBDual : ({q, b} : Row α) ∈ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hQB
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 2 := by
    rw [blocker_involution hH]
    exact hHRows
  have hABnotH : ({a, b} : Row α) ∉ H := by
    intro hAB
    have hABPair : ({a, b} : Row α) ∈ pairRows H :=
      Finset.mem_filter.mpr ⟨hAB, by simp [hab]⟩
    rw [hPairs] at hABPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hABPair
    rcases hABPair with hEq | hEq | hEq
    · have hpAB : p ∈ ({a, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpAB
      rcases hpAB with hpa | hpb'
      · exact hap hpa.symm
      · exact hpb hpb'
    · have hpAB : p ∈ ({a, b} : Row α) := hEq.symm ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpAB
      rcases hpAB with hpa | hpb'
      · exact hap hpa.symm
      · exact hpb hpb'
    · have hqAB : q ∈ ({a, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqAB
      rcases hqAB with hqa | hqb'
      · exact haq hqa.symm
      · exact hqb hqb'
  have hABnotDual : ({a, b} : Row α) ∉ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hABnotH
  rcases pair_blocker_support_type hDualCard hDualDegree hPQDual hpq with
      hD | hD | hI
  · exact (path_middle_support_two_impossible hDualCard hDualDegree hDualRows
      hAPDual hPQDual hQBDual hABnotDual hap hpq hqb hD.1 hD.2.1 hD.2.2).elim
  · exact (path_middle_support_two_impossible hDualCard hDualDegree hDualRows
      (by simpa [Finset.pair_comm] using hQBDual)
      (by simpa [Finset.pair_comm] using hPQDual)
      (by simpa [Finset.pair_comm] using hAPDual)
      (by simpa [Finset.pair_comm] using hABnotDual)
      hqb.symm hpq.symm hap.symm hD.2.1 hD.1 hD.2.2.symm).elim
  · exact ⟨a, p, q, b, hDistinct, hPairs, hI.1, hI.2.1, hI.2.2⟩

theorem p4_central_structure {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (_hHcard : H.card = 8)
    (hHRows : RowsCardAtLeast H 2)
    (hHdegree : MaxDegreeAtMost H 3)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphP4 H) :
    ∃ a p q b,
      ({a, p, q, b} : Row α).card = 4 ∧
      pairRows H = {{a, p}, {p, q}, {q, b}} ∧
      degree H p = 3 ∧ degree H q = 3 ∧
      (blocker (pairSide H p q)).card = 2 ∧
      (blocker (pairSide H q p)).card = 2 := by
  obtain ⟨a, p, q, b, hDistinct, hPairs, hSp, hSq, hInter⟩ :=
    p4_central_support_type hH hHRows hDualCard hDualDegree hShape
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hPQ : ({p, q} : Row α) ∈ H := by
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hSideP : (blocker (pairSide H p q)).card = 2 := by
    rw [pairSide_blocker_card_eq_support_sdiff hH hpq hPQ,
      Finset.card_sdiff, hSp]
    have hInter' :
        (pointSupport (blocker H) q ∩ pointSupport (blocker H) p).card = 1 := by
      simpa [Finset.inter_comm] using hInter
    rw [hInter']
  have hSideQ : (blocker (pairSide H q p)).card = 2 := by
    rw [pairSide_blocker_card_eq_support_sdiff hH hpq.symm
      (by simpa [Finset.pair_comm] using hPQ),
      Finset.card_sdiff, hSq, hInter]
  have hPairRowsCard : (pairRows H).card = 3 := by
    rw [hPairs]
    have hAPnePQ : ({a, p} : Row α) ≠ {p, q} := by
      intro hEq
      have haPQ : a ∈ ({p, q} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at haPQ
      rcases haPQ with hap' | haq'
      · exact hap hap'
      · exact haq haq'
    have hAPneQB : ({a, p} : Row α) ≠ {q, b} := by
      intro hEq
      have haQB : a ∈ ({q, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at haQB
      rcases haQB with haq' | hab'
      · exact haq haq'
      · exact hab hab'
    have hPQneQB : ({p, q} : Row α) ≠ {q, b} := by
      intro hEq
      have hpQB : p ∈ ({q, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpQB
      rcases hpQB with hpq' | hpb'
      · exact hpq hpq'
      · exact hpb hpb'
    simp [hAPnePQ, hAPneQB, hPQneQB]
  have hPairRowsUpper : (pairRows H).card ≤ 3 := by omega
  have central_degree_three (x y : α) (hxy : x ≠ y)
      (hPairXY : ({x, y} : Row α) ∈ H)
      (hSide : (blocker (pairSide H x y)).card = 2)
      (hCover : ∀ A ∈ pairRows H, x ∈ A ∨ y ∈ A) : degree H y = 3 := by
    by_contra hNotThree
    have hDegreeY : degree H y ≤ 2 := by
      have := hHdegree y
      omega
    have hSideRows : RowsCardAtLeast (blocker (pairSide H x y)) 2 :=
      pairSide_blocker_rows_cardAtLeast_two hPairXY hDualRows
    obtain ⟨w, A, -, -, hAH, hAcard, hxA, hyA, -⟩ :=
      pairSide_two_blocker_structure hH hHRows hPairRowsUpper hPairXY hDegreeY
        hSideRows hSide
    have hAPair : A ∈ pairRows H := Finset.mem_filter.mpr ⟨hAH, hAcard⟩
    rcases hCover A hAPair with hx | hy
    · exact hxA hx
    · exact hyA hy
  have hCentralCover : ∀ A ∈ pairRows H, p ∈ A ∨ q ∈ A := by
    intro A hA
    rw [hPairs] at hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have hqDegree := central_degree_three p q hpq hPQ hSideP hCentralCover
  have hpDegree := central_degree_three q p hpq.symm
    (by simpa [Finset.pair_comm] using hPQ) hSideQ
    (by
      intro A hA
      rcases hCentralCover A hA with hp | hq
      · exact Or.inr hp
      · exact Or.inl hq)
  exact ⟨a, p, q, b, hDistinct, hPairs, hpDegree, hqDegree, hSideP, hSideQ⟩

theorem p4_central_row_decomposition {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α} {a p q b : α}
    (hH : IsClutter H) (hHcard : H.card = 8) (hHRows : RowsCardAtLeast H 2)
    (hDistinct : ({a, p, q, b} : Row α).card = 4)
    (hPairs : pairRows H = {{a, p}, {p, q}, {q, b}})
    (hpDegree : degree H p = 3) (hqDegree : degree H q = 3) :
    ∃ X Y Z,
      X ∈ H ∧ Y ∈ H ∧ p ∈ X ∧ q ∉ X ∧ p ∉ Y ∧ q ∈ Y ∧
      3 ≤ X.card ∧ 3 ≤ Y.card ∧ X ≠ Y ∧
      Z = avoidPoint (avoidPoint H p) q ∧ Z.card = 3 ∧
      IsClutter Z ∧ RowsCardAtLeast Z 3 ∧
      (∀ R ∈ Z, p ∉ R) ∧ (∀ R ∈ Z, q ∉ R) ∧
      H = {{a, p}, {p, q}, {q, b}, X, Y} ∪ Z := by
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hAP : ({a, p} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hQB : ({q, b} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hAPnePQ : ({a, p} : Row α) ≠ {p, q} := by
    intro hEq
    have haPQ : a ∈ ({p, q} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at haPQ
    rcases haPQ with hap' | haq'
    · exact hap hap'
    · exact haq haq'
  have hPQneQB : ({p, q} : Row α) ≠ {q, b} := by
    intro hEq
    have hpQB : p ∈ ({q, b} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpQB
    rcases hpQB with hpq' | hpb'
    · exact hpq hpq'
    · exact hpb hpb'
  obtain ⟨X, hXH, hpX, hXneAP, hXnePQ, hPSupport⟩ :=
    pointSupport_eq_three_of_two_rows hpDegree hAP hPQ hAPnePQ
      (by simp) (by simp)
  obtain ⟨Y, hYH, hqY, hYnePQ, hYneQB, hQSupport⟩ :=
    pointSupport_eq_three_of_two_rows hqDegree hPQ hQB hPQneQB
      (by simp) (by simp)
  have hqX : q ∉ X := by
    intro hqX
    have hPairSubset : ({p, q} : Row α) ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpX
      · exact hqX
    have hEq : ({p, q} : Row α) = X := hH hPQ hXH hPairSubset
    exact hXnePQ hEq.symm
  have hpY : p ∉ Y := by
    intro hpY
    have hPairSubset : ({p, q} : Row α) ⊆ Y := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpY
      · exact hqY
    have hEq : ({p, q} : Row α) = Y := hH hPQ hYH hPairSubset
    exact hYnePQ hEq.symm
  have hXY : X ≠ Y := by
    intro hXY
    exact hpY (hXY ▸ hpX)
  have hXcard : 3 ≤ X.card := by
    have hXlower := hHRows X hXH
    by_contra hnot
    have hXpair : X ∈ pairRows H :=
      Finset.mem_filter.mpr ⟨hXH, by omega⟩
    rw [hPairs] at hXpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXpair
    rcases hXpair with hEq | hEq | hEq
    · exact hXneAP hEq
    · exact hXnePQ hEq
    · exact hqX (hEq ▸ by simp)
  have hYcard : 3 ≤ Y.card := by
    have hYlower := hHRows Y hYH
    by_contra hnot
    have hYpair : Y ∈ pairRows H :=
      Finset.mem_filter.mpr ⟨hYH, by omega⟩
    rw [hPairs] at hYpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hYpair
    rcases hYpair with hEq | hEq | hEq
    · exact hpY (hEq ▸ by simp)
    · exact hYnePQ hEq
    · exact hYneQB hEq
  let Z := avoidPoint (avoidPoint H p) q
  have hpZ : ∀ R ∈ Z, p ∉ R := by
    intro R hR
    exact (mem_avoidPoint.mp (mem_avoidPoint.mp hR).1).2
  have hqZ : ∀ R ∈ Z, q ∉ R := by
    intro R hR
    exact (mem_avoidPoint.mp hR).2
  have hZH : Z ⊆ H := by
    intro R hR
    exact (mem_avoidPoint.mp (mem_avoidPoint.mp hR).1).1
  have hZClutter : IsClutter Z := by
    intro A hAZ B hBZ hAB
    exact hH (hZH hAZ) (hZH hBZ) hAB
  have hZRows : RowsCardAtLeast Z 3 := by
    intro R hRZ
    have hRlower := hHRows R (hZH hRZ)
    by_contra hnot
    have hRpair : R ∈ pairRows H :=
      Finset.mem_filter.mpr ⟨hZH hRZ, by omega⟩
    rw [hPairs] at hRpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRpair
    rcases hRpair with hEq | hEq | hEq
    · exact hpZ R hRZ (hEq ▸ by simp)
    · exact hpZ R hRZ (hEq ▸ by simp)
    · exact hqZ R hRZ (hEq ▸ by simp)
  have hAvoidPCard : (avoidPoint H p).card = 5 := by
    have hPartition := card_avoidPoint_add_degree H p
    omega
  have hQSupportAvoid :
      pointSupport (avoidPoint H p) q = {{q, b}, Y} := by
    ext R
    constructor
    · intro hR
      obtain ⟨hRAvoid, hqR⟩ := mem_pointSupport.mp hR
      obtain ⟨hRH, hpR⟩ := mem_avoidPoint.mp hRAvoid
      have hRSupport : R ∈ pointSupport H q :=
        mem_pointSupport.mpr ⟨hRH, hqR⟩
      rw [hQSupport] at hRSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRSupport
      rcases hRSupport with hEq | hEq | hEq
      · exact (hpR (hEq ▸ by simp)).elim
      · simp [hEq]
      · simp [hEq]
    · intro hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with hEq | hEq
      · subst R
        exact mem_pointSupport.mpr
          ⟨mem_avoidPoint.mpr ⟨hQB, by simp [hpq, hpb]⟩, by simp⟩
      · subst R
        exact mem_pointSupport.mpr ⟨mem_avoidPoint.mpr ⟨hYH, hpY⟩, hqY⟩
  have hQDegreeAvoid : degree (avoidPoint H p) q = 2 := by
    rw [← pointSupport_card, hQSupportAvoid]
    simp [hYneQB.symm]
  have hZcard : Z.card = 3 := by
    have hPartition := card_avoidPoint_add_degree (avoidPoint H p) q
    simpa [Z, hQDegreeAvoid, hAvoidPCard] using hPartition
  have hHdecomp : H = {{a, p}, {p, q}, {q, b}, X, Y} ∪ Z := by
    ext R
    constructor
    · intro hRH
      by_cases hpR : p ∈ R
      · have hRSupport : R ∈ pointSupport H p :=
          mem_pointSupport.mpr ⟨hRH, hpR⟩
        rw [hPSupport] at hRSupport
        simp only [Finset.mem_insert, Finset.mem_singleton] at hRSupport
        rcases hRSupport with rfl | rfl | rfl <;>
          exact Finset.mem_union_left _ (by simp)
      · by_cases hqR : q ∈ R
        · have hRSupport : R ∈ pointSupport H q :=
            mem_pointSupport.mpr ⟨hRH, hqR⟩
          rw [hQSupport] at hRSupport
          simp only [Finset.mem_insert, Finset.mem_singleton] at hRSupport
          rcases hRSupport with hEq | hEq | hEq
          · exact (hpR (hEq ▸ by simp)).elim
          · exact Finset.mem_union_left _ (by simp [hEq])
          · exact Finset.mem_union_left _ (by simp [hEq])
        · exact Finset.mem_union_right _
            (mem_avoidPoint.mpr ⟨mem_avoidPoint.mpr ⟨hRH, hpR⟩, hqR⟩)
    · intro hR
      rcases Finset.mem_union.mp hR with hRFixed | hRZ
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hRFixed
        rcases hRFixed with rfl | rfl | rfl | rfl | rfl
        · exact hAP
        · exact hPQ
        · exact hQB
        · exact hXH
        · exact hYH
      · exact hZH hRZ
  exact ⟨X, Y, Z, hXH, hYH, hpX, hqX, hpY, hqY,
    hXcard, hYcard, hXY, rfl, hZcard, hZClutter, hZRows,
    hpZ, hqZ, hHdecomp⟩

theorem p4_pairSide_left_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {H Z : Hypergraph α} {a p q b : α} {X Y : Row α}
    (hDistinct : ({a, p, q, b} : Row α).card = 4)
    (hHdecomp : H = {{a, p}, {p, q}, {q, b}, X, Y} ∪ Z)
    (hpX : p ∈ X) (hpY : p ∉ Y)
    (hpZ : ∀ R ∈ Z, p ∉ R) (hqZ : ∀ R ∈ Z, q ∉ R) :
    pairSide H p q = minimize (insert {b} (insert (Y.erase q) Z)) := by
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hSource :
      deletePoint (avoidPoint H p) q = insert {b} (insert (Y.erase q) Z) := by
    ext T
    constructor
    · intro hT
      obtain ⟨R, hRAvoid, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨hRH, hpR⟩ := mem_avoidPoint.mp hRAvoid
      rw [hHdecomp] at hRH
      rcases Finset.mem_union.mp hRH with hRFixed | hRZ
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hRFixed
        rcases hRFixed with rfl | rfl | rfl | rfl | rfl
        · exact (hpR (by simp)).elim
        · exact (hpR (by simp)).elim
        · simp [hqb]
        · exact (hpR hpX).elim
        · simp
      · have hqR := hqZ R hRZ
        simp [Finset.erase_eq_of_notMem hqR, hRZ]
    · intro hT
      simp only [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · apply Finset.mem_image.mpr
        refine ⟨{q, b}, mem_avoidPoint.mpr ⟨?_, ?_⟩, by simp [hqb]⟩
        · rw [hHdecomp]
          simp
        · simp [hpq, hpb]
      · rcases hT with rfl | hTZ
        · apply Finset.mem_image.mpr
          refine ⟨Y, mem_avoidPoint.mpr ⟨?_, hpY⟩, rfl⟩
          rw [hHdecomp]
          simp
        · apply Finset.mem_image.mpr
          refine ⟨T, mem_avoidPoint.mpr ⟨?_, hpZ T hTZ⟩, ?_⟩
          · rw [hHdecomp]
            exact Finset.mem_union_right _ hTZ
          · exact Finset.erase_eq_of_notMem (hqZ T hTZ)
  rw [pairSide, residual, hSource]

theorem p4_pairSide_right_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {H Z : Hypergraph α} {a p q b : α} {X Y : Row α}
    (hDistinct : ({a, p, q, b} : Row α).card = 4)
    (hHdecomp : H = {{a, p}, {p, q}, {q, b}, X, Y} ∪ Z)
    (hqX : q ∉ X) (hqY : q ∈ Y)
    (hpZ : ∀ R ∈ Z, p ∉ R) (hqZ : ∀ R ∈ Z, q ∉ R) :
    pairSide H q p = minimize (insert {a} (insert (X.erase p) Z)) := by
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hEraseAP : ({a, p} : Row α).erase p = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxp, hxa | hxp'⟩
      · exact hxa
      · exact (hxp hxp').elim
    · intro hxa
      subst x
      exact ⟨hap, Or.inl rfl⟩
  have hSource :
      deletePoint (avoidPoint H q) p = insert {a} (insert (X.erase p) Z) := by
    ext T
    constructor
    · intro hT
      obtain ⟨R, hRAvoid, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨hRH, hqR⟩ := mem_avoidPoint.mp hRAvoid
      rw [hHdecomp] at hRH
      rcases Finset.mem_union.mp hRH with hRFixed | hRZ
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hRFixed
        rcases hRFixed with rfl | rfl | rfl | rfl | rfl
        · simp [hEraseAP]
        · exact (hqR (by simp)).elim
        · exact (hqR (by simp)).elim
        · simp
        · exact (hqR hqY).elim
      · have hpR := hpZ R hRZ
        simp [Finset.erase_eq_of_notMem hpR, hRZ]
    · intro hT
      simp only [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · apply Finset.mem_image.mpr
        refine ⟨{a, p}, mem_avoidPoint.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [hHdecomp]
          simp
        · simp [haq.symm, hpq.symm]
        · exact hEraseAP
      · rcases hT with rfl | hTZ
        · apply Finset.mem_image.mpr
          refine ⟨X, mem_avoidPoint.mpr ⟨?_, hqX⟩, rfl⟩
          rw [hHdecomp]
          simp
        · apply Finset.mem_image.mpr
          refine ⟨T, mem_avoidPoint.mpr ⟨?_, hqZ T hTZ⟩, ?_⟩
          · rw [hHdecomp]
            exact Finset.mem_union_right _ hTZ
          · exact Finset.erase_eq_of_notMem (hpZ T hTZ)
  rw [pairSide, residual, hSource]

theorem p4_pairGraph_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hHRows : RowsCardAtLeast H 2)
    (hHdegree : MaxDegreeAtMost H 3)
    (hDualCard : (blocker H).card = 5)
    (hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphP4 H) :
    False := by
  obtain ⟨a, p, q, b, hDistinct, hPairs, hpDegree, hqDegree,
      hSidePCard, hSideQCard⟩ :=
    p4_central_structure hH hHcard hHRows hHdegree hDualCard
      hDualRows hDualDegree hShape
  obtain ⟨hap, haq, hab, hpq, hpb, hqb⟩ :=
    pairwise_ne_of_quad_card_eq_four hDistinct
  have hAP : ({a, p} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hPQ : ({p, q} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hQB : ({q, b} : Row α) ∈ H :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  obtain ⟨X, Y, Z, hXH, hYH, hpX, hqX, hpY, hqY,
      hXcard, hYcard, hXY, -, hZcard, hZClutter, hZRows,
      hpZ, hqZ, hHdecomp⟩ :=
    p4_central_row_decomposition hH hHcard hHRows hDistinct hPairs
      hpDegree hqDegree
  have hYEraseCard : 2 ≤ (Y.erase q).card := by
    rw [Finset.card_erase_of_mem hqY]
    omega
  have hXEraseCard : 2 ≤ (X.erase p).card := by
    rw [Finset.card_erase_of_mem hpX]
    omega
  have hSidePForm :=
    p4_pairSide_left_normal_form hDistinct hHdecomp hpX hpY hpZ hqZ
  have hSideQForm :=
    p4_pairSide_right_normal_form hDistinct hHdecomp hqX hqY hpZ hqZ
  obtain ⟨c, d, hcd, hYErase, hTraceC⟩ :=
    two_blocker_trace_normal_form hZRows hYEraseCard hSidePForm hSidePCard
  obtain ⟨e, f, hef, hXErase, hTraceE⟩ :=
    two_blocker_trace_normal_form hZRows hXEraseCard hSideQForm hSideQCard
  let C : Row α := {c, d}
  let E : Row α := {e, f}
  have hCcard : C.card = 2 := by simp [C, hcd]
  have hEcard : E.card = 2 := by simp [E, hef]
  have hYForm : Y = insert q C := by
    calc
      Y = insert q (Y.erase q) := (Finset.insert_erase hqY).symm
      _ = insert q C := by rw [hYErase]
  have hXForm : X = insert p E := by
    calc
      X = insert p (X.erase p) := (Finset.insert_erase hpX).symm
      _ = insert p E := by rw [hXErase]
  have haE : a ∉ E := by
    intro haE
    have hSubset : ({a, p} : Row α) ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hXForm]
        simp [haE]
      · exact hpX
    have hEq : ({a, p} : Row α) = X := hH hAP hXH hSubset
    have hCardEq := congrArg Finset.card hEq
    have hAPcard : ({a, p} : Row α).card = 2 := by simp [hap]
    omega
  have hbC : b ∉ C := by
    intro hbC
    have hSubset : ({q, b} : Row α) ⊆ Y := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hqY
      · rw [hYForm]
        simp [hbC]
    have hEq : ({q, b} : Row α) = Y := hH hQB hYH hSubset
    have hCardEq := congrArg Finset.card hEq
    have hQBcard : ({q, b} : Row α).card = 2 := by simp [hqb]
    omega
  have hTraceC' : ∀ R ∈ Z, b ∈ R ∨ C ⊆ R := by
    simpa [C] using hTraceC
  have hTraceE' : ∀ R ∈ Z, a ∈ R ∨ E ⊆ R := by
    simpa [E] using hTraceE
  have hZH : Z ⊆ H := by
    intro R hRZ
    rw [hHdecomp]
    exact Finset.mem_union_right _ hRZ
  have hYNotZ : Y ∉ Z := by
    intro hYZ
    exact hqZ Y hYZ hqY
  have hXNotZ : X ∉ Z := by
    intro hXZ
    exact hpZ X hXZ hpX
  have hAPcard : ({a, p} : Row α).card = 2 := by simp [hap]
  have hQBcard : ({q, b} : Row α).card = 2 := by simp [hqb]
  have hAPneX : ({a, p} : Row α) ≠ X := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hAPneY : ({a, p} : Row α) ≠ Y := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hQBneX : ({q, b} : Row α) ≠ X := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hQBneY : ({q, b} : Row α) ≠ Y := by
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    omega
  have hAPneQB : ({a, p} : Row α) ≠ {q, b} := by
    intro hEq
    have hpQB : p ∈ ({q, b} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpQB
    rcases hpQB with hpq' | hpb'
    · exact hpq hpq'
    · exact hpb hpb'
  have hYNotRest : Y ∉ Z := hYNotZ
  have hXNotRest : X ∉ insert Y Z := by
    simp only [Finset.mem_insert]
    exact fun h ↦ h.elim hXY hXNotZ
  have hQBNotRest : ({q, b} : Row α) ∉ insert X (insert Y Z) := by
    simp only [Finset.mem_insert]
    exact fun h ↦ h.elim hQBneX (fun h' ↦ h'.elim hQBneY (fun hZ ↦ hqZ _ hZ (by simp)))
  have hAPNotRest : ({a, p} : Row α) ∉
      insert {q, b} (insert X (insert Y Z)) := by
    simp only [Finset.mem_insert]
    exact fun h ↦ h.elim hAPneQB
      (fun h' ↦ h'.elim hAPneX (fun h'' ↦ h''.elim hAPneY
        (fun hZ ↦ hpZ _ hZ (by simp))))
  let F : Hypergraph α := insert {a, p} (insert {q, b} (insert X (insert Y Z)))
  have hFH : F ⊆ H := by
    intro R hRF
    simp only [F, Finset.mem_insert] at hRF
    rcases hRF with rfl | rfl | rfl | rfl | hRZ
    · exact hAP
    · exact hQB
    · exact hXH
    · exact hYH
    · exact hZH hRZ
  have hBudget : ∀ x,
      degree Z x +
        (if x = a then 1 else 0) +
        (if x = b then 1 else 0) +
        (if x ∈ C then 1 else 0) +
        (if x ∈ E then 1 else 0) ≤ 3 := by
    intro x
    have hDegreeF : degree F x =
        degree Z x +
          (if x ∈ Y then 1 else 0) +
          (if x ∈ X then 1 else 0) +
          (if x ∈ ({q, b} : Row α) then 1 else 0) +
          (if x ∈ ({a, p} : Row α) then 1 else 0) := by
      rw [degree_insert_eq_add_indicator hAPNotRest,
        degree_insert_eq_add_indicator hQBNotRest,
        degree_insert_eq_add_indicator hXNotRest,
        degree_insert_eq_add_indicator hYNotRest]
    have haLe : (if x = a then 1 else 0) ≤
        (if x ∈ ({a, p} : Row α) then 1 else 0) := by
      by_cases hxa : x = a
      · subst x
        simp
      · simp [hxa]
    have hbLe : (if x = b then 1 else 0) ≤
        (if x ∈ ({q, b} : Row α) then 1 else 0) := by
      by_cases hxb : x = b
      · subst x
        simp
      · simp [hxb]
    have hCLe : (if x ∈ C then 1 else 0) ≤
        (if x ∈ Y then 1 else 0) := by
      by_cases hxC : x ∈ C
      · simp [hxC, hYForm]
      · simp [hxC]
    have hELe : (if x ∈ E then 1 else 0) ≤
        (if x ∈ X then 1 else 0) := by
      by_cases hxE : x ∈ E
      · simp [hxE, hXForm]
      · simp [hxE]
    have hDegreeUpper : degree F x ≤ 3 :=
      (degree_mono hFH x).trans (hHdegree x)
    omega
  obtain ⟨S, T, hSZ, hTZ, hST, hSGood, hTGood⟩ :=
    generalized_trace_two_good hZClutter hZcard hZRows hCcard hEcard
      hab haE hbC hTraceC' hTraceE' hBudget
  have hSLift : insert p (insert q S) ∈ blocker H :=
    p4_good_blocker_lift hDistinct hHdecomp hXForm hYForm hqX hpY
      hpZ hqZ hSZ hSGood
  have hTLift : insert p (insert q T) ∈ blocker H :=
    p4_good_blocker_lift hDistinct hHdecomp hXForm hYForm hqX hpY
      hpZ hqZ hTZ hTGood
  have hpS : p ∉ S := (mem_blocker.mp hSZ).avoids_inactive hpZ
  have hqS : q ∉ S := (mem_blocker.mp hSZ).avoids_inactive hqZ
  have hpT : p ∉ T := (mem_blocker.mp hTZ).avoids_inactive hpZ
  have hqT : q ∉ T := (mem_blocker.mp hTZ).avoids_inactive hqZ
  have hLiftNe : insert p (insert q S) ≠ insert p (insert q T) := by
    intro hEq
    have hErase := congrArg (fun R : Row α ↦ (R.erase p).erase q) hEq
    apply hST
    simpa [hpq, hpS, hqS, hpT, hqT] using hErase
  let Cboth : Hypergraph α := {insert p (insert q S), insert p (insert q T)}
  have hCbothCard : Cboth.card = 2 := by simp [Cboth, hLiftNe]
  have hCbothSubset : Cboth ⊆ blocker H := by
    intro U hU
    simp only [Cboth, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl
    · exact hSLift
    · exact hTLift
  have hCbothBoth : ∀ U ∈ Cboth, p ∈ U ∧ q ∈ U := by
    intro U hU
    simp only [Cboth, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl <;> simp
  have hCount := pairSide_blocker_card_add_both_le hpq hPQ
    hCbothSubset hCbothBoth
  rw [hSidePCard, hSideQCard, hCbothCard, hDualCard] at hCount
  omega

end AiMathLab.P0054.G413
