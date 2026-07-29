import AiMathLab.P0054G413.PairGraphs.ThreeK2
import Mathlib.Tactic.FinCases

namespace AiMathLab.P0054.G413

def fiveRowAt {α : Type*}
    (R0 R1 R2 R3 R4 : Row α) (i : Fin 5) : Row α :=
  if i = 0 then R0
  else if i = 1 then R1
  else if i = 2 then R2
  else if i = 3 then R3
  else R4

def fiveRowSupport {α : Type*} [DecidableEq α]
    (R0 R1 R2 R3 R4 : Row α) (x : α) : FiveSupport :=
  Finset.univ.filter fun i ↦ x ∈ fiveRowAt R0 R1 R2 R3 R4 i

theorem fiveRowAt_mem {α : Type*} [DecidableEq α]
    (R0 R1 R2 R3 R4 : Row α) (i : Fin 5) :
    fiveRowAt R0 R1 R2 R3 R4 i ∈
      ({R0, R1, R2, R3, R4} : Hypergraph α) := by
  fin_cases i <;> simp [fiveRowAt]

theorem fiveRowSupport_card_eq_degree {α : Type*} [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (x : α) :
    (fiveRowSupport R0 R1 R2 R3 R4 x).card =
      degree {R0, R1, R2, R3, R4} x := by
  let rowAt := fiveRowAt R0 R1 R2 R3 R4
  have hImage : Finset.univ.image rowAt = {R0, R1, R2, R3, R4} := by
    ext E
    constructor
    · intro hE
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE
      fin_cases i <;> simp [rowAt, fiveRowAt]
    · intro hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp [rowAt, fiveRowAt]⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp [rowAt, fiveRowAt]⟩
      · exact Finset.mem_image.mpr ⟨2, by simp, by simp [rowAt, fiveRowAt]⟩
      · exact Finset.mem_image.mpr ⟨3, by simp, by simp [rowAt, fiveRowAt]⟩
      · exact Finset.mem_image.mpr ⟨4, by simp, by simp [rowAt, fiveRowAt]⟩
  have hImageCard :
      (Finset.univ.image rowAt).card = (Finset.univ : Finset (Fin 5)).card := by
    rw [hImage, hRowsCard]
    decide
  have hInj : Set.InjOn rowAt (Finset.univ : Finset (Fin 5)) :=
    Finset.card_image_iff.mp hImageCard
  have hFilterImage :
      ((Finset.univ.filter fun i ↦ x ∈ rowAt i).image rowAt) =
        (({R0, R1, R2, R3, R4} : Hypergraph α).filter fun E ↦ x ∈ E) := by
    ext E
    constructor
    · intro hE
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨-, hxi⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨by rw [← hImage]; simp, hxi⟩
    · intro hE
      obtain ⟨hERows, hxE⟩ := Finset.mem_filter.mp hE
      rw [← hImage] at hERows
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hERows
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨by simp, hxE⟩, rfl⟩
  rw [fiveRowSupport, degree]
  rw [← Finset.card_image_iff.mpr (hInj.mono (Finset.filter_subset _ _)), hFilterImage]

theorem validFiveSupportPair_of_pair_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {x y : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hPair : ({x, y} : Row α) ∈
      blocker ({R0, R1, R2, R3, R4} : Hypergraph α))
    (hxy : x ≠ y) :
    IsValidFiveSupportPair
      (fiveRowSupport R0 R1 R2 R3 R4 x,
        fiveRowSupport R0 R1 R2 R3 R4 y) := by
  let X := fiveRowSupport R0 R1 R2 R3 R4 x
  let Y := fiveRowSupport R0 R1 R2 R3 R4 y
  have hUnion : X ∪ Y = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    obtain ⟨z, hzPair, hzRow⟩ :=
      (mem_blocker.mp hPair).prop
        (fiveRowAt R0 R1 R2 R3 R4 i) (fiveRowAt_mem R0 R1 R2 R3 R4 i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with rfl | rfl
    · exact Or.inl (by simpa [X, fiveRowSupport] using hzRow)
    · exact Or.inr (by simpa [Y, fiveRowSupport] using hzRow)
  have hXCard : X.card ≤ 3 := by
    change (fiveRowSupport R0 R1 R2 R3 R4 x).card ≤ 3
    rw [fiveRowSupport_card_eq_degree hRowsCard]
    exact hDegree x
  have hYCard : Y.card ≤ 3 := by
    change (fiveRowSupport R0 R1 R2 R3 R4 y).card ≤ 3
    rw [fiveRowSupport_card_eq_degree hRowsCard]
    exact hDegree y
  obtain ⟨hXPrivate, hYPrivate⟩ := pair_blocker_support_private hPair hxy
  have exists_index_of_mem (E : Row α)
      (hE : E ∈ ({R0, R1, R2, R3, R4} : Hypergraph α)) :
      ∃ i : Fin 5, E = fiveRowAt R0 R1 R2 R3 R4 i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [fiveRowAt]⟩
    · exact ⟨1, by simp [fiveRowAt]⟩
    · exact ⟨2, by simp [fiveRowAt]⟩
    · exact ⟨3, by simp [fiveRowAt]⟩
    · exact ⟨4, by simp [fiveRowAt]⟩
  have hXDiff : X \ Y ≠ ∅ := by
    intro hEmpty
    obtain ⟨E, hE⟩ := hXPrivate
    obtain ⟨hEX, hEY⟩ := Finset.mem_sdiff.mp hE
    obtain ⟨hERows, hxE⟩ := mem_pointSupport.mp hEX
    obtain ⟨i, rfl⟩ := exists_index_of_mem E hERows
    have hi : i ∈ X \ Y := by
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa [X, fiveRowSupport] using hxE
      · intro hiY
        apply hEY
        exact mem_pointSupport.mpr
          ⟨fiveRowAt_mem R0 R1 R2 R3 R4 i,
            by simpa [Y, fiveRowSupport] using hiY⟩
    rw [hEmpty] at hi
    simp at hi
  have hYDiff : Y \ X ≠ ∅ := by
    intro hEmpty
    obtain ⟨E, hE⟩ := hYPrivate
    obtain ⟨hEY, hEX⟩ := Finset.mem_sdiff.mp hE
    obtain ⟨hERows, hyE⟩ := mem_pointSupport.mp hEY
    obtain ⟨i, rfl⟩ := exists_index_of_mem E hERows
    have hi : i ∈ Y \ X := by
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa [Y, fiveRowSupport] using hyE
      · intro hiX
        apply hEX
        exact mem_pointSupport.mpr
          ⟨fiveRowAt_mem R0 R1 R2 R3 R4 i,
            by simpa [X, fiveRowSupport] using hiX⟩
    rw [hEmpty] at hi
    simp at hi
  exact ⟨hUnion, hXCard, hYCard, hXDiff, hYDiff⟩

theorem fiveRowSupport_union_ne_univ_of_not_pairRow {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {x y : α}
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hNotPair : ({x, y} : Row α) ∉
      pairRows (blocker ({R0, R1, R2, R3, R4} : Hypergraph α))) :
    fiveRowSupport R0 R1 R2 R3 R4 x ∪
      fiveRowSupport R0 R1 R2 R3 R4 y ≠ Finset.univ := by
  intro hUnion
  have hNotBlocker : ({x, y} : Row α) ∉
      blocker ({R0, R1, R2, R3, R4} : Hypergraph α) := by
    intro hPair
    apply hNotPair
    exact Finset.mem_filter.mpr ⟨hPair, by
      have hLower := hBRows {x, y} hPair
      have hUpper : ({x, y} : Row α).card ≤ 2 := Finset.card_le_two
      omega⟩
  obtain ⟨E, hERows, hxE, hyE⟩ :=
    exists_row_avoiding_nonblocker_pair hBRows hNotBlocker
  have exists_index_of_mem (F : Row α)
      (hF : F ∈ ({R0, R1, R2, R3, R4} : Hypergraph α)) :
      ∃ i : Fin 5, F = fiveRowAt R0 R1 R2 R3 R4 i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [fiveRowAt]⟩
    · exact ⟨1, by simp [fiveRowAt]⟩
    · exact ⟨2, by simp [fiveRowAt]⟩
    · exact ⟨3, by simp [fiveRowAt]⟩
    · exact ⟨4, by simp [fiveRowAt]⟩
  obtain ⟨i, rfl⟩ := exists_index_of_mem E hERows
  have hi : i ∈ fiveRowSupport R0 R1 R2 R3 R4 x ∪
      fiveRowSupport R0 R1 R2 R3 R4 y := by
    rw [hUnion]
    simp
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hxE (by simpa [fiveRowSupport] using hi)
  · exact hyE (by simpa [fiveRowSupport] using hi)

theorem three_point_transversal_iff_five_support_union {α : Type*}
    [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {x y z : α} :
    IsTransversal ({R0, R1, R2, R3, R4} : Hypergraph α) {x, y, z} ↔
      fiveRowSupport R0 R1 R2 R3 R4 x ∪
        fiveRowSupport R0 R1 R2 R3 R4 y ∪
          fiveRowSupport R0 R1 R2 R3 R4 z = Finset.univ := by
  constructor
  · intro hTransversal
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    obtain ⟨w, hwTriple, hwRow⟩ :=
      hTransversal (fiveRowAt R0 R1 R2 R3 R4 i)
        (fiveRowAt_mem R0 R1 R2 R3 R4 i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple
    rcases hwTriple with rfl | rfl | rfl
    · exact Or.inl (Or.inl (by simpa [fiveRowSupport] using hwRow))
    · exact Or.inl (Or.inr (by simpa [fiveRowSupport] using hwRow))
    · exact Or.inr (by simpa [fiveRowSupport] using hwRow)
  · intro hUnion E hERows
    have exists_index_of_mem (F : Row α)
        (hF : F ∈ ({R0, R1, R2, R3, R4} : Hypergraph α)) :
        ∃ i : Fin 5, F = fiveRowAt R0 R1 R2 R3 R4 i := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [fiveRowAt]⟩
      · exact ⟨1, by simp [fiveRowAt]⟩
      · exact ⟨2, by simp [fiveRowAt]⟩
      · exact ⟨3, by simp [fiveRowAt]⟩
      · exact ⟨4, by simp [fiveRowAt]⟩
    obtain ⟨i, rfl⟩ := exists_index_of_mem E hERows
    have hi : i ∈ fiveRowSupport R0 R1 R2 R3 R4 x ∪
        fiveRowSupport R0 R1 R2 R3 R4 y ∪
          fiveRowSupport R0 R1 R2 R3 R4 z := by
      rw [hUnion]
      simp
    rcases Finset.mem_union.mp hi with hxy | hz
    · rcases Finset.mem_union.mp hxy with hx | hy
      · exact ⟨x, by simp, by simpa [fiveRowSupport] using hx⟩
      · exact ⟨y, by simp, by simpa [fiveRowSupport] using hy⟩
    · exact ⟨z, by simp, by simpa [fiveRowSupport] using hz⟩

def threeK2GoodOfSixSupports
    (A B C D E F : FiveSupport) : Finset BoolCube :=
  Finset.univ.filter fun q ↦
    (if q.1 then A else B) ∪
      (if q.2.1 then C else D) ∪
        (if q.2.2 then E else F) = Finset.univ

noncomputable def threeK2CubeTransversalCodes {α : Type*}
    [Fintype α] [DecidableEq α]
    (K : Hypergraph α) (a b c d e f : α) : Finset BoolCube := by
  classical
  exact Finset.univ.filter fun q ↦
    IsTransversal K (threeK2Decode a b c d e f q)

theorem threeK2CubeTransversalCodes_eq_support_good {α : Type*}
    [Fintype α] [DecidableEq α]
    (R0 R1 R2 R3 R4 : Row α) (a b c d e f : α) :
    threeK2CubeTransversalCodes
        ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f =
      threeK2GoodOfSixSupports
        (fiveRowSupport R0 R1 R2 R3 R4 a)
        (fiveRowSupport R0 R1 R2 R3 R4 b)
        (fiveRowSupport R0 R1 R2 R3 R4 c)
        (fiveRowSupport R0 R1 R2 R3 R4 d)
        (fiveRowSupport R0 R1 R2 R3 R4 e)
        (fiveRowSupport R0 R1 R2 R3 R4 f) := by
  ext q
  rcases q with ⟨p, q, r⟩
  cases p <;> cases q <;> cases r <;>
    simp [threeK2CubeTransversalCodes, threeK2GoodOfSixSupports,
      threeK2Decode, three_point_transversal_iff_five_support_union]

theorem threeK2CubeTransversalCodes_card_eq {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6) :
    (threeK2CubeTransversalCodes K a b c d e f).card =
      (threeK2TransversalTriples K a b c d e f).card := by
  classical
  let decode : BoolCube → Row α := threeK2Decode a b c d e f
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  have hca := Ne.symm hac
  have hea := Ne.symm hae
  have hcb := Ne.symm hbc
  have heb := Ne.symm hbe
  have hec := Ne.symm hce
  have hed := Ne.symm hde
  have hCodeDecode (q : BoolCube) :
      threeK2Code a c e (decode q) = q := by
    rcases q with ⟨q0, q1, q2⟩
    cases q0 <;> cases q1 <;> cases q2 <;>
      simp [decode, threeK2Decode, threeK2Code, hab, hac, had, hae, haf,
        hca, hcb, hcd, hce, hcf, hea, heb, hec, hed, hef]
  have hDecodeInjective : Function.Injective decode := by
    intro p q hpq
    rw [← hCodeDecode p, ← hCodeDecode q, hpq]
  have hImage :
      (threeK2CubeTransversalCodes K a b c d e f).image decode =
        threeK2TransversalTriples K a b c d e f := by
    ext T
    constructor
    · intro hT
      obtain ⟨q, hqGood, rfl⟩ := Finset.mem_image.mp hT
      have hqTransversal : IsTransversal K (decode q) :=
        (Finset.mem_filter.mp hqGood).2
      have hqEndpoint : decode q ∈ threeK2EndpointTriples a b c d e f := by
        rcases q with ⟨p, q, r⟩
        cases p <;> cases q <;> cases r <;>
          simp [decode, threeK2Decode, threeK2EndpointTriples]
      exact Finset.mem_filter.mpr ⟨hqEndpoint, hqTransversal⟩
    · intro hT
      obtain ⟨hTEndpoint, hTTransversal⟩ := Finset.mem_filter.mp hT
      simp only [threeK2EndpointTriples, Finset.mem_insert,
        Finset.mem_singleton] at hTEndpoint
      rcases hTEndpoint with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        apply Finset.mem_image.mpr
        first
        | exact ⟨(true, true, true), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(true, true, false), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(true, false, true), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(true, false, false), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(false, true, true), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(false, true, false), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(false, false, true), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
        | exact ⟨(false, false, false), Finset.mem_filter.mpr ⟨by simp,
            by simpa [decode, threeK2Decode] using hTTransversal⟩,
            by simp [decode, threeK2Decode]⟩
  rw [← hImage]
  exact (Finset.card_image_iff.mpr hDecodeInjective.injOn).symm

private theorem pair_ne_of_left_not_mem {α : Type*} [DecidableEq α]
    {x y : α} {U : Row α} (hxU : x ∉ U) :
    ({x, y} : Row α) ≠ U := by
  intro hEq
  exact hxU (hEq ▸ (by simp))

private theorem pair_ne_of_right_not_mem {α : Type*} [DecidableEq α]
    {x y : α} {U : Row α} (hyU : y ∉ U) :
    ({x, y} : Row α) ≠ U := by
  intro hEq
  exact hyU (hEq ▸ (by simp))

private theorem pair_ne_of_one_not_mem {α : Type*} [DecidableEq α]
    {x y : α} {U : Row α} (h : x ∉ U ∨ y ∉ U) :
    ({x, y} : Row α) ≠ U := by
  rcases h with hxU | hyU
  · exact pair_ne_of_left_not_mem hxU
  · exact pair_ne_of_right_not_mem hyU

private theorem threeK2_first_second_not_fixed {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (p q : Bool) :
    ({if p then a else b, if q then c else d} : Row α) ∉
      ({{a, b}, {c, d}, {e, f}} : Hypergraph α) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  cases p <;> cases q
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    all_goals exact pair_ne_of_one_not_mem (by simp_all [eq_comm])

private theorem threeK2_first_third_not_fixed {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (p q : Bool) :
    ({if p then a else b, if q then e else f} : Row α) ∉
      ({{a, b}, {c, d}, {e, f}} : Hypergraph α) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  cases p <;> cases q
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    all_goals exact pair_ne_of_one_not_mem (by simp_all [eq_comm])

private theorem threeK2_second_third_not_fixed {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (p q : Bool) :
    ({if p then c else d, if q then e else f} : Row α) ∉
      ({{a, b}, {c, d}, {e, f}} : Hypergraph α) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  cases p <;> cases q
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    all_goals exact pair_ne_of_one_not_mem (by simp_all [eq_comm])

theorem threeK2_actual_support_classification {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α}
    {a b c d e f : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hPairs : pairRows (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
      {{a, b}, {c, d}, {e, f}}) :
    let P : ValidFiveSupportPair :=
      ⟨(fiveRowSupport R0 R1 R2 R3 R4 a,
          fiveRowSupport R0 R1 R2 R3 R4 b), by
        exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
          (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
          (pairwise_ne_of_sext_card_eq_six hVertices).1⟩
    let Q : ValidFiveSupportPair :=
      ⟨(fiveRowSupport R0 R1 R2 R3 R4 c,
          fiveRowSupport R0 R1 R2 R3 R4 d), by
        exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
          (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
          (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.1⟩
    let S : ValidFiveSupportPair :=
      ⟨(fiveRowSupport R0 R1 R2 R3 R4 e,
          fiveRowSupport R0 R1 R2 R3 R4 f), by
        exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
          (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
          (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    ((threeK2TransversalTriples
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 4 →
        HasThreeK2RowWitness P Q S) ∧
      ((threeK2TransversalTriples
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 3 →
        IsThreeK2AsymmetricSupportSystem P Q S) := by
  dsimp only
  let P : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 a,
        fiveRowSupport R0 R1 R2 R3 R4 b), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).1⟩
  let Q : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 c,
        fiveRowSupport R0 R1 R2 R3 R4 d), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.1⟩
  let S : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 e,
        fiveRowSupport R0 R1 R2 R3 R4 f), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hCompatible : ThreeK2FiveSupportsCompatible P Q S := by
    intro p q
    have hPQ := fiveRowSupport_union_ne_univ_of_not_pairRow hBRows
      (hPairs ▸ threeK2_first_second_not_fixed hVertices p q)
    have hPS := fiveRowSupport_union_ne_univ_of_not_pairRow hBRows
      (hPairs ▸ threeK2_first_third_not_fixed hVertices p q)
    have hQS := fiveRowSupport_union_ne_univ_of_not_pairRow hBRows
      (hPairs ▸ threeK2_second_third_not_fixed hVertices p q)
    cases p <;> cases q <;>
      simpa [P, Q, S, selectFiveSupport] using And.intro hPQ (And.intro hPS hQS)
  have hGoodEq :
      threeK2CubeTransversalCodes
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f =
        threeK2FiniteGood P Q S := by
    simpa [P, Q, S, threeK2FiniteGood, threeK2GoodOfSixSupports,
      selectFiveSupport] using
      threeK2CubeTransversalCodes_eq_support_good R0 R1 R2 R3 R4 a b c d e f
  have hCardEq :
      (threeK2TransversalTriples
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card =
        (threeK2FiniteGood P Q S).card := by
    rw [← hGoodEq]
    exact (threeK2CubeTransversalCodes_card_eq hVertices).symm
  change
    ((threeK2TransversalTriples
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 4 →
        HasThreeK2RowWitness P Q S) ∧
      ((threeK2TransversalTriples
          ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 3 →
        IsThreeK2AsymmetricSupportSystem P Q S)
  constructor
  · intro hGood
    apply threeK2_finite_four_good_has_row_witness P Q S hCompatible
    omega
  · intro hGood
    apply threeK2_finite_three_good_asymmetric P Q S hCompatible
    omega

def threeK2EndpointChoice {α : Type*}
    (a b c d e f : α) (x : Fin 3 × Bool) : α :=
  match x.1 with
  | 0 => if x.2 then a else b
  | 1 => if x.2 then c else d
  | 2 => if x.2 then e else f

theorem threeK2_endpointChoice_ne_of_group_ne {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    {x y : Fin 3 × Bool} (hGroup : x.1 ≠ y.1) :
    threeK2EndpointChoice a b c d e f x ≠
      threeK2EndpointChoice a b c d e f y := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  rcases x with ⟨i, p⟩
  rcases y with ⟨j, q⟩
  fin_cases i <;> fin_cases j <;> cases p <;> cases q <;>
    simp_all [threeK2EndpointChoice, eq_comm]

theorem threeK2_endpointChoice_pair_not_fixed {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    {x y : Fin 3 × Bool} (hGroup : x.1 ≠ y.1) :
    ({threeK2EndpointChoice a b c d e f x,
        threeK2EndpointChoice a b c d e f y} : Row α) ∉
      ({{a, b}, {c, d}, {e, f}} : Hypergraph α) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  rcases x with ⟨i, p⟩
  rcases y with ⟨j, q⟩
  fin_cases i <;> fin_cases j <;> cases p <;> cases q
  all_goals
    simp_all only [threeK2EndpointChoice]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    all_goals exact pair_ne_of_one_not_mem (by simp_all [eq_comm])

theorem threeK2_actual_four_good_row_witness {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hPairs : pairRows (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
      {{a, b}, {c, d}, {e, f}})
    (hGood : (threeK2TransversalTriples
      ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 4) :
    ∃ i : Fin 5, ∃ x y : Fin 3 × Bool,
      x.1 ≠ y.1 ∧
        fiveRowSupport R0 R1 R2 R3 R4
            (threeK2EndpointChoice a b c d e f x) ∪
          fiveRowSupport R0 R1 R2 R3 R4
            (threeK2EndpointChoice a b c d e f y) = Finset.univ.erase i := by
  have hWitness :=
    (threeK2_actual_support_classification hRowsCard hVertices hKDegree
      hBRows hPairs).1 hGood
  obtain ⟨i, x, y, hGroup, hUnion⟩ := hWitness
  refine ⟨i, x, y, hGroup, ?_⟩
  rcases x with ⟨j, p⟩
  rcases y with ⟨k, q⟩
  fin_cases j <;> fin_cases k <;> cases p <;> cases q <;>
    simpa [threeK2EndpointChoice, selectFiveSupport] using hUnion

theorem threeK2_degrees_of_four_good {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hGoodCard : (threeK2TransversalTriples K a b c d e f).card = 4) :
    let Good := threeK2TransversalTriples K a b c d e f
    (degree Good a = 2 ∧ degree Good b = 2 ∧
      degree Good c = 2 ∧ degree Good d = 2 ∧
      degree Good e = 2 ∧ degree Good f = 2) ∧
    (degree (blocker K) a = 3 ∧ degree (blocker K) b = 3 ∧
      degree (blocker K) c = 3 ∧ degree (blocker K) d = 3 ∧
      degree (blocker K) e = 3 ∧ degree (blocker K) f = 3) := by
  classical
  let Good := threeK2TransversalTriples K a b c d e f
  have hGoodEndpoint : Good ⊆ threeK2EndpointTriples a b c d e f := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hGoodBlocker : Good ⊆ blocker K :=
    threeK2_transversal_triples_subset_blocker hVertices hBRows hPairs
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hda := Ne.symm had
  have hea := Ne.symm hae
  have hfa := Ne.symm haf
  have hcb := Ne.symm hbc
  have hdb := Ne.symm hbd
  have heb := Ne.symm hbe
  have hfb := Ne.symm hbf
  have hdc := Ne.symm hcd
  have hec := Ne.symm hce
  have hfc := Ne.symm hcf
  have hed := Ne.symm hde
  have hfd := Ne.symm hdf
  have hfe := Ne.symm hef
  have hAB : ({a, b} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hCD : ({c, d} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hEF : ({e, f} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have pair_not_good (x y : α) (hxy : x ≠ y) : ({x, y} : Row α) ∉ Good := by
    intro hPairGood
    have hPairEndpoint := hGoodEndpoint hPairGood
    have hTripleCard := threeK2_endpoint_triple_card hVertices hPairEndpoint
    have hPairCard : ({x, y} : Row α).card = 2 := by simp [hxy]
    omega
  have pair_endpoint_degree_le_two (x y : α) (hxy : x ≠ y)
      (hPair : ({x, y} : Row α) ∈ blocker K) :
      degree Good x ≤ 2 ∧ degree Good y ≤ 2 := by
    have hPairNotGood := pair_not_good x y hxy
    have hInsertSubset : insert ({x, y} : Row α) Good ⊆ blocker K :=
      Finset.insert_subset hPair hGoodBlocker
    have hxInsert : degree (insert ({x, y} : Row α) Good) x =
        degree Good x + 1 :=
      degree_insert_of_notMem hPairNotGood (by simp)
    have hyInsert : degree (insert ({x, y} : Row α) Good) y =
        degree Good y + 1 :=
      degree_insert_of_notMem hPairNotGood (by simp)
    have hxMono := degree_mono hInsertSubset x
    have hyMono := degree_mono hInsertSubset y
    have hxUpper := hBDegree x
    have hyUpper := hBDegree y
    omega
  obtain ⟨haUpper, hbUpper⟩ := pair_endpoint_degree_le_two a b hab hAB
  obtain ⟨hcUpper, hdUpper⟩ := pair_endpoint_degree_le_two c d hcd hCD
  obtain ⟨heUpper, hfUpper⟩ := pair_endpoint_degree_le_two e f hef hEF
  have hRowIncidence (T : Row α) (hTGood : T ∈ Good) :
      (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) +
        (if c ∈ T then 1 else 0) + (if d ∈ T then 1 else 0) +
        (if e ∈ T then 1 else 0) + (if f ∈ T then 1 else 0) = 3 := by
    have hTEndpoint := hGoodEndpoint hTGood
    simp only [threeK2EndpointTriples, Finset.mem_insert,
      Finset.mem_singleton] at hTEndpoint
    rcases hTEndpoint with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  have hIncidenceSum :
      3 * Good.card = degree Good a + degree Good b + degree Good c +
        degree Good d + degree Good e + degree Good f := by
    calc
      3 * Good.card = Finset.sum Good (fun _T ↦ 3) := by simp [Nat.mul_comm]
      _ = Finset.sum Good (fun T ↦
          (if a ∈ T then 1 else 0) + (if b ∈ T then 1 else 0) +
            (if c ∈ T then 1 else 0) + (if d ∈ T then 1 else 0) +
            (if e ∈ T then 1 else 0) + (if f ∈ T then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro T hT
        exact (hRowIncidence T hT).symm
      _ = degree Good a + degree Good b + degree Good c +
          degree Good d + degree Good e + degree Good f := by
        simp only [Finset.sum_add_distrib, sum_indicator_eq_degree]
  have hGoodCard' : Good.card = 4 := hGoodCard
  have haGood : degree Good a = 2 := by omega
  have hbGood : degree Good b = 2 := by omega
  have hcGood : degree Good c = 2 := by omega
  have hdGood : degree Good d = 2 := by omega
  have heGood : degree Good e = 2 := by omega
  have hfGood : degree Good f = 2 := by omega
  have endpoint_degree_eq_three (x y : α)
      (hPair : ({x, y} : Row α) ∈ blocker K)
      (hPairNotGood : ({x, y} : Row α) ∉ Good)
      (hxGood : degree Good x = 2) : degree (blocker K) x = 3 := by
    have hInsertSubset : insert ({x, y} : Row α) Good ⊆ blocker K :=
      Finset.insert_subset hPair hGoodBlocker
    have hxInsert : degree (insert ({x, y} : Row α) Good) x =
        degree Good x + 1 := degree_insert_of_notMem hPairNotGood (by simp)
    have hxMono := degree_mono hInsertSubset x
    have hxUpper := hBDegree x
    omega
  refine ⟨⟨haGood, hbGood, hcGood, hdGood, heGood, hfGood⟩, ?_⟩
  exact ⟨endpoint_degree_eq_three a b hAB (pair_not_good a b hab) haGood,
    endpoint_degree_eq_three b a (by simpa [Finset.pair_comm] using hAB)
      (by simpa [Finset.pair_comm] using pair_not_good a b hab) hbGood,
    endpoint_degree_eq_three c d hCD (pair_not_good c d hcd) hcGood,
    endpoint_degree_eq_three d c (by simpa [Finset.pair_comm] using hCD)
      (by simpa [Finset.pair_comm] using pair_not_good c d hcd) hdGood,
    endpoint_degree_eq_three e f hEF (pair_not_good e f hef) heGood,
    endpoint_degree_eq_three f e (by simpa [Finset.pair_comm] using hEF)
      (by simpa [Finset.pair_comm] using pair_not_good e f hef) hfGood⟩

private theorem degree_insert_of_point_not_mem {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {E : Row α} {x : α} (hxE : x ∉ E) :
    degree (insert E H) x = degree H x := by
  have hFilter :
      (insert E H).filter (fun A ↦ x ∈ A) = H.filter (fun A ↦ x ∈ A) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hAH, hxA⟩
      · exact (hxE hxA).elim
      · exact ⟨hAH, hxA⟩
    · rintro ⟨hAH, hxA⟩
      exact ⟨Or.inr hAH, hxA⟩
  rw [degree, degree, hFilter]

theorem exists_fiveRowAt_of_mem {α : Type*} [DecidableEq α]
    {R0 R1 R2 R3 R4 E : Row α}
    (hE : E ∈ ({R0, R1, R2, R3, R4} : Hypergraph α)) :
    ∃ i : Fin 5, E = fiveRowAt R0 R1 R2 R3 R4 i := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [fiveRowAt]⟩
  · exact ⟨1, by simp [fiveRowAt]⟩
  · exact ⟨2, by simp [fiveRowAt]⟩
  · exact ⟨3, by simp [fiveRowAt]⟩
  · exact ⟨4, by simp [fiveRowAt]⟩

theorem threeK2_endpointChoice_not_mem {α : Type*}
    {a b c d e f : α} {T : Row α}
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hd : d ∉ T) (he : e ∉ T) (hf : f ∉ T)
    (x : Fin 3 × Bool) :
    threeK2EndpointChoice a b c d e f x ∉ T := by
  rcases x with ⟨i, p⟩
  fin_cases i <;> cases p <;>
    simp only [threeK2EndpointChoice, if_true] <;> assumption

theorem threeK2_four_good_impossible_of_rows {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hBCard : (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)).card = 8)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hBDegree : MaxDegreeAtMost
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 3)
    (hPairs : pairRows (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
      {{a, b}, {c, d}, {e, f}})
    (hGoodCard : (threeK2TransversalTriples
      ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 4) :
    False := by
  classical
  let K : Hypergraph α := {R0, R1, R2, R3, R4}
  let Good := threeK2TransversalTriples K a b c d e f
  let AB : Row α := {a, b}
  let CD : Row α := {c, d}
  let EF : Row α := {e, f}
  let Base : Hypergraph α := insert AB (insert CD (insert EF Good))
  change K.card = 5 at hRowsCard
  change MaxDegreeAtMost K 3 at hKDegree
  change (blocker K).card = 8 at hBCard
  change RowsCardAtLeast (blocker K) 2 at hBRows
  change MaxDegreeAtMost (blocker K) 3 at hBDegree
  change pairRows (blocker K) = {{a, b}, {c, d}, {e, f}} at hPairs
  change Good.card = 4 at hGoodCard
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  have hAB : AB ∈ blocker K := by
    change ({a, b} : Row α) ∈ blocker K
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hCD : CD ∈ blocker K := by
    change ({c, d} : Row α) ∈ blocker K
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hEF : EF ∈ blocker K := by
    change ({e, f} : Row α) ∈ blocker K
    exact (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hGoodBlocker : Good ⊆ blocker K :=
    threeK2_transversal_triples_subset_blocker hVertices hBRows hPairs
  have hGoodEndpoint : Good ⊆ threeK2EndpointTriples a b c d e f := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have pair_not_good (x y : α) (hxy : x ≠ y) : ({x, y} : Row α) ∉ Good := by
    intro hPairGood
    have hTripleCard :=
      threeK2_endpoint_triple_card hVertices (hGoodEndpoint hPairGood)
    have hPairCard : ({x, y} : Row α).card = 2 := by simp [hxy]
    omega
  have hABNotGood : AB ∉ Good := by
    exact pair_not_good a b hab
  have hCDNotGood : CD ∉ Good := by
    exact pair_not_good c d hcd
  have hEFNotGood : EF ∉ Good := by
    exact pair_not_good e f hef
  have hABCD : AB ≠ CD := by
    exact pair_ne_of_left_not_mem (by simp [CD, hac, had])
  have hABEF : AB ≠ EF := by
    exact pair_ne_of_left_not_mem (by simp [EF, hae, haf])
  have hCDEF : CD ≠ EF := by
    exact pair_ne_of_left_not_mem (by simp [EF, hce, hcf])
  have hCDNotTail : CD ∉ insert EF Good := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hCDEF, hCDNotGood⟩
  have hABNotTail : AB ∉ insert CD (insert EF Good) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hABCD, hABEF, hABNotGood⟩
  have hBaseCard : Base.card = 7 := by
    change (insert AB (insert CD (insert EF Good))).card = 7
    rw [Finset.card_insert_of_notMem hABNotTail,
      Finset.card_insert_of_notMem hCDNotTail,
      Finset.card_insert_of_notMem hEFNotGood, hGoodCard]
  have hBaseSubset : Base ⊆ blocker K :=
    Finset.insert_subset hAB
      (Finset.insert_subset hCD (Finset.insert_subset hEF hGoodBlocker))
  obtain ⟨hGoodDegrees, -⟩ :=
    threeK2_degrees_of_four_good hVertices hBRows hBDegree hPairs hGoodCard
  obtain ⟨haGood, hbGood, hcGood, hdGood, heGood, hfGood⟩ := hGoodDegrees
  have haBase : degree Base a = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) a = 3
    rw [degree_insert_of_notMem hABNotTail (by simp [AB]),
      degree_insert_of_point_not_mem (by simp [CD, hac, had]),
      degree_insert_of_point_not_mem (by simp [EF, hae, haf]), haGood]
  have hbBase : degree Base b = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) b = 3
    rw [degree_insert_of_notMem hABNotTail (by simp [AB]),
      degree_insert_of_point_not_mem (by simp [CD, hbc, hbd]),
      degree_insert_of_point_not_mem (by simp [EF, hbe, hbf]), hbGood]
  have hcBase : degree Base c = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) c = 3
    rw [degree_insert_of_point_not_mem (by simp [AB, eq_comm, hac, hbc]),
      degree_insert_of_notMem hCDNotTail (by simp [CD]),
      degree_insert_of_point_not_mem (by simp [EF, hce, hcf]), hcGood]
  have hdBase : degree Base d = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) d = 3
    rw [degree_insert_of_point_not_mem (by simp [AB, eq_comm, had, hbd]),
      degree_insert_of_notMem hCDNotTail (by simp [CD]),
      degree_insert_of_point_not_mem (by simp [EF, hde, hdf]), hdGood]
  have heBase : degree Base e = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) e = 3
    rw [degree_insert_of_point_not_mem (by simp [AB, eq_comm, hae, hbe]),
      degree_insert_of_point_not_mem (by simp [CD, eq_comm, hce, hde]),
      degree_insert_of_notMem hEFNotGood (by simp [EF]), heGood]
  have hfBase : degree Base f = 3 := by
    change degree (insert AB (insert CD (insert EF Good))) f = 3
    rw [degree_insert_of_point_not_mem (by simp [AB, eq_comm, haf, hbf]),
      degree_insert_of_point_not_mem (by simp [CD, eq_comm, hcf, hdf]),
      degree_insert_of_notMem hEFNotGood (by simp [EF]), hfGood]
  have outside_avoids_endpoints {T : Row α}
      (hTBlocker : T ∈ blocker K) (hTNotBase : T ∉ Base) :
      a ∉ T ∧ b ∉ T ∧ c ∉ T ∧ d ∉ T ∧ e ∉ T ∧ f ∉ T := by
    have hInsertSubset : insert T Base ⊆ blocker K :=
      Finset.insert_subset hTBlocker hBaseSubset
    have avoid_endpoint (x : α) (hxBase : degree Base x = 3) : x ∉ T := by
      intro hxT
      have hxInsert : degree (insert T Base) x = degree Base x + 1 :=
        degree_insert_of_notMem hTNotBase hxT
      have hxMono := degree_mono hInsertSubset x
      have hxUpper := hBDegree x
      omega
    exact ⟨avoid_endpoint a haBase, avoid_endpoint b hbBase,
      avoid_endpoint c hcBase, avoid_endpoint d hdBase,
      avoid_endpoint e heBase, avoid_endpoint f hfBase⟩
  have hBaseLt : Base.card < (blocker K).card := by omega
  obtain ⟨T, hTBlocker, hTNotBase⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hBaseLt
  obtain ⟨haT, hbT, hcT, hdT, heT, hfT⟩ :=
    outside_avoids_endpoints hTBlocker hTNotBase
  obtain ⟨i, x, y, hGroup, hSupport⟩ :=
    threeK2_actual_four_good_row_witness hRowsCard hVertices hKDegree
      hBRows hPairs hGoodCard
  let u := threeK2EndpointChoice a b c d e f x
  let v := threeK2EndpointChoice a b c d e f y
  let R := fiveRowAt R0 R1 R2 R3 R4 i
  have huv : u ≠ v :=
    threeK2_endpointChoice_ne_of_group_ne hVertices hGroup
  have huT : u ∉ T :=
    threeK2_endpointChoice_not_mem haT hbT hcT hdT heT hfT x
  have hvT : v ∉ T :=
    threeK2_endpointChoice_not_mem haT hbT hcT hdT heT hfT y
  have hiAvoid : i ∉
      fiveRowSupport R0 R1 R2 R3 R4 u ∪
        fiveRowSupport R0 R1 R2 R3 R4 v := by
    rw [hSupport]
    simp
  have huR : u ∉ R := by
    intro hu
    apply hiAvoid
    exact Finset.mem_union_left _ (by simpa [fiveRowSupport, R] using hu)
  have hvR : v ∉ R := by
    intro hv
    apply hiAvoid
    exact Finset.mem_union_right _ (by simpa [fiveRowSupport, R] using hv)
  have hRK : R ∈ K := fiveRowAt_mem R0 R1 R2 R3 R4 i
  obtain ⟨z, hzT, hzR⟩ := (mem_blocker.mp hTBlocker).prop R hRK
  have hzu : z ≠ u := fun h ↦ huT (h ▸ hzT)
  have hzv : z ≠ v := fun h ↦ hvT (h ▸ hzT)
  have hTransversal : IsTransversal K {u, v, z} := by
    intro E hEK
    obtain ⟨j, rfl⟩ := exists_fiveRowAt_of_mem hEK
    by_cases hji : j = i
    · subst j
      exact ⟨z, by simp, hzR⟩
    · have hjSupport : j ∈
          fiveRowSupport R0 R1 R2 R3 R4 u ∪
            fiveRowSupport R0 R1 R2 R3 R4 v := by
        rw [hSupport]
        simp [hji]
      rcases Finset.mem_union.mp hjSupport with hu | hv
      · exact ⟨u, by simp, by simpa [fiveRowSupport] using hu⟩
      · exact ⟨v, by simp, by simpa [fiveRowSupport] using hv⟩
  obtain ⟨U, hUSubset, hUMinimal⟩ :=
    exists_minimalTransversal_subset hTransversal
  have hUBlocker : U ∈ blocker K := mem_blocker.mpr hUMinimal
  have hzU : z ∈ U := by
    obtain ⟨w, hwU, hwR⟩ := hUMinimal.prop R hRK
    have hwTriple := hUSubset hwU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple
    rcases hwTriple with hwu | hwv | hwz
    · exact (huR (hwu ▸ hwR)).elim
    · exact (hvR (hwv ▸ hwR)).elim
    · exact hwz ▸ hwU
  have huvU : u ∈ U ∨ v ∈ U := by
    by_contra h
    push Not at h
    have hUSingleton : U ⊆ {z} := by
      intro w hwU
      have hwTriple := hUSubset hwU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwTriple ⊢
      rcases hwTriple with hwu | hwv | hwz
      · exact (h.1 (hwu ▸ hwU)).elim
      · exact (h.2 (hwv ▸ hwU)).elim
      · exact hwz
    have hUUpper := Finset.card_le_card hUSingleton
    have hULower := hBRows U hUBlocker
    simp at hUUpper
    omega
  let V : Row α := {a, b, c, d, e, f}
  have hBaseEndpoint : ∀ W ∈ Base, W ⊆ V := by
    intro W hW
    simp only [Base, Finset.mem_insert] at hW
    rcases hW with rfl | rfl | rfl | hWGood
    · intro t ht
      simp only [AB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [V]
    · intro t ht
      simp only [CD, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [V]
    · intro t ht
      simp only [EF, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [V]
    · have hEndpoint := hGoodEndpoint hWGood
      simp only [threeK2EndpointTriples, Finset.mem_insert,
        Finset.mem_singleton] at hEndpoint
      rcases hEndpoint with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        intro t ht <;> simp only [Finset.mem_insert, Finset.mem_singleton] at ht <;>
        rcases ht with rfl | rfl | rfl <;> simp [V]
  have hzV : z ∉ V := by
    simp only [V, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ haT (h ▸ hzT), fun h ↦ hbT (h ▸ hzT),
      fun h ↦ hcT (h ▸ hzT), fun h ↦ hdT (h ▸ hzT),
      fun h ↦ heT (h ▸ hzT), fun h ↦ hfT (h ▸ hzT)⟩
  have hUNotBase : U ∉ Base := by
    intro hUBase
    exact hzV (hBaseEndpoint U hUBase hzU)
  obtain ⟨haU, hbU, hcU, hdU, heU, hfU⟩ :=
    outside_avoids_endpoints hUBlocker hUNotBase
  rcases huvU with huU | hvU
  · exact (threeK2_endpointChoice_not_mem haU hbU hcU hdU heU hfU x) huU
  · exact (threeK2_endpointChoice_not_mem haU hbU hcU hdU heU hfU y) hvU

def threeK2EndpointAt {α : Type*}
    (a b c d e f : α) (i : Fin 6) : α :=
  if i = 0 then a
  else if i = 1 then b
  else if i = 2 then c
  else if i = 3 then d
  else if i = 4 then e
  else f

def threeK2Embed {α : Type*}
    (a b c d e f x : α) (i : Fin 7) : α :=
  if hi : i.val < 6 then threeK2EndpointAt a b c d e f ⟨i.val, hi⟩ else x

theorem threeK2EndpointAt_injective {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6) :
    Function.Injective (threeK2EndpointAt a b c d e f) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [threeK2EndpointAt, eq_comm]

theorem threeK2Embed_injective {α : Type*} [DecidableEq α]
    {a b c d e f x : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hx : x ∉ ({a, b, c, d, e, f} : Row α)) :
    Function.Injective (threeK2Embed a b c d e f x) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hxa, hxb, hxc, hxd, hxe, hxf⟩ := hx
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [threeK2Embed, threeK2EndpointAt, eq_comm]

theorem blocker_image_of_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    {H : Hypergraph α} {T : Row α} {g : α → β}
    (hg : Function.Injective g) (hT : T ∈ blocker H) :
    T.image g ∈ blocker (H.image fun R ↦ R.image g) := by
  classical
  apply mem_blocker.mpr
  have hTransversal : IsTransversal (H.image fun R ↦ R.image g) (T.image g) := by
    intro E hE
    obtain ⟨R, hRH, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨x, hxT, hxR⟩ := (mem_blocker.mp hT).prop R hRH
    exact ⟨g x, Finset.mem_image.mpr ⟨x, hxT, rfl⟩,
      Finset.mem_image.mpr ⟨x, hxR, rfl⟩⟩
  apply hTransversal.minimal_of_privateRows
  intro y hyImage
  obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hyImage
  obtain ⟨R, hRPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
  refine ⟨R.image g, Finset.mem_image.mpr ⟨R, hRPrivate.1, rfl⟩,
    Finset.mem_image.mpr ⟨x, hxT, rfl⟩,
    Finset.mem_image.mpr ⟨x, hRPrivate.2.2.1, rfl⟩, ?_⟩
  intro z hzTImage hzRImage
  obtain ⟨u, huT, rfl⟩ := Finset.mem_image.mp hzTImage
  obtain ⟨v, hvR, huv⟩ := Finset.mem_image.mp hzRImage
  have huv' : u = v := (hg huv).symm
  subst v
  have hux : u = x := hRPrivate.2.2.2 huT hvR
  exact congrArg g hux

theorem blocker_image_eq_of_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    {H : Hypergraph α} {g : α → β}
    (hg : Function.Injective g) :
    blocker (H.image fun R ↦ R.image g) =
      (blocker H).image fun T ↦ T.image g := by
  classical
  ext T
  constructor
  · intro hT
    let S : Row α := Finset.univ.filter fun x ↦ g x ∈ T
    have hTRange : T ⊆ Finset.univ.image g := by
      intro y hyT
      obtain ⟨P, hPPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hyT
      obtain ⟨R, hRH, rfl⟩ := Finset.mem_image.mp hPPrivate.1
      obtain ⟨x, hxR, hxy⟩ := Finset.mem_image.mp hPPrivate.2.2.1
      exact Finset.mem_image.mpr ⟨x, by simp, hxy⟩
    have hSImage : S.image g = T := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hxS).2
      · intro hyT
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (hTRange hyT)
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨by simp, hyT⟩, rfl⟩
    have hS : S ∈ blocker H := by
      apply mem_blocker.mpr
      have hTransversal : IsTransversal H S := by
        intro R hRH
        have hRImage : R.image g ∈ H.image fun E ↦ E.image g :=
          Finset.mem_image.mpr ⟨R, hRH, rfl⟩
        obtain ⟨y, hyT, hyR⟩ := (mem_blocker.mp hT).prop _ hRImage
        obtain ⟨x, hxR, hxy⟩ := Finset.mem_image.mp hyR
        subst y
        exact ⟨x, Finset.mem_filter.mpr ⟨by simp, hyT⟩, hxR⟩
      apply hTransversal.minimal_of_privateRows
      intro x hxS
      have hgxT : g x ∈ T := (Finset.mem_filter.mp hxS).2
      obtain ⟨P, hPPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hgxT
      obtain ⟨R, hRH, hRImage⟩ := Finset.mem_image.mp hPPrivate.1
      refine ⟨R, hRH, hxS, ?_, ?_⟩
      · obtain ⟨z, hzR, hzgx⟩ := Finset.mem_image.mp
          (hRImage ▸ hPPrivate.2.2.1)
        exact (hg hzgx).symm ▸ hzR
      · intro z hzS hzR
        have hgzT : g z ∈ T := (Finset.mem_filter.mp hzS).2
        have hgzP : g z ∈ P := by
          rw [← hRImage]
          exact Finset.mem_image.mpr ⟨z, hzR, rfl⟩
        exact hg (hPPrivate.2.2.2 hgzT hgzP)
    exact Finset.mem_image.mpr ⟨S, hS, hSImage⟩
  · intro hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    exact blocker_image_of_injective hg hS

theorem threeK2AsymmetricRows_card (m : BoolCube) :
    (threeK2AsymmetricRows m).card = 5 := by
  rcases m with ⟨p, q, r⟩
  cases p <;> cases q <;> cases r <;> decide

theorem supportRowCode_injective_of_asymmetric {P Q S : ValidFiveSupportPair}
    {m : BoolCube}
    (hCodes : threeK2FiniteRowCodes P Q S = threeK2AsymmetricRows m) :
    Function.Injective (supportRowCode P Q S) := by
  have hImageCard :
      ((Finset.univ : Finset (Fin 5)).image (supportRowCode P Q S)).card = 5 := by
    rw [show (Finset.univ : Finset (Fin 5)).image (supportRowCode P Q S) =
        threeK2FiniteRowCodes P Q S by rfl,
      hCodes, threeK2AsymmetricRows_card]
  have hUnivCard : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  have hInjOn : Set.InjOn (supportRowCode P Q S)
      (Finset.univ : Finset (Fin 5)) := by
    apply Finset.card_image_iff.mp
    rw [hImageCard, hUnivCard]
  intro i j hij
  exact hInjOn (by simp) (by simp) hij

def threeK2OutsideRowCodes {α : Type*} [DecidableEq α]
    (P Q S : ValidFiveSupportPair)
    (R0 R1 R2 R3 R4 : Row α) (x : α) : Finset BoolCube :=
  (fiveRowSupport R0 R1 R2 R3 R4 x).image (supportRowCode P Q S)

theorem mem_threeK2OutsideRowCodes_iff {α : Type*} [DecidableEq α]
    {P Q S : ValidFiveSupportPair}
    {R0 R1 R2 R3 R4 : Row α} {x : α} {i : Fin 5}
    (hCodeInj : Function.Injective (supportRowCode P Q S)) :
    supportRowCode P Q S i ∈
        threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x ↔
      x ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
  constructor
  · intro h
    obtain ⟨j, hjSupport, hji⟩ := Finset.mem_image.mp h
    have hji' : j = i := hCodeInj hji
    subst j
    simpa [fiveRowSupport] using hjSupport
  · intro hxi
    exact Finset.mem_image.mpr
      ⟨i, by simpa [fiveRowSupport] using hxi, rfl⟩

theorem inter_image_univ_eq_image_filter {α β : Type*}
    [Fintype α] [DecidableEq β]
    (R : Row β) (g : α → β) :
    R ∩ (Finset.univ.image g) =
      (Finset.univ.filter fun i ↦ g i ∈ R).image g := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxR, hxImage⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxImage
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨by simp, hxR⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨-, hiR⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_inter.mpr ⟨hiR, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩

theorem endpointIn_supportRowCode_iff {α : Type*} [DecidableEq α]
    {P Q S : ValidFiveSupportPair}
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f : α}
    (hPa : selectFiveSupport P true = fiveRowSupport R0 R1 R2 R3 R4 a)
    (hPb : selectFiveSupport P false = fiveRowSupport R0 R1 R2 R3 R4 b)
    (hQc : selectFiveSupport Q true = fiveRowSupport R0 R1 R2 R3 R4 c)
    (hQd : selectFiveSupport Q false = fiveRowSupport R0 R1 R2 R3 R4 d)
    (hSe : selectFiveSupport S true = fiveRowSupport R0 R1 R2 R3 R4 e)
    (hSf : selectFiveSupport S false = fiveRowSupport R0 R1 R2 R3 R4 f)
    (hComplement : ∀ i : Fin 5,
      (i ∈ selectFiveSupport P true ↔ i ∉ selectFiveSupport P false) ∧
      (i ∈ selectFiveSupport Q true ↔ i ∉ selectFiveSupport Q false) ∧
      (i ∈ selectFiveSupport S true ↔ i ∉ selectFiveSupport S false))
    (i : Fin 5) (j : Fin 6) :
    endpointInBoolCube j (supportRowCode P Q S i) = true ↔
      threeK2EndpointAt a b c d e f j ∈
        fiveRowAt R0 R1 R2 R3 R4 i := by
  obtain ⟨hP, hQ, hS⟩ := hComplement i
  have haIff :
      i ∈ selectFiveSupport P true ↔
        a ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hPa]
    simp [fiveRowSupport]
  have hbIff :
      i ∈ selectFiveSupport P false ↔
        b ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hPb]
    simp [fiveRowSupport]
  have hcIff :
      i ∈ selectFiveSupport Q true ↔
        c ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hQc]
    simp [fiveRowSupport]
  have hdIff :
      i ∈ selectFiveSupport Q false ↔
        d ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hQd]
    simp [fiveRowSupport]
  have heIff :
      i ∈ selectFiveSupport S true ↔
        e ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hSe]
    simp [fiveRowSupport]
  have hfIff :
      i ∈ selectFiveSupport S false ↔
        f ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    rw [hSf]
    simp [fiveRowSupport]
  have habNeg :
      a ∉ fiveRowAt R0 R1 R2 R3 R4 i ↔
        b ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    constructor
    · intro ha
      by_contra hb
      exact ha (haIff.mp (hP.mpr (fun hb' ↦ hb (hbIff.mp hb'))))
    · intro hb ha
      exact (hP.mp (haIff.mpr ha)) (hbIff.mpr hb)
  have hcdNeg :
      c ∉ fiveRowAt R0 R1 R2 R3 R4 i ↔
        d ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    constructor
    · intro hc
      by_contra hd
      exact hc (hcIff.mp (hQ.mpr (fun hd' ↦ hd (hdIff.mp hd'))))
    · intro hd hc
      exact (hQ.mp (hcIff.mpr hc)) (hdIff.mpr hd)
  have hefNeg :
      e ∉ fiveRowAt R0 R1 R2 R3 R4 i ↔
        f ∈ fiveRowAt R0 R1 R2 R3 R4 i := by
    constructor
    · intro he
      by_contra hf
      exact he (heIff.mp (hS.mpr (fun hf' ↦ hf (hfIff.mp hf'))))
    · intro hf he
      exact (hS.mp (heIff.mpr he)) (hfIff.mpr hf)
  fin_cases j
  · simp [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hPa, fiveRowSupport]
  · simpa [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hPa, fiveRowSupport] using habNeg
  · simp [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hQc, fiveRowSupport]
  · simpa [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hQc, fiveRowSupport] using hcdNeg
  · simp [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hSe, fiveRowSupport]
  · simpa [endpointInBoolCube, supportRowCode, threeK2EndpointAt,
      hSe, fiveRowSupport] using hefNeg

theorem threeK2_asymmetric_row_image_eq {α : Type*}
    [DecidableEq α]
    {P Q S : ValidFiveSupportPair}
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f x : α}
    (hPa : selectFiveSupport P true = fiveRowSupport R0 R1 R2 R3 R4 a)
    (hPb : selectFiveSupport P false = fiveRowSupport R0 R1 R2 R3 R4 b)
    (hQc : selectFiveSupport Q true = fiveRowSupport R0 R1 R2 R3 R4 c)
    (hQd : selectFiveSupport Q false = fiveRowSupport R0 R1 R2 R3 R4 d)
    (hSe : selectFiveSupport S true = fiveRowSupport R0 R1 R2 R3 R4 e)
    (hSf : selectFiveSupport S false = fiveRowSupport R0 R1 R2 R3 R4 f)
    (hComplement : ∀ i : Fin 5,
      (i ∈ selectFiveSupport P true ↔ i ∉ selectFiveSupport P false) ∧
      (i ∈ selectFiveSupport Q true ↔ i ∉ selectFiveSupport Q false) ∧
      (i ∈ selectFiveSupport S true ↔ i ∉ selectFiveSupport S false))
    (hCodeInj : Function.Injective (supportRowCode P Q S))
    (i : Fin 5) :
    ((Finset.univ : Finset (Fin 7)).filter fun j ↦
        if hj : j.val < 6 then
          endpointInBoolCube ⟨j.val, hj⟩ (supportRowCode P Q S i)
        else supportRowCode P Q S i ∈
          threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x).image
        (threeK2Embed a b c d e f x) =
      fiveRowAt R0 R1 R2 R3 R4 i ∩
        (Finset.univ.image (threeK2Embed a b c d e f x)) := by
  rw [inter_image_univ_eq_image_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases j
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (0 : Fin 6)
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (1 : Fin 6)
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (2 : Fin 6)
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (3 : Fin 6)
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (4 : Fin 6)
  · simpa [threeK2Embed] using
      endpointIn_supportRowCode_iff hPa hPb hQc hQd hSe hSf hComplement i (5 : Fin 6)
  · simpa [threeK2Embed] using
      (mem_threeK2OutsideRowCodes_iff
        (R0 := R0) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4)
        (x := x) (i := i) hCodeInj)

theorem threeK2_asymmetric_restriction_eq_image {α : Type*}
    [DecidableEq α]
    {P Q S : ValidFiveSupportPair} {m : BoolCube}
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f x : α}
    (hPa : selectFiveSupport P true = fiveRowSupport R0 R1 R2 R3 R4 a)
    (hPb : selectFiveSupport P false = fiveRowSupport R0 R1 R2 R3 R4 b)
    (hQc : selectFiveSupport Q true = fiveRowSupport R0 R1 R2 R3 R4 c)
    (hQd : selectFiveSupport Q false = fiveRowSupport R0 R1 R2 R3 R4 d)
    (hSe : selectFiveSupport S true = fiveRowSupport R0 R1 R2 R3 R4 e)
    (hSf : selectFiveSupport S false = fiveRowSupport R0 R1 R2 R3 R4 f)
    (hComplement : ∀ i : Fin 5,
      (i ∈ selectFiveSupport P true ↔ i ∉ selectFiveSupport P false) ∧
      (i ∈ selectFiveSupport Q true ↔ i ∉ selectFiveSupport Q false) ∧
      (i ∈ selectFiveSupport S true ↔ i ∉ selectFiveSupport S false))
    (hCodes : threeK2FiniteRowCodes P Q S = threeK2AsymmetricRows m) :
    (asymmetricRowsSeven m
        (threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x)).image
        (fun R ↦ R.image (threeK2Embed a b c d e f x)) =
      restrictRows ({R0, R1, R2, R3, R4} : Hypergraph α)
        (Finset.univ.image (threeK2Embed a b c d e f x)) := by
  let code := supportRowCode P Q S
  let X := threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x
  let g := threeK2Embed a b c d e f x
  have hCodeInj : Function.Injective code :=
    supportRowCode_injective_of_asymmetric hCodes
  ext E
  constructor
  · intro hE
    obtain ⟨T, hTModel, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨q, hqCodes, rfl⟩ := Finset.mem_image.mp hTModel
    rw [← hCodes] at hqCodes
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hqCodes
    apply mem_restrictRows.mpr
    refine ⟨fiveRowAt R0 R1 R2 R3 R4 i,
      fiveRowAt_mem R0 R1 R2 R3 R4 i, ?_⟩
    exact (threeK2_asymmetric_row_image_eq hPa hPb hQc hQd hSe hSf
      hComplement hCodeInj i).symm
  · intro hE
    obtain ⟨R, hRRows, rfl⟩ := mem_restrictRows.mp hE
    obtain ⟨i, rfl⟩ := exists_fiveRowAt_of_mem hRRows
    have hCodeModel : code i ∈ threeK2AsymmetricRows m := by
      rw [← hCodes]
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(Finset.univ : Finset (Fin 7)).filter fun j ↦
        if hj : j.val < 6 then endpointInBoolCube ⟨j.val, hj⟩ (code i)
        else code i ∈ X, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨code i, hCodeModel, rfl⟩
    · exact threeK2_asymmetric_row_image_eq hPa hPb hQc hQd hSe hSf
        hComplement hCodeInj i

theorem finitePrivateBlockerCertificate_eq_true_iff {n : Nat}
    {H : Hypergraph (Fin n)} {T : Row (Fin n)} :
    finitePrivateBlockerCertificate H T = true ↔ T ∈ blocker H := by
  constructor
  · intro hCertificate
    simp only [finitePrivateBlockerCertificate, finiteIsTransversal, Bool.and_eq_true,
      decide_eq_true_eq] at hCertificate
    obtain ⟨hNotDisjoint, hPrivate⟩ := hCertificate
    have hTransversal : IsTransversal H T := by
      intro E hEH
      by_contra hNoIntersection
      apply hNotDisjoint E hEH
      apply Finset.disjoint_left.mpr
      intro x hxT hxE
      exact hNoIntersection ⟨x, hxT, hxE⟩
    apply mem_blocker.mpr
    apply hTransversal.minimal_of_privateRows
    intro x hxT
    obtain ⟨E, hEH, hInter⟩ := hPrivate x hxT
    refine ⟨E, hEH, hxT, ?_, ?_⟩
    · have hxInter : x ∈ T ∩ E := by rw [hInter]; simp
      exact (Finset.mem_inter.mp hxInter).2
    · intro y hyT hyE
      have hyInter : y ∈ T ∩ E := Finset.mem_inter.mpr ⟨hyT, hyE⟩
      rw [hInter] at hyInter
      simpa using hyInter
  · intro hT
    have hMinimal := mem_blocker.mp hT
    simp only [finitePrivateBlockerCertificate, finiteIsTransversal, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · intro E hEH hDisjoint
      obtain ⟨x, hxT, hxE⟩ := hMinimal.prop E hEH
      exact Finset.disjoint_left.mp hDisjoint hxT hxE
    intro x hxT
    obtain ⟨E, hEPrivate⟩ := hMinimal.exists_privateRow hxT
    refine ⟨E, hEPrivate.1, ?_⟩
    ext y
    constructor
    · intro hy
      have hyx := hEPrivate.2.2.2
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      simp [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact Finset.mem_inter.mpr ⟨hxT, hEPrivate.2.2.1⟩

def finiteBlocker {n : Nat} (H : Hypergraph (Fin n)) : Hypergraph (Fin n) :=
  Finset.univ.filter fun T ↦ finitePrivateBlockerCertificate H T = true

theorem finiteBlocker_eq_blocker {n : Nat} (H : Hypergraph (Fin n)) :
    finiteBlocker H = blocker H := by
  ext T
  simp [finiteBlocker, finitePrivateBlockerCertificate_eq_true_iff]

def endpointInBoolCubeSeven (z : Fin 7) (q : BoolCube) : Bool :=
  if z = 0 then endpointInBoolCube 0 q
  else if z = 1 then endpointInBoolCube 1 q
  else if z = 2 then endpointInBoolCube 2 q
  else if z = 3 then endpointInBoolCube 3 q
  else if z = 4 then endpointInBoolCube 4 q
  else if z = 5 then endpointInBoolCube 5 q
  else false

def threeK2AsymmetricSpecial (m : BoolCube) : Row (Fin 7) :=
  Finset.univ.filter fun z ↦
    endpointInBoolCubeSeven z (boolCubeComplement m) = false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
-- The explicit Fin 7 certificate requires full Boolean normalization.
theorem threeK2_asymmetric_special_certificate :
    ∀ m : BoolCube,
      finitePrivateBlockerCertificate
        (asymmetricRowsSeven m {boolCubeComplement m})
        (threeK2AsymmetricSpecial m) = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
-- Uniqueness scans every finite candidate and normalizes its private-row certificate.
theorem threeK2_asymmetric_special_unique :
    ∀ (m : BoolCube) (T : Row (Fin 7)),
      finitePrivateBlockerCertificate
          (asymmetricRowsSeven m {boolCubeComplement m}) T = true →
        6 ∈ T → T = threeK2AsymmetricSpecial m := by
  decide

def threeK2UnsaturatedEndpoint (m : BoolCube) : Fin 6 :=
  if m.1 then 0 else 1

theorem threeK2_unsaturated_endpoint_not_in_complement :
    ∀ m : BoolCube,
      endpointInBoolCube (threeK2UnsaturatedEndpoint m)
        (boolCubeComplement m) = false := by
  decide

theorem threeK2_punctured_has_unsaturated_endpoint :
    ∀ m : BoolCube, ∃ q ∈ boolCubePuncturedClass m,
      endpointInBoolCube (threeK2UnsaturatedEndpoint m) q = true := by
  decide

theorem threeK2_punctured_saturated_endpoint_codes :
    ∀ (m : BoolCube) (z : Fin 6),
      endpointInBoolCube z (boolCubeComplement m) = true →
      ∃ q₁ ∈ boolCubePuncturedClass m,
        ∃ q₂ ∈ boolCubePuncturedClass m,
          q₁ ≠ q₂ ∧ endpointInBoolCube z q₁ = true ∧
            endpointInBoolCube z q₂ = true := by
  decide

theorem endpointInBoolCube_iff_mem_decode {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (z : Fin 6) (q : BoolCube) :
    endpointInBoolCube z q = true ↔
      threeK2EndpointAt a b c d e f z ∈ threeK2Decode a b c d e f q := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  rcases q with ⟨p, q, r⟩
  fin_cases z <;> cases p <;> cases q <;> cases r <;>
    simp_all [endpointInBoolCube, threeK2EndpointAt, threeK2Decode, eq_comm]

theorem threeK2Decode_injective {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6) :
    Function.Injective (threeK2Decode a b c d e f) := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  have hca := Ne.symm hac
  have hea := Ne.symm hae
  have hcb := Ne.symm hbc
  have heb := Ne.symm hbe
  have hec := Ne.symm hce
  have hed := Ne.symm hde
  have hCodeDecode (q : BoolCube) :
      threeK2Code a c e (threeK2Decode a b c d e f q) = q := by
    rcases q with ⟨q0, q1, q2⟩
    cases q0 <;> cases q1 <;> cases q2 <;>
      simp [threeK2Decode, threeK2Code, hab, hac, had, hae, haf,
        hca, hcb, hcd, hce, hcf, hea, heb, hec, hed, hef]
  intro p q hpq
  rw [← hCodeDecode p, ← hCodeDecode q, hpq]

theorem threeK2Decode_mem_transversalTriples {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {q : BoolCube}
    (hCube : q ∈ threeK2CubeTransversalCodes K a b c d e f) :
    threeK2Decode a b c d e f q ∈
      threeK2TransversalTriples K a b c d e f := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · rcases q with ⟨p, q, r⟩
    cases p <;> cases q <;> cases r <;>
      simp [threeK2EndpointTriples, threeK2Decode]
  · exact (Finset.mem_filter.mp hCube).2

def threeK2EndpointPairAt {α : Type*} [DecidableEq α]
    (a b c d e f : α) (z : Fin 6) : Row α :=
  if z.val < 2 then {a, b}
  else if z.val < 4 then {c, d}
  else {e, f}

theorem threeK2EndpointPairAt_mem {α : Type*}
    [Fintype α] [DecidableEq α]
    {a b c d e f : α} {z : Fin 6}
    {K : Hypergraph α}
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}}) :
    threeK2EndpointPairAt a b c d e f z ∈ blocker K := by
  have hPairRows : threeK2EndpointPairAt a b c d e f z ∈ pairRows (blocker K) := by
    rw [hPairs]
    fin_cases z <;> simp [threeK2EndpointPairAt]
  exact (Finset.mem_filter.mp hPairRows).1

theorem threeK2EndpointAt_mem_pairAt {α : Type*} [DecidableEq α]
    (a b c d e f : α) (z : Fin 6) :
    threeK2EndpointAt a b c d e f z ∈
      threeK2EndpointPairAt a b c d e f z := by
  fin_cases z <;> simp [threeK2EndpointAt, threeK2EndpointPairAt]

theorem threeK2EndpointPairAt_card {α : Type*} [DecidableEq α]
    {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (z : Fin 6) :
    (threeK2EndpointPairAt a b c d e f z).card = 2 := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  fin_cases z <;> simp [threeK2EndpointPairAt, hab, hcd, hef]

theorem threeK2EndpointPairAt_subset_endpoints {α : Type*} [DecidableEq α]
    (a b c d e f : α) (z : Fin 6) :
    threeK2EndpointPairAt a b c d e f z ⊆ {a, b, c, d, e, f} := by
  fin_cases z <;> simp only [threeK2EndpointPairAt] <;>
    intro x hx <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢ <;>
    aesop

theorem threeK2Decode_subset_endpoints {α : Type*} [DecidableEq α]
    (a b c d e f : α) (q : BoolCube) :
    threeK2Decode a b c d e f q ⊆ {a, b, c, d, e, f} := by
  rcases q with ⟨p, q, r⟩
  cases p <;> cases q <;> cases r <;> simp only [threeK2Decode] <;>
    intro x hx <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢ <;>
    aesop

theorem threeK2_lift_asymmetric_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {m : BoolCube} {X : Finset BoolCube}
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f x : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hx : x ∉ ({a, b, c, d, e, f} : Row α))
    (hFamily :
      (asymmetricRowsSeven m X).image
          (fun R ↦ R.image (threeK2Embed a b c d e f x)) =
        restrictRows ({R0, R1, R2, R3, R4} : Hypergraph α)
          (Finset.univ.image (threeK2Embed a b c d e f x)))
    {T : Row (Fin 7)}
    (hT : finitePrivateBlockerCertificate (asymmetricRowsSeven m X) T = true) :
    T.image (threeK2Embed a b c d e f x) ∈
      blocker ({R0, R1, R2, R3, R4} : Hypergraph α) := by
  have hg := threeK2Embed_injective hVertices hx
  have hTModel : T ∈ blocker (asymmetricRowsSeven m X) :=
    finitePrivateBlockerCertificate_eq_true_iff.mp hT
  have hTRestriction := blocker_image_of_injective hg hTModel
  rw [hFamily] at hTRestriction
  apply blocker_restrictRows_lift _ hTRestriction
  intro y hy
  obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨z, by simp, rfl⟩

theorem threeK2_asymmetric_saturated_endpoint_base {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {m : BoolCube} {z : Fin 6}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hCubeGood : threeK2CubeTransversalCodes K a b c d e f =
      boolCubePuncturedClass m)
    (hSaturated : endpointInBoolCube z (boolCubeComplement m) = true) :
    ∃ B : Hypergraph α,
      B.card = 3 ∧
        B ⊆ pointSupport (blocker K) (threeK2EndpointAt a b c d e f z) ∧
        ∀ T ∈ B, T ⊆ ({a, b, c, d, e, f} : Row α) := by
  classical
  obtain ⟨q₁, hq₁Class, q₂, hq₂Class, hq₁q₂, hzq₁, hzq₂⟩ :=
    threeK2_punctured_saturated_endpoint_codes m z hSaturated
  let P := threeK2EndpointPairAt a b c d e f z
  let T₁ := threeK2Decode a b c d e f q₁
  let T₂ := threeK2Decode a b c d e f q₂
  let y := threeK2EndpointAt a b c d e f z
  have hq₁Cube : q₁ ∈ threeK2CubeTransversalCodes K a b c d e f := by
    rw [hCubeGood]
    exact hq₁Class
  have hq₂Cube : q₂ ∈ threeK2CubeTransversalCodes K a b c d e f := by
    rw [hCubeGood]
    exact hq₂Class
  have hT₁Good : T₁ ∈ threeK2TransversalTriples K a b c d e f :=
    threeK2Decode_mem_transversalTriples hq₁Cube
  have hT₂Good : T₂ ∈ threeK2TransversalTriples K a b c d e f :=
    threeK2Decode_mem_transversalTriples hq₂Cube
  have hGoodBlocker :
      threeK2TransversalTriples K a b c d e f ⊆ blocker K :=
    threeK2_transversal_triples_subset_blocker hVertices hBRows hPairs
  have hPBlocker : P ∈ blocker K := threeK2EndpointPairAt_mem hPairs
  have hT₁Blocker : T₁ ∈ blocker K := hGoodBlocker hT₁Good
  have hT₂Blocker : T₂ ∈ blocker K := hGoodBlocker hT₂Good
  have hyP : y ∈ P := threeK2EndpointAt_mem_pairAt a b c d e f z
  have hyT₁ : y ∈ T₁ :=
    (endpointInBoolCube_iff_mem_decode hVertices z q₁).mp hzq₁
  have hyT₂ : y ∈ T₂ :=
    (endpointInBoolCube_iff_mem_decode hVertices z q₂).mp hzq₂
  have hT₁T₂ : T₁ ≠ T₂ := by
    intro hEq
    exact hq₁q₂ (threeK2Decode_injective hVertices hEq)
  have hPCard : P.card = 2 := threeK2EndpointPairAt_card hVertices z
  have hT₁Card : T₁.card = 3 :=
    threeK2_endpoint_triple_card hVertices (Finset.mem_filter.mp hT₁Good).1
  have hT₂Card : T₂.card = 3 :=
    threeK2_endpoint_triple_card hVertices (Finset.mem_filter.mp hT₂Good).1
  have hPT₁ : P ≠ T₁ := by
    intro hEq
    rw [hEq] at hPCard
    omega
  have hPT₂ : P ≠ T₂ := by
    intro hEq
    rw [hEq] at hPCard
    omega
  let B : Hypergraph α := {P, T₁, T₂}
  have hBCard : B.card = 3 := by
    simp [B, hPT₁, hPT₂, hT₁T₂]
  have hBSubset : B ⊆ pointSupport (blocker K) y := by
    intro T hT
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact mem_pointSupport.mpr ⟨hPBlocker, hyP⟩
    · exact mem_pointSupport.mpr ⟨hT₁Blocker, hyT₁⟩
    · exact mem_pointSupport.mpr ⟨hT₂Blocker, hyT₂⟩
  refine ⟨B, hBCard, hBSubset, ?_⟩
  intro T hT
  simp only [B, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · exact threeK2EndpointPairAt_subset_endpoints a b c d e f z
  · exact threeK2Decode_subset_endpoints a b c d e f q₁
  · exact threeK2Decode_subset_endpoints a b c d e f q₂

theorem threeK2_asymmetric_saturated_endpoint_degree {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {m : BoolCube} {z : Fin 6}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hCubeGood : threeK2CubeTransversalCodes K a b c d e f =
      boolCubePuncturedClass m)
    (hSaturated : endpointInBoolCube z (boolCubeComplement m) = true) :
    degree (blocker K) (threeK2EndpointAt a b c d e f z) = 3 := by
  obtain ⟨B, hBCard, hBSubset, -⟩ :=
    threeK2_asymmetric_saturated_endpoint_base hVertices hBRows hPairs
      hCubeGood hSaturated
  have hLower := Finset.card_le_card hBSubset
  rw [hBCard, pointSupport_card] at hLower
  exact Nat.le_antisymm (hBDegree _) hLower

theorem threeK2_asymmetric_outside_support_eq_complement {α : Type*}
    [Fintype α] [DecidableEq α]
    {P Q S : ValidFiveSupportPair} {m : BoolCube}
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f x : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hBDegree : MaxDegreeAtMost
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 3)
    (hPairs : pairRows
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
        {{a, b}, {c, d}, {e, f}})
    (hxOutside : x ∉ ({a, b, c, d, e, f} : Row α))
    (hxActive : ∃ R ∈ ({R0, R1, R2, R3, R4} : Hypergraph α), x ∈ R)
    (hCodes : threeK2FiniteRowCodes P Q S = threeK2AsymmetricRows m)
    (hCubeGood : threeK2CubeTransversalCodes
      ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f =
        boolCubePuncturedClass m)
    (hFamily :
      (asymmetricRowsSeven m
          (threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x)).image
          (fun R ↦ R.image (threeK2Embed a b c d e f x)) =
        restrictRows ({R0, R1, R2, R3, R4} : Hypergraph α)
          (Finset.univ.image (threeK2Embed a b c d e f x))) :
    threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x =
      {boolCubeComplement m} := by
  classical
  let K : Hypergraph α := {R0, R1, R2, R3, R4}
  let X := threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x
  let code := supportRowCode P Q S
  let g := threeK2Embed a b c d e f x
  have hCodeInj : Function.Injective code :=
    supportRowCode_injective_of_asymmetric hCodes
  have hXSubset : X ⊆ threeK2AsymmetricRows m := by
    intro q hqX
    obtain ⟨i, hiSupport, rfl⟩ := Finset.mem_image.mp hqX
    rw [← hCodes]
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  have hXNonempty : X ≠ ∅ := by
    obtain ⟨R, hRK, hxR⟩ := hxActive
    obtain ⟨i, rfl⟩ := exists_fiveRowAt_of_mem hRK
    intro hEmpty
    have hCodeMem : code i ∈ X :=
      (mem_threeK2OutsideRowCodes_iff
        (R0 := R0) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4)
        (x := x) (i := i) hCodeInj).mpr hxR
    rw [hEmpty] at hCodeMem
    simp at hCodeMem
  have hXCard : X.card ≤ 3 := by
    change ((fiveRowSupport R0 R1 R2 R3 R4 x).image code).card ≤ 3
    rw [Finset.card_image_iff.mpr hCodeInj.injOn,
      fiveRowSupport_card_eq_degree hRowsCard]
    exact hKDegree x
  by_contra hNotSpecial
  obtain ⟨T, h6T, hTCertificate, hObstruction⟩ :=
    threeK2_asymmetric_outside_obstruction m X hXSubset hXNonempty
      hXCard hNotSpecial
  let U : Row α := T.image g
  have hg : Function.Injective g := threeK2Embed_injective hVertices hxOutside
  have hUBlocker : U ∈ blocker K :=
    threeK2_lift_asymmetric_blocker hVertices hxOutside hFamily hTCertificate
  have hxU : x ∈ U := by
    apply Finset.mem_image.mpr
    refine ⟨6, h6T, ?_⟩
    simp [g, threeK2Embed]
  rcases hObstruction with hTCard | ⟨z, hzT, hSaturated⟩
  · have hUCard : U.card = 2 := by
      change (T.image g).card = 2
      rw [Finset.card_image_iff.mpr hg.injOn, hTCard]
    have hUPair : U ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hUBlocker, hUCard⟩
    rw [hPairs] at hUPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hUPair
    rcases hUPair with hU | hU | hU
    · apply hxOutside
      rw [hU] at hxU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxU ⊢
      aesop
    · apply hxOutside
      rw [hU] at hxU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxU ⊢
      aesop
    · apply hxOutside
      rw [hU] at hxU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxU ⊢
      aesop
  · let y := threeK2EndpointAt a b c d e f z
    have hyU : y ∈ U := by
      apply Finset.mem_image.mpr
      refine ⟨z.castLE (by omega), hzT, ?_⟩
      simp [g, y, threeK2Embed]
    obtain ⟨B, hBCard, hBSubset, hBEndpoints⟩ :=
      threeK2_asymmetric_saturated_endpoint_base hVertices hBRows hPairs
        hCubeGood hSaturated
    have hUNotB : U ∉ B := by
      intro hUB
      exact hxOutside (hBEndpoints U hUB hxU)
    have hInsertCard : (insert U B).card = 4 := by
      rw [Finset.card_insert_of_notMem hUNotB, hBCard]
    have hInsertSubset : insert U B ⊆ pointSupport (blocker K) y := by
      apply Finset.insert_subset
      · exact mem_pointSupport.mpr ⟨hUBlocker, hyU⟩
      · exact hBSubset
    have hLower := Finset.card_le_card hInsertSubset
    rw [hInsertCard, pointSupport_card] at hLower
    exact (Nat.not_succ_le_self 3) (hLower.trans (hBDegree y))

theorem threeK2_asymmetric_unsaturated_endpoint_base {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {m : BoolCube}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hCubeGood : threeK2CubeTransversalCodes K a b c d e f =
      boolCubePuncturedClass m) :
    ∃ B : Hypergraph α,
      B.card = 2 ∧
        B ⊆ pointSupport (blocker K)
          (threeK2EndpointAt a b c d e f (threeK2UnsaturatedEndpoint m)) ∧
        ∀ T ∈ B, T ⊆ ({a, b, c, d, e, f} : Row α) := by
  classical
  let z := threeK2UnsaturatedEndpoint m
  obtain ⟨q, hqClass, hzq⟩ := threeK2_punctured_has_unsaturated_endpoint m
  let P := threeK2EndpointPairAt a b c d e f z
  let T := threeK2Decode a b c d e f q
  let y := threeK2EndpointAt a b c d e f z
  have hqCube : q ∈ threeK2CubeTransversalCodes K a b c d e f := by
    rw [hCubeGood]
    exact hqClass
  have hTGood : T ∈ threeK2TransversalTriples K a b c d e f :=
    threeK2Decode_mem_transversalTriples hqCube
  have hGoodBlocker :
      threeK2TransversalTriples K a b c d e f ⊆ blocker K :=
    threeK2_transversal_triples_subset_blocker hVertices hBRows hPairs
  have hPBlocker : P ∈ blocker K := threeK2EndpointPairAt_mem hPairs
  have hTBlocker : T ∈ blocker K := hGoodBlocker hTGood
  have hyP : y ∈ P := threeK2EndpointAt_mem_pairAt a b c d e f z
  have hyT : y ∈ T :=
    (endpointInBoolCube_iff_mem_decode hVertices z q).mp hzq
  have hPCard : P.card = 2 := threeK2EndpointPairAt_card hVertices z
  have hTCard : T.card = 3 :=
    threeK2_endpoint_triple_card hVertices (Finset.mem_filter.mp hTGood).1
  have hPT : P ≠ T := by
    intro hEq
    rw [hEq] at hPCard
    omega
  let B : Hypergraph α := {P, T}
  have hBCard : B.card = 2 := by simp [B, hPT]
  have hBSubset : B ⊆ pointSupport (blocker K) y := by
    intro U hU
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl
    · exact mem_pointSupport.mpr ⟨hPBlocker, hyP⟩
    · exact mem_pointSupport.mpr ⟨hTBlocker, hyT⟩
  refine ⟨B, hBCard, hBSubset, ?_⟩
  intro U hU
  simp only [B, Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl
  · exact threeK2EndpointPairAt_subset_endpoints a b c d e f z
  · exact threeK2Decode_subset_endpoints a b c d e f q

theorem threeK2AsymmetricSpecial_image_subset {α : Type*} [DecidableEq α]
    (a b c d e f x : α) (m : BoolCube) :
    (threeK2AsymmetricSpecial m).image (threeK2Embed a b c d e f x) ⊆
      insert x ({a, b, c, d, e, f} : Row α) := by
  intro y hy
  obtain ⟨z, hzSpecial, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_insert]
  by_cases hz : z.val < 6
  · right
    let w : Fin 6 := ⟨z.val, hz⟩
    have hEndpoint :
        threeK2EndpointAt a b c d e f w ∈
          ({a, b, c, d, e, f} : Row α) := by
      exact threeK2EndpointPairAt_subset_endpoints a b c d e f w
        (threeK2EndpointAt_mem_pairAt a b c d e f w)
    change threeK2Embed a b c d e f x z ∈
      ({a, b, c, d, e, f} : Row α)
    rw [threeK2Embed, dif_pos hz]
    exact hEndpoint
  · left
    rw [threeK2Embed, dif_neg hz]

theorem threeK2_unsaturated_endpoint_mem_special_image {α : Type*}
    [DecidableEq α] (a b c d e f x : α) (m : BoolCube) :
    threeK2EndpointAt a b c d e f (threeK2UnsaturatedEndpoint m) ∈
      (threeK2AsymmetricSpecial m).image (threeK2Embed a b c d e f x) := by
  rcases m with ⟨p, q, r⟩
  cases p
  · apply Finset.mem_image.mpr
    refine ⟨1, ?_, ?_⟩
    · simp [threeK2AsymmetricSpecial, endpointInBoolCubeSeven,
        boolCubeComplement, endpointInBoolCube]
    · simp [threeK2Embed, threeK2UnsaturatedEndpoint, threeK2EndpointAt]
  · apply Finset.mem_image.mpr
    refine ⟨0, ?_, ?_⟩
    · simp [threeK2AsymmetricSpecial, endpointInBoolCubeSeven,
        boolCubeComplement, endpointInBoolCube]
    · simp [threeK2Embed, threeK2UnsaturatedEndpoint, threeK2EndpointAt]

theorem threeK2_asymmetric_at_most_one_outside {α : Type*}
    [Fintype α] [DecidableEq α]
    {m : BoolCube} {R0 R1 R2 R3 R4 : Row α}
    {a b c d e f x y : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hBDegree : MaxDegreeAtMost
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 3)
    (hPairs : pairRows
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
        {{a, b}, {c, d}, {e, f}})
    (hCubeGood : threeK2CubeTransversalCodes
      ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f =
        boolCubePuncturedClass m)
    (hxOutside : x ∉ ({a, b, c, d, e, f} : Row α))
    (hyOutside : y ∉ ({a, b, c, d, e, f} : Row α))
    (hxy : x ≠ y)
    (hFamilyX :
      (asymmetricRowsSeven m {boolCubeComplement m}).image
          (fun R ↦ R.image (threeK2Embed a b c d e f x)) =
        restrictRows ({R0, R1, R2, R3, R4} : Hypergraph α)
          (Finset.univ.image (threeK2Embed a b c d e f x)))
    (hFamilyY :
      (asymmetricRowsSeven m {boolCubeComplement m}).image
          (fun R ↦ R.image (threeK2Embed a b c d e f y)) =
        restrictRows ({R0, R1, R2, R3, R4} : Hypergraph α)
          (Finset.univ.image (threeK2Embed a b c d e f y))) :
    False := by
  classical
  let K : Hypergraph α := {R0, R1, R2, R3, R4}
  let z := threeK2UnsaturatedEndpoint m
  let p := threeK2EndpointAt a b c d e f z
  let S := threeK2AsymmetricSpecial m
  let gX := threeK2Embed a b c d e f x
  let gY := threeK2Embed a b c d e f y
  let U := S.image gX
  let V := S.image gY
  have hSCertificate := threeK2_asymmetric_special_certificate m
  have hUBlocker : U ∈ blocker K :=
    threeK2_lift_asymmetric_blocker hVertices hxOutside hFamilyX hSCertificate
  have hVBlocker : V ∈ blocker K :=
    threeK2_lift_asymmetric_blocker hVertices hyOutside hFamilyY hSCertificate
  have h6S : (6 : Fin 7) ∈ S := by
    simp [S, threeK2AsymmetricSpecial, endpointInBoolCubeSeven]
  have hxU : x ∈ U := by
    apply Finset.mem_image.mpr
    refine ⟨6, h6S, ?_⟩
    simp [gX, threeK2Embed]
  have hyV : y ∈ V := by
    apply Finset.mem_image.mpr
    refine ⟨6, h6S, ?_⟩
    simp [gY, threeK2Embed]
  have hpU : p ∈ U := by
    exact threeK2_unsaturated_endpoint_mem_special_image a b c d e f x m
  have hpV : p ∈ V := by
    exact threeK2_unsaturated_endpoint_mem_special_image a b c d e f y m
  have hUSubset : U ⊆ insert x ({a, b, c, d, e, f} : Row α) :=
    threeK2AsymmetricSpecial_image_subset a b c d e f x m
  have hVSubset : V ⊆ insert y ({a, b, c, d, e, f} : Row α) :=
    threeK2AsymmetricSpecial_image_subset a b c d e f y m
  have hxV : x ∉ V := by
    intro hxV
    have hxRange := hVSubset hxV
    simp only [Finset.mem_insert] at hxRange
    rcases hxRange with hxy' | hxEndpoint
    · exact hxy hxy'
    · apply hxOutside
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxEndpoint
  have hUV : U ≠ V := fun hEq ↦ hxV (hEq ▸ hxU)
  obtain ⟨B, hBCard, hBSubset, hBEndpoints⟩ :=
    threeK2_asymmetric_unsaturated_endpoint_base hVertices hBRows hPairs hCubeGood
  have hUNotB : U ∉ B := by
    intro hUB
    exact hxOutside (hBEndpoints U hUB hxU)
  have hVNotB : V ∉ B := by
    intro hVB
    exact hyOutside (hBEndpoints V hVB hyV)
  have hFourCard : (insert U (insert V B)).card = 4 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hVNotB, hBCard]
    · simp [hUV, hUNotB]
  have hFourSubset : insert U (insert V B) ⊆ pointSupport (blocker K) p := by
    apply Finset.insert_subset
    · exact mem_pointSupport.mpr ⟨hUBlocker, hpU⟩
    apply Finset.insert_subset
    · exact mem_pointSupport.mpr ⟨hVBlocker, hpV⟩
    · exact hBSubset
  have hLower := Finset.card_le_card hFourSubset
  rw [hFourCard, pointSupport_card] at hLower
  exact (Nat.not_succ_le_self 3) (hLower.trans (hBDegree p))

theorem subset_threeK2Decode_code_of_endpoint_subset {α : Type*}
    [DecidableEq α] {a b c d e f : α} {T : Row α}
    (hTSubset : T ⊆ ({a, b, c, d, e, f} : Row α))
    (hAB : ¬({a, b} : Row α) ⊆ T)
    (hCD : ¬({c, d} : Row α) ⊆ T)
    (hEF : ¬({e, f} : Row α) ⊆ T) :
    T ⊆ threeK2Decode a b c d e f (threeK2Code a c e T) := by
  intro x hxT
  have hxEndpoint := hTSubset hxT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxEndpoint
  rcases hxEndpoint with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [threeK2Decode, threeK2Code, hxT]
  · have haT : a ∉ T := by
      intro haT
      apply hAB
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haT
      · exact hxT
    simp [threeK2Decode, threeK2Code, haT]
  · simp [threeK2Decode, threeK2Code, hxT]
  · have hcT : c ∉ T := by
      intro hcT
      apply hCD
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcT
      · exact hxT
    simp [threeK2Decode, threeK2Code, hcT]
  · simp [threeK2Decode, threeK2Code, hxT]
  · have heT : e ∉ T := by
      intro heT
      apply hEF
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact heT
      · exact hxT
    simp [threeK2Decode, threeK2Code, heT]

theorem mem_threeK2EndpointTriples_of_endpoint_subset {α : Type*}
    [DecidableEq α] {a b c d e f : α} {T : Row α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hTSubset : T ⊆ ({a, b, c, d, e, f} : Row α))
    (hTCard : T.card = 3)
    (hAB : ¬({a, b} : Row α) ⊆ T)
    (hCD : ¬({c, d} : Row α) ⊆ T)
    (hEF : ¬({e, f} : Row α) ⊆ T) :
    T ∈ threeK2EndpointTriples a b c d e f := by
  let q := threeK2Code a c e T
  let D := threeK2Decode a b c d e f q
  have hTD : T ⊆ D :=
    subset_threeK2Decode_code_of_endpoint_subset hTSubset hAB hCD hEF
  have hDEndpoint : D ∈ threeK2EndpointTriples a b c d e f := by
    rcases q with ⟨p, q, r⟩
    cases p <;> cases q <;> cases r <;>
      simp [D, threeK2Decode, threeK2EndpointTriples]
  have hDCard : D.card = 3 :=
    threeK2_endpoint_triple_card hVertices hDEndpoint
  have hEq : T = D := Finset.eq_of_subset_of_card_le hTD (by omega)
  exact hEq ▸ hDEndpoint

theorem threeK2EndpointTriple_subset_endpoints {α : Type*}
    [DecidableEq α] {a b c d e f : α} {T : Row α}
    (hT : T ∈ threeK2EndpointTriples a b c d e f) :
    T ⊆ ({a, b, c, d, e, f} : Row α) := by
  simp only [threeK2EndpointTriples, Finset.mem_insert,
    Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    aesop

theorem threeK2_endpoint_only_blocker_mem_base {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {T : Row α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hTBlocker : T ∈ blocker K)
    (hTSubset : T ⊆ ({a, b, c, d, e, f} : Row α)) :
    T ∈ insert ({a, b} : Row α)
      (insert ({c, d} : Row α)
        (insert ({e, f} : Row α)
          (threeK2TransversalTriples K a b c d e f))) := by
  classical
  by_cases hTCardTwo : T.card = 2
  · have hTPair : T ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr ⟨hTBlocker, hTCardTwo⟩
    rw [hPairs] at hTPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hTPair ⊢
    rcases hTPair with hT | hT | hT
    · exact Or.inl hT
    · exact Or.inr (Or.inl hT)
    · exact Or.inr (Or.inr (Or.inl hT))
  · obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
        hcd, hce, hcf, hde, hdf, hef⟩ :=
      pairwise_ne_of_sext_card_eq_six hVertices
    have hABBlocker : ({a, b} : Row α) ∈ blocker K :=
      (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
    have hCDBlocker : ({c, d} : Row α) ∈ blocker K :=
      (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
    have hEFBlocker : ({e, f} : Row α) ∈ blocker K :=
      (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
    have hBlockerClutter : IsClutter (blocker K) := blocker_isClutter K
    have hABNotSubset : ¬({a, b} : Row α) ⊆ T := by
      intro hSubset
      have hEq := hBlockerClutter hABBlocker hTBlocker hSubset
      apply hTCardTwo
      rw [← hEq]
      simp [hab]
    have hCDNotSubset : ¬({c, d} : Row α) ⊆ T := by
      intro hSubset
      have hEq := hBlockerClutter hCDBlocker hTBlocker hSubset
      apply hTCardTwo
      rw [← hEq]
      simp [hcd]
    have hEFNotSubset : ¬({e, f} : Row α) ⊆ T := by
      intro hSubset
      have hEq := hBlockerClutter hEFBlocker hTBlocker hSubset
      apply hTCardTwo
      rw [← hEq]
      simp [hef]
    let q := threeK2Code a c e T
    let D := threeK2Decode a b c d e f q
    have hTD : T ⊆ D :=
      subset_threeK2Decode_code_of_endpoint_subset hTSubset hABNotSubset
        hCDNotSubset hEFNotSubset
    have hDEndpoint : D ∈ threeK2EndpointTriples a b c d e f := by
      rcases q with ⟨p, q, r⟩
      cases p <;> cases q <;> cases r <;>
        simp [D, threeK2Decode, threeK2EndpointTriples]
    have hDCard : D.card = 3 :=
      threeK2_endpoint_triple_card hVertices hDEndpoint
    have hTLower := hBRows T hTBlocker
    have hTUpper := Finset.card_le_card hTD
    have hTCard : T.card = 3 := by omega
    have hTEndpoint := mem_threeK2EndpointTriples_of_endpoint_subset
      hVertices hTSubset hTCard hABNotSubset hCDNotSubset hEFNotSubset
    have hTGood : T ∈ threeK2TransversalTriples K a b c d e f :=
      Finset.mem_filter.mpr ⟨hTEndpoint, (mem_blocker.mp hTBlocker).prop⟩
    simp [hTGood]

theorem restrictRows_eq_self_of_rows_subset {α : Type*} [DecidableEq α]
    {K : Hypergraph α} {V : Row α}
    (hRows : ∀ R ∈ K, R ⊆ V) :
    restrictRows K V = K := by
  ext R
  constructor
  · intro hR
    obtain ⟨E, hEK, hER⟩ := mem_restrictRows.mp hR
    have hInter : E ∩ V = E := Finset.inter_eq_left.mpr (hRows E hEK)
    rw [hInter] at hER
    exact hER ▸ hEK
  · intro hRK
    exact mem_restrictRows.mpr
      ⟨R, hRK, Finset.inter_eq_left.mpr (hRows R hRK)⟩

theorem threeK2Embed_range {α : Type*} [DecidableEq α]
    {a b c d e f x : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hxOutside : x ∉ ({a, b, c, d, e, f} : Row α)) :
    (Finset.univ : Finset (Fin 7)).image (threeK2Embed a b c d e f x) =
      insert x ({a, b, c, d, e, f} : Row α) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
    fin_cases z <;> simp [threeK2Embed, threeK2EndpointAt]
  · intro hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact Finset.mem_image.mpr ⟨6, by simp, by simp [threeK2Embed]⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩
      · exact Finset.mem_image.mpr ⟨2, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩
      · exact Finset.mem_image.mpr ⟨3, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩
      · exact Finset.mem_image.mpr ⟨4, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩
      · exact Finset.mem_image.mpr ⟨5, by simp, by simp [threeK2Embed, threeK2EndpointAt]⟩

theorem threeK2_three_good_impossible_of_rows {α : Type*}
    [Fintype α] [DecidableEq α]
    {R0 R1 R2 R3 R4 : Row α} {a b c d e f : α}
    (hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5)
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKDegree : MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3)
    (hBCard : (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)).card = 8)
    (hBRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2)
    (hBDegree : MaxDegreeAtMost
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 3)
    (hPairs : pairRows
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
        {{a, b}, {c, d}, {e, f}})
    (hGoodCard : (threeK2TransversalTriples
      ({R0, R1, R2, R3, R4} : Hypergraph α) a b c d e f).card = 3) :
    False := by
  classical
  let K : Hypergraph α := {R0, R1, R2, R3, R4}
  let V : Row α := {a, b, c, d, e, f}
  let Good := threeK2TransversalTriples K a b c d e f
  let Base : Hypergraph α :=
    insert ({a, b} : Row α)
      (insert ({c, d} : Row α) (insert ({e, f} : Row α) Good))
  let P : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 a,
        fiveRowSupport R0 R1 R2 R3 R4 b), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).1⟩
  let Q : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 c,
        fiveRowSupport R0 R1 R2 R3 R4 d), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.1⟩
  let S : ValidFiveSupportPair :=
    ⟨(fiveRowSupport R0 R1 R2 R3 R4 e,
        fiveRowSupport R0 R1 R2 R3 R4 f), by
      exact validFiveSupportPair_of_pair_blocker hRowsCard hKDegree
        (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
        (pairwise_ne_of_sext_card_eq_six hVertices).2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hAsymmetric : IsThreeK2AsymmetricSupportSystem P Q S :=
    (threeK2_actual_support_classification hRowsCard hVertices hKDegree
      hBRows hPairs).2 hGoodCard
  obtain ⟨m, hFiniteGood, hComplement, hCodes⟩ := hAsymmetric
  have hPa : selectFiveSupport P true = fiveRowSupport R0 R1 R2 R3 R4 a := by
    simp [P, selectFiveSupport]
  have hPb : selectFiveSupport P false = fiveRowSupport R0 R1 R2 R3 R4 b := by
    simp [P, selectFiveSupport]
  have hQc : selectFiveSupport Q true = fiveRowSupport R0 R1 R2 R3 R4 c := by
    simp [Q, selectFiveSupport]
  have hQd : selectFiveSupport Q false = fiveRowSupport R0 R1 R2 R3 R4 d := by
    simp [Q, selectFiveSupport]
  have hSe : selectFiveSupport S true = fiveRowSupport R0 R1 R2 R3 R4 e := by
    simp [S, selectFiveSupport]
  have hSf : selectFiveSupport S false = fiveRowSupport R0 R1 R2 R3 R4 f := by
    simp [S, selectFiveSupport]
  have hCubeGood : threeK2CubeTransversalCodes K a b c d e f =
      boolCubePuncturedClass m := by
    calc
      threeK2CubeTransversalCodes K a b c d e f =
          threeK2GoodOfSixSupports
            (fiveRowSupport R0 R1 R2 R3 R4 a)
            (fiveRowSupport R0 R1 R2 R3 R4 b)
            (fiveRowSupport R0 R1 R2 R3 R4 c)
            (fiveRowSupport R0 R1 R2 R3 R4 d)
            (fiveRowSupport R0 R1 R2 R3 R4 e)
            (fiveRowSupport R0 R1 R2 R3 R4 f) :=
        threeK2CubeTransversalCodes_eq_support_good
          R0 R1 R2 R3 R4 a b c d e f
      _ = threeK2FiniteGood P Q S := by
        simp [P, Q, S, threeK2FiniteGood, threeK2GoodOfSixSupports,
          selectFiveSupport]
      _ = boolCubePuncturedClass m := hFiniteGood
  have hFamily (x : α) :
      (asymmetricRowsSeven m
          (threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x)).image
          (fun R ↦ R.image (threeK2Embed a b c d e f x)) =
        restrictRows K
          (Finset.univ.image (threeK2Embed a b c d e f x)) :=
    threeK2_asymmetric_restriction_eq_image hPa hPb hQc hQd hSe hSf
      hComplement hCodes
  have hSupportSpecial (x : α) (hxOutside : x ∉ V)
      (hxActive : ∃ R ∈ K, x ∈ R) :
      threeK2OutsideRowCodes P Q S R0 R1 R2 R3 R4 x =
        {boolCubeComplement m} :=
    threeK2_asymmetric_outside_support_eq_complement hRowsCard hVertices
      hKDegree hBRows hBDegree hPairs hxOutside hxActive hCodes hCubeGood
      (hFamily x)
  have hOutsideUnique {x y : α}
      (hxOutside : x ∉ V) (hyOutside : y ∉ V)
      (hxActive : ∃ R ∈ K, x ∈ R) (hyActive : ∃ R ∈ K, y ∈ R) : x = y := by
    by_contra hxy
    have hFamilyX := hFamily x
    have hFamilyY := hFamily y
    rw [hSupportSpecial x hxOutside hxActive] at hFamilyX
    rw [hSupportSpecial y hyOutside hyActive] at hFamilyY
    exact threeK2_asymmetric_at_most_one_outside hVertices hBRows hBDegree
      hPairs hCubeGood hxOutside hyOutside hxy hFamilyX hFamilyY
  change Good.card = 3 at hGoodCard
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  have hGoodEndpoint : Good ⊆ threeK2EndpointTriples a b c d e f := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have pair_not_good (u v : α) (huv : u ≠ v) : ({u, v} : Row α) ∉ Good := by
    intro hPairGood
    have hTripleCard :=
      threeK2_endpoint_triple_card hVertices (hGoodEndpoint hPairGood)
    have hPairCard : ({u, v} : Row α).card = 2 := by simp [huv]
    omega
  have hABNotGood : ({a, b} : Row α) ∉ Good := pair_not_good a b hab
  have hCDNotGood : ({c, d} : Row α) ∉ Good := pair_not_good c d hcd
  have hEFNotGood : ({e, f} : Row α) ∉ Good := pair_not_good e f hef
  have hABCD : ({a, b} : Row α) ≠ {c, d} :=
    pair_ne_of_left_not_mem (by simp [hac, had])
  have hABEF : ({a, b} : Row α) ≠ {e, f} :=
    pair_ne_of_left_not_mem (by simp [hae, haf])
  have hCDEF : ({c, d} : Row α) ≠ {e, f} :=
    pair_ne_of_left_not_mem (by simp [hce, hcf])
  have hCDNotTail : ({c, d} : Row α) ∉ insert ({e, f} : Row α) Good := by
    simp [hCDEF, hCDNotGood]
  have hABNotTail : ({a, b} : Row α) ∉
      insert ({c, d} : Row α) (insert ({e, f} : Row α) Good) := by
    simp [hABCD, hABEF, hABNotGood]
  have hBaseCard : Base.card = 6 := by
    change (insert ({a, b} : Row α)
      (insert ({c, d} : Row α) (insert ({e, f} : Row α) Good))).card = 6
    rw [Finset.card_insert_of_notMem hABNotTail,
      Finset.card_insert_of_notMem hCDNotTail,
      Finset.card_insert_of_notMem hEFNotGood, hGoodCard]
  have hBaseEndpoints : ∀ T ∈ Base, T ⊆ V := by
    intro T hT
    simp only [Base, Finset.mem_insert] at hT
    rcases hT with rfl | rfl | rfl | hTGood
    · simp [V]
    · exact threeK2EndpointPairAt_subset_endpoints a b c d e f 2
    · exact threeK2EndpointPairAt_subset_endpoints a b c d e f 4
    · exact threeK2EndpointTriple_subset_endpoints (hGoodEndpoint hTGood)
  by_cases hOutside : ∃ x, x ∉ V ∧ ∃ R ∈ K, x ∈ R
  · obtain ⟨x, hxOutside, hxActive⟩ := hOutside
    have hRowsRange : ∀ R ∈ K, R ⊆ insert x V := by
      intro R hRK y hyR
      by_cases hyV : y ∈ V
      · exact Finset.mem_insert.mpr (Or.inr hyV)
      · have hyActive : ∃ E ∈ K, y ∈ E := ⟨R, hRK, hyR⟩
        have hyx := hOutsideUnique hyV hxOutside hyActive hxActive
        exact Finset.mem_insert.mpr (Or.inl hyx)
    have hRange := threeK2Embed_range hVertices hxOutside
    have hFamilyExact :
        (asymmetricRowsSeven m {boolCubeComplement m}).image
            (fun R ↦ R.image (threeK2Embed a b c d e f x)) = K := by
      have hFx := hFamily x
      rw [hSupportSpecial x hxOutside hxActive] at hFx
      rw [hRange] at hFx
      exact hFx.trans (restrictRows_eq_self_of_rows_subset hRowsRange)
    let g := threeK2Embed a b c d e f x
    let U := (threeK2AsymmetricSpecial m).image g
    have hg : Function.Injective g := threeK2Embed_injective hVertices hxOutside
    have hBlockerImage : blocker K =
        (blocker (asymmetricRowsSeven m {boolCubeComplement m})).image
          (fun T ↦ T.image g) := by
      rw [← hFamilyExact]
      exact blocker_image_eq_of_injective hg
    have h6Special : (6 : Fin 7) ∈ threeK2AsymmetricSpecial m := by
      simp [threeK2AsymmetricSpecial, endpointInBoolCubeSeven]
    have hxU : x ∈ U := by
      apply Finset.mem_image.mpr
      refine ⟨6, h6Special, ?_⟩
      simp [g, threeK2Embed]
    have hUNotBase : U ∉ Base := by
      intro hUBase
      exact hxOutside (hBaseEndpoints U hUBase hxU)
    have hBlockerSubset : blocker K ⊆ insert U Base := by
      intro T hTK
      have hTRange : T ⊆ insert x V := by
        intro y hyT
        by_cases hyV : y ∈ V
        · exact Finset.mem_insert.mpr (Or.inr hyV)
        · by_cases hyActive : ∃ R ∈ K, y ∈ R
          · have hyx := hOutsideUnique hyV hxOutside hyActive hxActive
            exact Finset.mem_insert.mpr (Or.inl hyx)
          · have hyInactive : ∀ R ∈ K, y ∉ R := by
              intro R hRK hyR
              exact hyActive ⟨R, hRK, hyR⟩
            exact ((mem_blocker.mp hTK).avoids_inactive hyInactive hyT).elim
      by_cases hxT : x ∈ T
      · rw [hBlockerImage] at hTK
        obtain ⟨W, hWBlocker, rfl⟩ := Finset.mem_image.mp hTK
        obtain ⟨z, hzW, hzg⟩ := Finset.mem_image.mp hxT
        have hg6 : g 6 = x := by simp [g, threeK2Embed]
        have hz6 : z = 6 := hg (hzg.trans hg6.symm)
        subst z
        have hWCertificate :=
          finitePrivateBlockerCertificate_eq_true_iff.mpr hWBlocker
        have hWSpecial :=
          threeK2_asymmetric_special_unique m W hWCertificate hzW
        subst W
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · apply Finset.mem_insert.mpr
        right
        apply threeK2_endpoint_only_blocker_mem_base hVertices hBRows hPairs hTK
        intro y hyT
        have hyRange := hTRange hyT
        rw [Finset.mem_insert] at hyRange
        rcases hyRange with hyx | hyV
        · exact (hxT (hyx ▸ hyT)).elim
        · exact hyV
    have hUpper := Finset.card_le_card hBlockerSubset
    rw [hBCard, Finset.card_insert_of_notMem hUNotBase, hBaseCard] at hUpper
    omega
  · have hBlockerSubset : blocker K ⊆ Base := by
      intro T hTK
      apply threeK2_endpoint_only_blocker_mem_base hVertices hBRows hPairs hTK
      intro x hxT
      by_contra hxV
      have hxInactive : ∀ R ∈ K, x ∉ R := by
        intro R hRK hxR
        exact hOutside ⟨x, hxV, R, hRK, hxR⟩
      exact (mem_blocker.mp hTK).avoids_inactive hxInactive hxT
    have hUpper := Finset.card_le_card hBlockerSubset
    rw [hBCard, hBaseCard] at hUpper
    omega

theorem threeK2_pairGraph_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : Hypergraph α}
    (hH : IsClutter H)
    (hHcard : H.card = 8)
    (hHRows : RowsCardAtLeast H 2)
    (hHDegree : MaxDegreeAtMost H 3)
    (hDualCard : (blocker H).card = 5)
    (_hDualRows : RowsCardAtLeast (blocker H) 3)
    (hDualDegree : MaxDegreeAtMost (blocker H) 3)
    (hShape : HasPairGraphThreeK2 H) :
    False := by
  let K := blocker H
  have hBlockerK : blocker K = H := by
    simpa [K] using blocker_involution hH
  have hKcard : K.card = 5 := by simpa [K] using hDualCard
  have hKDegree : MaxDegreeAtMost K 3 := by simpa [K] using hDualDegree
  have hBcard : (blocker K).card = 8 := by rw [hBlockerK, hHcard]
  have hBRows : RowsCardAtLeast (blocker K) 2 := by
    rw [hBlockerK]
    exact hHRows
  have hBDegree : MaxDegreeAtMost (blocker K) 3 := by
    rw [hBlockerK]
    exact hHDegree
  obtain ⟨a, b, c, d, e, f, hVertices, hPairs⟩ := hShape
  have hKPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}} := by
    rw [hBlockerK]
    exact hPairs
  obtain ⟨R0, R1, R2, R3, R4, hK, -⟩ :=
    exists_five_distinct_rows_of_card_eq_five hKcard
  have hRowsCard : ({R0, R1, R2, R3, R4} : Hypergraph α).card = 5 := by
    rw [← hK]
    exact hKcard
  have hKDegreeRows :
      MaxDegreeAtMost ({R0, R1, R2, R3, R4} : Hypergraph α) 3 := by
    rw [← hK]
    exact hKDegree
  have hBcardRows :
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)).card = 8 := by
    rw [← hK]
    exact hBcard
  have hBRowsRows : RowsCardAtLeast
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 2 := by
    rw [← hK]
    exact hBRows
  have hBDegreeRows : MaxDegreeAtMost
      (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) 3 := by
    rw [← hK]
    exact hBDegree
  have hPairsRows :
      pairRows (blocker ({R0, R1, R2, R3, R4} : Hypergraph α)) =
        {{a, b}, {c, d}, {e, f}} := by
    rw [← hK]
    exact hKPairs
  have hCount := threeK2_endpoint_triple_count_cases hVertices hRowsCard
    hBRowsRows hBDegreeRows hPairsRows
  rcases hCount with hThree | hFour
  · exact threeK2_three_good_impossible_of_rows hRowsCard hVertices
      hKDegreeRows hBcardRows hBRowsRows hBDegreeRows hPairsRows hThree
  · exact threeK2_four_good_impossible_of_rows hRowsCard hVertices
      hKDegreeRows hBcardRows hBRowsRows hBDegreeRows hPairsRows hFour

end AiMathLab.P0054.G413
