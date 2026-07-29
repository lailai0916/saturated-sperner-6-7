import AiMathLab.P0054G413.PairGraphs.P3K2
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

namespace AiMathLab.P0054.G413

theorem pairwise_ne_of_sext_card_eq_six {α : Type*} [DecidableEq α]
    {a b c d e f : α} (hCard : ({a, b, c, d, e, f} : Row α).card = 6) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  have card_five_ne_six (v w x y z : α) : ({v, w, x, y, z} : Row α).card ≠ 6 := by
    have hUpper : ({v, w, x, y, z} : Row α).card ≤ 5 := Finset.card_le_five
    omega
  constructor
  · intro h
    subst b
    exact card_five_ne_six a c d e f (by simpa using hCard)
  constructor
  · intro h
    subst c
    exact card_five_ne_six b a d e f (by simpa using hCard)
  constructor
  · intro h
    subst d
    exact card_five_ne_six b c a e f (by simpa using hCard)
  constructor
  · intro h
    subst e
    exact card_five_ne_six b c d a f (by simpa using hCard)
  constructor
  · intro h
    subst f
    exact card_five_ne_six b c d e a (by simpa using hCard)
  constructor
  · intro h
    subst c
    exact card_five_ne_six a b d e f (by simpa using hCard)
  constructor
  · intro h
    subst d
    exact card_five_ne_six a c b e f (by simpa using hCard)
  constructor
  · intro h
    subst e
    exact card_five_ne_six a c d b f (by simpa using hCard)
  constructor
  · intro h
    subst f
    exact card_five_ne_six a c d e b (by simpa using hCard)
  constructor
  · intro h
    subst d
    exact card_five_ne_six a b c e f (by simpa using hCard)
  constructor
  · intro h
    subst e
    exact card_five_ne_six a b d c f (by simpa using hCard)
  constructor
  · intro h
    subst f
    exact card_five_ne_six a b d e c (by simpa using hCard)
  constructor
  · intro h
    subst e
    exact card_five_ne_six a b c d f (by simpa using hCard)
  constructor
  · intro h
    subst f
    exact card_five_ne_six a b c e d (by simpa using hCard)
  · intro h
    subst f
    exact card_five_ne_six a b c d e (by simpa using hCard)

def threeK2EndpointTriples {α : Type*} [DecidableEq α]
    (a b c d e f : α) : Hypergraph α :=
  {{a, c, e}, {a, c, f}, {a, d, e}, {a, d, f},
    {b, c, e}, {b, c, f}, {b, d, e}, {b, d, f}}

def threeK2OppositeTriple {α : Type*} [DecidableEq α]
    (a b c d e f : α) (R : Row α) : Row α :=
  {if a ∈ R then b else a, if c ∈ R then d else c, if e ∈ R then f else e}

abbrev BoolCube := Bool × Bool × Bool

def threeK2Code {α : Type*} [DecidableEq α]
    (a c e : α) (T : Row α) : BoolCube :=
  (decide (a ∈ T), decide (c ∈ T), decide (e ∈ T))

def threeK2Decode {α : Type*} [DecidableEq α]
    (a b c d e f : α) (q : BoolCube) : Row α :=
  {if q.1 then a else b, if q.2.1 then c else d, if q.2.2 then e else f}

def boolCubeClass (m : BoolCube) : Finset BoolCube :=
  {m, (m.1, !m.2.1, !m.2.2), (!m.1, m.2.1, !m.2.2),
    (!m.1, !m.2.1, m.2.2)}

def boolCubePuncturedClass (m : BoolCube) : Finset BoolCube :=
  {(m.1, !m.2.1, !m.2.2), (!m.1, m.2.1, !m.2.2),
    (!m.1, !m.2.1, m.2.2)}

def boolCubePairCovered (S : Finset BoolCube) : Bool :=
  decide ((false, false, false) ∈ S ∨ (false, false, true) ∈ S) &&
  decide ((false, true, false) ∈ S ∨ (false, true, true) ∈ S) &&
  decide ((true, false, false) ∈ S ∨ (true, false, true) ∈ S) &&
  decide ((true, true, false) ∈ S ∨ (true, true, true) ∈ S) &&
  decide ((false, false, false) ∈ S ∨ (false, true, false) ∈ S) &&
  decide ((false, false, true) ∈ S ∨ (false, true, true) ∈ S) &&
  decide ((true, false, false) ∈ S ∨ (true, true, false) ∈ S) &&
  decide ((true, false, true) ∈ S ∨ (true, true, true) ∈ S) &&
  decide ((false, false, false) ∈ S ∨ (true, false, false) ∈ S) &&
  decide ((false, false, true) ∈ S ∨ (true, false, true) ∈ S) &&
  decide ((false, true, false) ∈ S ∨ (true, true, false) ∈ S) &&
  decide ((false, true, true) ∈ S ∨ (true, true, true) ∈ S)

set_option maxRecDepth 100000 in
theorem boolCube_pairCovered_classification :
    ∀ Good : Finset BoolCube,
      boolCubePairCovered (Finset.univ \ Good) = true →
      (Good.card = 3 → ∃ m, Good = boolCubePuncturedClass m) ∧
      (Good.card = 4 → ∃ m, Good = boolCubeClass m) := by
  decide

abbrev FiveSupport := Finset (Fin 5)

def IsValidFiveSupportPair (P : FiveSupport × FiveSupport) : Prop :=
  P.1 ∪ P.2 = Finset.univ ∧
    P.1.card ≤ 3 ∧ P.2.card ≤ 3 ∧
    P.1 \ P.2 ≠ ∅ ∧ P.2 \ P.1 ≠ ∅

instance : DecidablePred IsValidFiveSupportPair := fun P ↦ by
  unfold IsValidFiveSupportPair
  infer_instance

abbrev ValidFiveSupportPair :=
  {P : FiveSupport × FiveSupport // IsValidFiveSupportPair P}

def selectFiveSupport (P : ValidFiveSupportPair) (b : Bool) : FiveSupport :=
  if b then P.1.1 else P.1.2

def ThreeK2FiveSupportsCompatible
    (P Q R : ValidFiveSupportPair) : Prop :=
  ∀ p q : Bool, selectFiveSupport P p ∪ selectFiveSupport Q q ≠ Finset.univ ∧
    selectFiveSupport P p ∪ selectFiveSupport R q ≠ Finset.univ ∧
    selectFiveSupport Q p ∪ selectFiveSupport R q ≠ Finset.univ

instance (P Q R : ValidFiveSupportPair) :
    Decidable (ThreeK2FiveSupportsCompatible P Q R) := by
  unfold ThreeK2FiveSupportsCompatible
  infer_instance

def threeK2FiniteGood
    (P Q R : ValidFiveSupportPair) : Finset BoolCube :=
  Finset.univ.filter fun b ↦
    selectFiveSupport P b.1 ∪ selectFiveSupport Q b.2.1 ∪
      selectFiveSupport R b.2.2 = Finset.univ

def HasThreeK2RowWitness
    (P Q R : ValidFiveSupportPair) : Prop :=
  ∃ i : Fin 5, ∃ x y : Fin 3 × Bool,
    x.1 ≠ y.1 ∧
      (match x.1 with
        | 0 => selectFiveSupport P x.2
        | 1 => selectFiveSupport Q x.2
        | 2 => selectFiveSupport R x.2) ∪
      (match y.1 with
        | 0 => selectFiveSupport P y.2
        | 1 => selectFiveSupport Q y.2
        | 2 => selectFiveSupport R y.2) = Finset.univ.erase i

instance (P Q R : ValidFiveSupportPair) :
    Decidable (HasThreeK2RowWitness P Q R) := by
  unfold HasThreeK2RowWitness
  infer_instance

def boolCubeComplement (q : BoolCube) : BoolCube :=
  (!q.1, !q.2.1, !q.2.2)

def supportRowCode
    (P Q R : ValidFiveSupportPair) (i : Fin 5) : BoolCube :=
  (decide (i ∈ selectFiveSupport P true),
    decide (i ∈ selectFiveSupport Q true),
    decide (i ∈ selectFiveSupport R true))

def threeK2FiniteRowCodes
    (P Q R : ValidFiveSupportPair) : Finset BoolCube :=
  Finset.univ.image (supportRowCode P Q R)

def threeK2AsymmetricRows (m : BoolCube) : Finset BoolCube :=
  insert m (insert (boolCubeComplement m) (boolCubePuncturedClass m))

def IsThreeK2AsymmetricSupportSystem
    (P Q R : ValidFiveSupportPair) : Prop :=
  ∃ m : BoolCube,
    threeK2FiniteGood P Q R = boolCubePuncturedClass m ∧
      (∀ i : Fin 5,
        (i ∈ selectFiveSupport P true ↔ i ∉ selectFiveSupport P false) ∧
        (i ∈ selectFiveSupport Q true ↔ i ∉ selectFiveSupport Q false) ∧
        (i ∈ selectFiveSupport R true ↔ i ∉ selectFiveSupport R false)) ∧
      threeK2FiniteRowCodes P Q R = threeK2AsymmetricRows m

instance (P Q R : ValidFiveSupportPair) :
    Decidable (IsThreeK2AsymmetricSupportSystem P Q R) := by
  unfold IsThreeK2AsymmetricSupportSystem
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
-- The valid subtype reduces the exhaustive check to 50^3 support triples.
theorem threeK2_finite_support_classification :
    ∀ P Q R : ValidFiveSupportPair,
      ThreeK2FiveSupportsCompatible P Q R →
      ((threeK2FiniteGood P Q R).card = 4 →
        HasThreeK2RowWitness P Q R) ∧
      ((threeK2FiniteGood P Q R).card = 3 →
        IsThreeK2AsymmetricSupportSystem P Q R) := by
  decide

theorem threeK2_finite_four_good_has_row_witness
    (P Q R : ValidFiveSupportPair)
    (hCompatible : ThreeK2FiveSupportsCompatible P Q R)
    (hGood : (threeK2FiniteGood P Q R).card = 4) :
    HasThreeK2RowWitness P Q R :=
  (threeK2_finite_support_classification P Q R hCompatible).1 hGood

theorem threeK2_finite_three_good_asymmetric
    (P Q R : ValidFiveSupportPair)
    (hCompatible : ThreeK2FiveSupportsCompatible P Q R)
    (hGood : (threeK2FiniteGood P Q R).card = 3) :
    IsThreeK2AsymmetricSupportSystem P Q R :=
  (threeK2_finite_support_classification P Q R hCompatible).2 hGood

def finiteIsTransversal {n : Nat}
    (H : Hypergraph (Fin n)) (T : Row (Fin n)) : Bool :=
  decide (∀ E ∈ H, ¬Disjoint T E)

def endpointInBoolCube (x : Fin 6) (q : BoolCube) : Bool :=
  if x = 0 then q.1
  else if x = 1 then !q.1
  else if x = 2 then q.2.1
  else if x = 3 then !q.2.1
  else if x = 4 then q.2.2
  else !q.2.2

def asymmetricRowsSeven
    (m : BoolCube) (X : Finset BoolCube) : Hypergraph (Fin 7) :=
  (threeK2AsymmetricRows m).image fun q ↦ Finset.univ.filter fun x ↦
    if hx : x.val < 6 then endpointInBoolCube ⟨x.val, hx⟩ q else q ∈ X

def finitePrivateBlockerCertificate {n : Nat}
    (H : Hypergraph (Fin n)) (T : Row (Fin n)) : Bool :=
  finiteIsTransversal H T &&
    decide (∀ x ∈ T, ∃ E ∈ H, T ∩ E = {x})

def HasAsymmetricOutsideObstruction
    (m : BoolCube) (X : Finset BoolCube) : Prop :=
  ∃ T : Row (Fin 7),
    6 ∈ T ∧
      finitePrivateBlockerCertificate (asymmetricRowsSeven m X) T = true ∧
      (T.card = 2 ∨ ∃ x : Fin 6, x.castLE (by omega) ∈ T ∧
        endpointInBoolCube x (boolCubeComplement m) = true)

instance (m : BoolCube) (X : Finset BoolCube) :
    Decidable (HasAsymmetricOutsideObstruction m X) := by
  unfold HasAsymmetricOutsideObstruction
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
-- Each illegal outside support has a private-row obstruction certificate.
theorem threeK2_asymmetric_outside_obstruction :
    ∀ m : BoolCube, ∀ X : Finset BoolCube,
      X ⊆ threeK2AsymmetricRows m →
      X ≠ ∅ → X.card ≤ 3 →
      X ≠ {boolCubeComplement m} →
      HasAsymmetricOutsideObstruction m X := by
  decide

noncomputable def threeK2TransversalTriples {α : Type*}
    [Fintype α] [DecidableEq α]
    (K : Hypergraph α) (a b c d e f : α) : Hypergraph α := by
  classical
  exact (threeK2EndpointTriples a b c d e f).filter (IsTransversal K)

set_option maxHeartbeats 1000000 in
theorem threeK2_endpoint_triples_card {α : Type*} [DecidableEq α]
    {a b c d e f : α} (hVertices : ({a, b, c, d, e, f} : Row α).card = 6) :
    (threeK2EndpointTriples a b c d e f).card = 8 := by
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
  let E := threeK2EndpointTriples a b c d e f
  let code : Row α → BoolCube := threeK2Code a c e
  let decode : BoolCube → Row α := threeK2Decode a b c d e f
  have hDecodeCode : ∀ T ∈ E, decode (code T) = T := by
    intro T hTE
    simp only [E, threeK2EndpointTriples, Finset.mem_insert,
      Finset.mem_singleton] at hTE
    rcases hTE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [decode, code, threeK2Code, threeK2Decode]
  have hInj : Set.InjOn code E := by
    intro T hTE U hUE hCode
    rw [← hDecodeCode T hTE, ← hDecodeCode U hUE, hCode]
  let codes : Finset (Bool × Bool × Bool) :=
    {(true, true, true), (true, true, false),
      (true, false, true), (true, false, false),
      (false, true, true), (false, true, false),
      (false, false, true), (false, false, false)}
  have hImage : E.image code = codes := by
    ext x
    rcases x with ⟨i, j, k⟩
    cases i <;> cases j <;> cases k <;>
      simp_all [E, code, codes, threeK2Code, threeK2EndpointTriples]
  have hCardImage : (E.image code).card = 8 := by rw [hImage]; decide
  rw [Finset.card_image_iff.mpr hInj] at hCardImage
  exact hCardImage

theorem threeK2_fixed_pairs_not_subset_endpoint_triple {α : Type*}
    [DecidableEq α] {a b c d e f : α} {T : Row α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hT : T ∈ threeK2EndpointTriples a b c d e f) :
    ¬({a, b} : Row α) ⊆ T ∧ ¬({c, d} : Row α) ⊆ T ∧
      ¬({e, f} : Row α) ⊆ T := by
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
  simp only [threeK2EndpointTriples, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Finset.subset_iff]

theorem threeK2_transversal_endpoint_triple_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α} {T : Row α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}})
    (hTEndpoint : T ∈ threeK2EndpointTriples a b c d e f)
    (hTTransversal : IsTransversal K T) :
    T ∈ blocker K := by
  obtain ⟨S, hST, hSMinimal⟩ := exists_minimalTransversal_subset hTTransversal
  have hSBlocker : S ∈ blocker K := mem_blocker.mpr hSMinimal
  have hSLower : 2 ≤ S.card := hBRows S hSBlocker
  have hTCard : T.card = 3 := by
    obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
        hcd, hce, hcf, hde, hdf, hef⟩ :=
      pairwise_ne_of_sext_card_eq_six hVertices
    simp only [threeK2EndpointTriples, Finset.mem_insert,
      Finset.mem_singleton] at hTEndpoint
    rcases hTEndpoint with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
        hcd, hce, hcf, hde, hdf, hef]
  have hSUpper : S.card ≤ 3 := by
    rw [← hTCard]
    exact Finset.card_le_card hST
  by_cases hSCard : S.card = 3
  · have hSTCard : T.card ≤ S.card := by omega
    have hEq : S = T := Finset.eq_of_subset_of_card_le hST hSTCard
    exact hEq ▸ hSBlocker
  have hSCardTwo : S.card = 2 := by omega
  have hSPair : S ∈ pairRows (blocker K) :=
    Finset.mem_filter.mpr ⟨hSBlocker, hSCardTwo⟩
  rw [hPairs] at hSPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hSPair
  obtain ⟨hAB, hCD, hEF⟩ :=
    threeK2_fixed_pairs_not_subset_endpoint_triple hVertices hTEndpoint
  rcases hSPair with rfl | rfl | rfl
  · exact (hAB hST).elim
  · exact (hCD hST).elim
  · exact (hEF hST).elim

theorem threeK2_endpoint_triple_card {α : Type*} [DecidableEq α]
    {a b c d e f : α} (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    {T : Row α} (hT : T ∈ threeK2EndpointTriples a b c d e f) :
    T.card = 3 := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  simp only [threeK2EndpointTriples, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef]

theorem threeK2_missed_triple_eq_opposite {α : Type*} [DecidableEq α]
    {a b c d e f : α} {R T : Row α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hAB : a ∈ R ∨ b ∈ R) (hCD : c ∈ R ∨ d ∈ R) (hEF : e ∈ R ∨ f ∈ R)
    (hT : T ∈ threeK2EndpointTriples a b c d e f)
    (hDisjoint : Disjoint T R) :
    T = threeK2OppositeTriple a b c d e f R := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    pairwise_ne_of_sext_card_eq_six hVertices
  simp only [threeK2EndpointTriples, Finset.mem_insert, Finset.mem_singleton] at hT
  simp only [Finset.disjoint_left] at hDisjoint
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [threeK2OppositeTriple]

theorem threeK2_at_least_three_endpoint_triples {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKcard : K.card = 5)
    (hAB : ({a, b} : Row α) ∈ blocker K)
    (hCD : ({c, d} : Row α) ∈ blocker K)
    (hEF : ({e, f} : Row α) ∈ blocker K) :
    3 ≤ (threeK2TransversalTriples K a b c d e f).card := by
  classical
  let E := threeK2EndpointTriples a b c d e f
  let Good := threeK2TransversalTriples K a b c d e f
  let Bad := E \ Good
  let opposite : Row α → Row α := threeK2OppositeTriple a b c d e f
  have hBadSubset : Bad ⊆ K.image opposite := by
    intro T hTBad
    obtain ⟨hTE, hTGood⟩ := Finset.mem_sdiff.mp hTBad
    have hNotTransversal : ¬ IsTransversal K T := by
      intro hTransversal
      exact hTGood (by
        simp only [Good, threeK2TransversalTriples, Finset.mem_filter]
        exact ⟨hTE, hTransversal⟩)
    simp only [IsTransversal] at hNotTransversal
    push_neg at hNotTransversal
    obtain ⟨R, hRK, hNoHit⟩ := hNotTransversal
    have hABHit : a ∈ R ∨ b ∈ R := by
      obtain ⟨x, hxPair, hxR⟩ := (mem_blocker.mp hAB).prop R hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with rfl | rfl
      · exact Or.inl hxR
      · exact Or.inr hxR
    have hCDHit : c ∈ R ∨ d ∈ R := by
      obtain ⟨x, hxPair, hxR⟩ := (mem_blocker.mp hCD).prop R hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with rfl | rfl
      · exact Or.inl hxR
      · exact Or.inr hxR
    have hEFHit : e ∈ R ∨ f ∈ R := by
      obtain ⟨x, hxPair, hxR⟩ := (mem_blocker.mp hEF).prop R hRK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with rfl | rfl
      · exact Or.inl hxR
      · exact Or.inr hxR
    have hDisjoint : Disjoint T R := Finset.disjoint_left.mpr fun x hxT hxR ↦
      hNoHit x hxT hxR
    exact Finset.mem_image.mpr ⟨R, hRK,
      (threeK2_missed_triple_eq_opposite hVertices hABHit hCDHit hEFHit
        hTE hDisjoint).symm⟩
  have hBadUpper : Bad.card ≤ 5 := by
    calc
      Bad.card ≤ (K.image opposite).card := Finset.card_le_card hBadSubset
      _ ≤ K.card := Finset.card_image_le
      _ = 5 := hKcard
  have hGoodSubset : Good ⊆ E := by
    intro T hT
    change T ∈ (E.filter (IsTransversal K)) at hT
    exact (Finset.mem_filter.mp hT).1
  have hPartition : Good ∪ Bad = E := by
    exact Finset.union_sdiff_of_subset hGoodSubset
  have hDisjoint : Disjoint Good Bad := Finset.disjoint_sdiff
  have hCardSum : Good.card + Bad.card = 8 := by
    rw [← Finset.card_union_of_disjoint hDisjoint, hPartition]
    exact threeK2_endpoint_triples_card hVertices
  change 3 ≤ Good.card
  omega

theorem threeK2_transversal_triples_subset_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}}) :
    threeK2TransversalTriples K a b c d e f ⊆ blocker K := by
  classical
  intro T hT
  obtain ⟨hTEndpoint, hTTransversal⟩ := Finset.mem_filter.mp hT
  exact threeK2_transversal_endpoint_triple_mem_blocker hVertices hBRows hPairs
    hTEndpoint hTTransversal

theorem threeK2_at_most_four_endpoint_triples {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}}) :
    (threeK2TransversalTriples K a b c d e f).card ≤ 4 := by
  classical
  let Good := threeK2TransversalTriples K a b c d e f
  have hGoodEndpoint : Good ⊆ threeK2EndpointTriples a b c d e f := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hGoodBlocker : Good ⊆ blocker K := by
    exact threeK2_transversal_triples_subset_blocker hVertices hBRows hPairs
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
    have hxInsert : degree (insert ({x, y} : Row α) Good) x = degree Good x + 1 :=
      degree_insert_of_notMem hPairNotGood (by simp)
    have hyInsert : degree (insert ({x, y} : Row α) Good) y = degree Good y + 1 :=
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
  change Good.card ≤ 4
  omega

theorem threeK2_endpoint_triple_count_cases {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {a b c d e f : α}
    (hVertices : ({a, b, c, d, e, f} : Row α).card = 6)
    (hKcard : K.card = 5)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBDegree : MaxDegreeAtMost (blocker K) 3)
    (hPairs : pairRows (blocker K) = {{a, b}, {c, d}, {e, f}}) :
    (threeK2TransversalTriples K a b c d e f).card = 3 ∨
      (threeK2TransversalTriples K a b c d e f).card = 4 := by
  have hAB : ({a, b} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hCD : ({c, d} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hEF : ({e, f} : Row α) ∈ blocker K :=
    (pair_mem_of_mem_pairRows (by rw [hPairs]; simp)).1
  have hLower := threeK2_at_least_three_endpoint_triples hVertices hKcard hAB hCD hEF
  have hUpper := threeK2_at_most_four_endpoint_triples
    hVertices hBRows hBDegree hPairs
  omega

end AiMathLab.P0054.G413
