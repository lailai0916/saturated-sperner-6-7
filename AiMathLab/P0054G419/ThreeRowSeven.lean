import AiMathLab.P0054G413.ThreeRowExact
import Mathlib

namespace AiMathLab.P0054.G419

open G413

def threeSupportMask {α : Type*} [DecidableEq α]
    (A B C : Row α) (x : α) : Nat :=
  (if x ∈ A then 1 else 0) +
    (if x ∈ B then 2 else 0) +
    (if x ∈ C then 4 else 0)

theorem threeSupportMask_privatePart_first {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ privatePart A B C) :
    threeSupportMask A B C x = 1 := by
  obtain ⟨hxA, hxBC⟩ := Finset.mem_sdiff.mp hx
  have hxB : x ∉ B := fun h ↦ hxBC (Finset.mem_union_left C h)
  have hxC : x ∉ C := fun h ↦ hxBC (Finset.mem_union_right B h)
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeSupportMask_privatePart_second {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ privatePart B A C) :
    threeSupportMask A B C x = 2 := by
  obtain ⟨hxB, hxAC⟩ := Finset.mem_sdiff.mp hx
  have hxA : x ∉ A := fun h ↦ hxAC (Finset.mem_union_left C h)
  have hxC : x ∉ C := fun h ↦ hxAC (Finset.mem_union_right A h)
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeSupportMask_privatePart_third {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ privatePart C A B) :
    threeSupportMask A B C x = 4 := by
  obtain ⟨hxC, hxAB⟩ := Finset.mem_sdiff.mp hx
  have hxA : x ∉ A := fun h ↦ hxAB (Finset.mem_union_left B h)
  have hxB : x ∉ B := fun h ↦ hxAB (Finset.mem_union_right A h)
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeSupportMask_sharedPart_twelve {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ sharedPart A B C) :
    threeSupportMask A B C x = 3 := by
  obtain ⟨hxAB, hxC⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hxAB
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeSupportMask_sharedPart_thirteen {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ sharedPart A C B) :
    threeSupportMask A B C x = 5 := by
  obtain ⟨hxAC, hxB⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hxA, hxC⟩ := Finset.mem_inter.mp hxAC
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeSupportMask_sharedPart_twentyThree {α : Type*} [DecidableEq α]
    {A B C : Row α} {x : α} (hx : x ∈ sharedPart B C A) :
    threeSupportMask A B C x = 6 := by
  obtain ⟨hxBC, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hxB, hxC⟩ := Finset.mem_inter.mp hxBC
  simp [threeSupportMask, hxA, hxB, hxC]

theorem threeRows_first_partition {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    A = privatePart A B C ∪ sharedPart A B C ∪ sharedPart A C B := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C
  all_goals simp_all [privatePart, sharedPart]

theorem threeRows_second_partition {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    B = privatePart B A C ∪ sharedPart A B C ∪ sharedPart B C A := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C
  all_goals simp_all [privatePart, sharedPart]

theorem threeRows_third_partition {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    C = privatePart C A B ∪ sharedPart A C B ∪ sharedPart B C A := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C
  all_goals simp_all [privatePart, sharedPart]

theorem threePart_union_card {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    A.card =
      (privatePart A B C).card +
        (sharedPart A B C).card +
        (sharedPart A C B).card := by
  let P := privatePart A B C
  let X := sharedPart A B C
  let Y := sharedPart A C B
  have hPartition : A = P ∪ X ∪ Y := by
    simpa [P, X, Y] using threeRows_first_partition hNoCommon
  have hPrivateShared :
      Disjoint P X := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxX
    exact (Finset.mem_sdiff.mp hxP).2
      (Finset.mem_union_left C (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxX).1).2)
  have hPrivateShared' :
      Disjoint P Y := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxY
    exact (Finset.mem_sdiff.mp hxP).2
      (Finset.mem_union_right B (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxY).1).2)
  have hShared : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxY
    exact (Finset.mem_sdiff.mp hxX).2
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxY).1).2
  have hUnionDisjoint : Disjoint (P ∪ X) Y := by
    apply Finset.disjoint_left.mpr
    intro x hxPX hxY
    rcases Finset.mem_union.mp hxPX with hxP | hxX
    · exact Finset.disjoint_left.mp hPrivateShared' hxP hxY
    · exact Finset.disjoint_left.mp hShared hxX hxY
  calc
    A.card = (P ∪ X ∪ Y).card := congrArg Finset.card hPartition
    _ = (P ∪ X).card + Y.card := Finset.card_union_of_disjoint hUnionDisjoint
    _ = P.card + X.card + Y.card := by
      rw [Finset.card_union_of_disjoint hPrivateShared]
    _ = (privatePart A B C).card +
        (sharedPart A B C).card +
        (sharedPart A C B).card := by rfl

theorem threePart_union_card_second {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    B.card =
      (privatePart B A C).card +
        (sharedPart A B C).card +
        (sharedPart B C A).card := by
  have h := threePart_union_card (A := B) (B := A) (C := C) (by
    intro x hx
    exact hNoCommon x ⟨hx.2.1, hx.1, hx.2.2⟩)
  simpa [privatePart, sharedPart, Finset.inter_comm] using h

theorem threePart_union_card_third {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hNoCommon : ∀ x, ¬(x ∈ A ∧ x ∈ B ∧ x ∈ C)) :
    C.card =
      (privatePart C A B).card +
        (sharedPart A C B).card +
        (sharedPart B C A).card := by
  have h := threePart_union_card (A := C) (B := A) (C := B) (by
    intro x hx
    exact hNoCommon x ⟨hx.2.1, hx.2.2, hx.1⟩)
  simpa [privatePart, sharedPart, Finset.inter_comm, Finset.union_comm] using h

def threePairFirstCode (i : Fin 6) : Nat :=
  if i = 0 then 3
  else if i = 1 then 3
  else if i = 2 then 5
  else if i = 3 then 3
  else if i = 4 then 5
  else 6

def threePairSecondCode (i : Fin 6) : Nat :=
  if i = 0 then 5
  else if i = 1 then 6
  else if i = 2 then 6
  else if i = 3 then 4
  else if i = 4 then 2
  else 1

def threePairCode (i : Fin 6) : Finset Nat :=
  {threePairFirstCode i, threePairSecondCode i}

theorem threePairCode_injective : Function.Injective threePairCode := by
  intro i j h
  have h1 := congrArg (fun s : Finset Nat ↦ 1 ∈ s) h
  have h2 := congrArg (fun s : Finset Nat ↦ 2 ∈ s) h
  have h3 := congrArg (fun s : Finset Nat ↦ 3 ∈ s) h
  have h4 := congrArg (fun s : Finset Nat ↦ 4 ∈ s) h
  have h5 := congrArg (fun s : Finset Nat ↦ 5 ∈ s) h
  have h6 := congrArg (fun s : Finset Nat ↦ 6 ∈ s) h
  fin_cases i <;> fin_cases j <;>
    simp [threePairCode, threePairFirstCode, threePairSecondCode] at h1 h2 h3 h4 h5 h6 ⊢

theorem threePairCodes_ne (i : Fin 6) :
    threePairFirstCode i ≠ threePairSecondCode i := by
  fin_cases i <;> simp [threePairFirstCode, threePairSecondCode]

def threePairDomain {α : Type*} [DecidableEq α]
    (A B C : Row α) (i : Fin 6) : Finset (α × α) :=
  let P := privatePart A B C
  let Q := privatePart B A C
  let R := privatePart C A B
  let X := sharedPart A B C
  let Y := sharedPart A C B
  let Z := sharedPart B C A
  if i = 0 then X.product Y
  else if i = 1 then X.product Z
  else if i = 2 then Y.product Z
  else if i = 3 then X.product R
  else if i = 4 then Y.product Q
  else Z.product P

def threePairChoices {α : Type*} [DecidableEq α]
    (A B C : Row α) : Finset (Σ _i : Fin 6, α × α) :=
  Finset.univ.sigma (threePairDomain A B C)

def threePairChoiceRow {α : Type*} [DecidableEq α]
    (q : Σ _i : Fin 6, α × α) : Row α :=
  {q.2.1, q.2.2}

theorem threePairChoice_support_codes {α : Type*} [DecidableEq α]
    {A B C : Row α} {q : Σ _i : Fin 6, α × α}
    (hq : q ∈ threePairChoices A B C) :
    threeSupportMask A B C q.2.1 = threePairFirstCode q.1 ∧
      threeSupportMask A B C q.2.2 = threePairSecondCode q.1 := by
  cases q with
  | mk i p =>
      have hDomain := (Finset.mem_sigma.mp hq).2
      fin_cases i
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_twelve hFirst,
          threeSupportMask_sharedPart_thirteen hSecond⟩
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_twelve hFirst,
          threeSupportMask_sharedPart_twentyThree hSecond⟩
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_thirteen hFirst,
          threeSupportMask_sharedPart_twentyThree hSecond⟩
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_twelve hFirst,
          threeSupportMask_privatePart_third hSecond⟩
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_thirteen hFirst,
          threeSupportMask_privatePart_second hSecond⟩
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact ⟨threeSupportMask_sharedPart_twentyThree hFirst,
          threeSupportMask_privatePart_first hSecond⟩

theorem ordered_pair_eq_of_distinct_codes {α : Type*} [DecidableEq α]
    (f : α → Nat) {u v u' v' : α} {a b : Nat}
    (hu : f u = a) (hv : f v = b)
    (hu' : f u' = a) (hv' : f v' = b)
    (hab : a ≠ b) (hRow : ({u, v} : Row α) = {u', v'}) :
    u = u' ∧ v = v' := by
  have huMem : u ∈ ({u', v'} : Row α) := by rw [← hRow]; simp
  have hvMem : v ∈ ({u', v'} : Row α) := by rw [← hRow]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at huMem hvMem
  have huu' : u = u' := by
    rcases huMem with huu' | huv'
    · exact huu'
    · exfalso
      apply hab
      calc
        a = f u := hu.symm
        _ = f v' := congrArg f huv'
        _ = b := hv'
  have hvv' : v = v' := by
    rcases hvMem with hvu' | hvv'
    · exfalso
      apply hab
      calc
        a = f u' := hu'.symm
        _ = f v := congrArg f hvu'.symm
        _ = b := hv
    · exact hvv'
  exact ⟨huu', hvv'⟩

theorem threePairChoiceRow_code {α : Type*} [DecidableEq α]
    {A B C : Row α} {q : Σ _i : Fin 6, α × α}
    (hq : q ∈ threePairChoices A B C) :
    (threePairChoiceRow q).image (threeSupportMask A B C) = threePairCode q.1 := by
  obtain ⟨hFirst, hSecond⟩ := threePairChoice_support_codes hq
  simp [threePairChoiceRow, threePairCode, hFirst, hSecond]

theorem threePairChoiceRow_injective {α : Type*} [DecidableEq α]
    (A B C : Row α) :
    Set.InjOn threePairChoiceRow
      (↑(threePairChoices A B C) : Set (Σ _i : Fin 6, α × α)) := by
  intro q hq r hr hRows
  have hCode : threePairCode q.1 = threePairCode r.1 := by
    calc
      threePairCode q.1 = (threePairChoiceRow q).image (threeSupportMask A B C) :=
        (threePairChoiceRow_code hq).symm
      _ = (threePairChoiceRow r).image (threeSupportMask A B C) := by rw [hRows]
      _ = threePairCode r.1 := threePairChoiceRow_code hr
  have hIndex : q.1 = r.1 := threePairCode_injective hCode
  cases q with
  | mk i p =>
      cases r with
      | mk j s =>
          simp only at hIndex
          subst j
          obtain ⟨hpFirst, hpSecond⟩ := threePairChoice_support_codes hq
          obtain ⟨hsFirst, hsSecond⟩ := threePairChoice_support_codes hr
          change ({p.1, p.2} : Row α) = {s.1, s.2} at hRows
          have hPair := ordered_pair_eq_of_distinct_codes
            (threeSupportMask A B C) hpFirst hpSecond hsFirst hsSecond
            (threePairCodes_ne i) hRows
          have hps : p = s := Prod.ext hPair.1 hPair.2
          subst s
          rfl

theorem threePairChoices_card {α : Type*} [DecidableEq α]
    (A B C : Row α) :
    (threePairChoices A B C).card =
      (sharedPart A B C).card * (sharedPart A C B).card +
      (sharedPart A B C).card * (sharedPart B C A).card +
      (sharedPart A C B).card * (sharedPart B C A).card +
      (sharedPart A B C).card * (privatePart C A B).card +
      (sharedPart A C B).card * (privatePart B A C).card +
      (sharedPart B C A).card * (privatePart A B C).card := by
  rw [threePairChoices, Finset.card_sigma]
  simp [threePairDomain, Finset.card_product, Fin.sum_univ_succ]
  omega

theorem threePairChoiceRow_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} {A B C : Row α}
    (hK : K = {A, B, C})
    {q : Σ _i : Fin 6, α × α}
    (hq : q ∈ threePairChoices A B C) :
    threePairChoiceRow q ∈ blocker K := by
  cases q with
  | mk i p =>
      have hDomain := (Finset.mem_sigma.mp hq).2
      fin_cases i
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_shared_pair_mem_blocker hK hFirst hSecond
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_shared_pair_mem_blocker
          (K := K) (T₁ := B) (T₂ := A) (T₃ := C)
          (by
            rw [hK]
            ext E
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto)
          (by simpa [sharedPart, Finset.inter_comm] using hFirst) hSecond
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_shared_pair_mem_blocker
          (K := K) (T₁ := C) (T₂ := A) (T₃ := B)
          (by
            rw [hK]
            ext E
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto)
          (by simpa [sharedPart, Finset.inter_comm] using hFirst)
          (by simpa [sharedPart, Finset.inter_comm] using hSecond)
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_private_pair_mem_blocker hK hFirst hSecond
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_private_pair_mem_blocker
          (K := K) (T₁ := A) (T₂ := C) (T₃ := B)
          (by
            rw [hK]
            ext E
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto) hFirst hSecond
      · obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp (by
          simpa [threePairChoices, threePairDomain] using hDomain)
        exact shared_private_pair_mem_blocker
          (K := K) (T₁ := B) (T₂ := C) (T₃ := A)
          (by
            rw [hK]
            ext E
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto) hFirst hSecond

theorem threePairChoiceRow_card {α : Type*} [DecidableEq α]
    {A B C : Row α} {q : Σ _i : Fin 6, α × α}
    (hq : q ∈ threePairChoices A B C) :
    (threePairChoiceRow q).card = 2 := by
  obtain ⟨hFirst, hSecond⟩ := threePairChoice_support_codes hq
  have hNe : q.2.1 ≠ q.2.2 := by
    intro hEq
    apply threePairCodes_ne q.1
    calc
      threePairFirstCode q.1 = threeSupportMask A B C q.2.1 := hFirst.symm
      _ = threeSupportMask A B C q.2.2 := by rw [hEq]
      _ = threePairSecondCode q.1 := hSecond
  simp [threePairChoiceRow, hNe]

theorem threePairGenerated_card_le_pairRows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} {A B C : Row α}
    (hK : K = {A, B, C}) :
    (sharedPart A B C).card * (sharedPart A C B).card +
      (sharedPart A B C).card * (sharedPart B C A).card +
      (sharedPart A C B).card * (sharedPart B C A).card +
      (sharedPart A B C).card * (privatePart C A B).card +
      (sharedPart A C B).card * (privatePart B A C).card +
      (sharedPart B C A).card * (privatePart A B C).card ≤
      (pairRows (blocker K)).card := by
  classical
  let generated := (threePairChoices A B C).image threePairChoiceRow
  have hGeneratedCard : generated.card =
      (sharedPart A B C).card * (sharedPart A C B).card +
      (sharedPart A B C).card * (sharedPart B C A).card +
      (sharedPart A C B).card * (sharedPart B C A).card +
      (sharedPart A B C).card * (privatePart C A B).card +
      (sharedPart A C B).card * (privatePart B A C).card +
      (sharedPart B C A).card * (privatePart A B C).card := by
    change ((threePairChoices A B C).image threePairChoiceRow).card = _
    rw [Finset.card_image_iff.mpr (threePairChoiceRow_injective A B C)]
    exact threePairChoices_card A B C
  have hGeneratedSubset : generated ⊆ pairRows (blocker K) := by
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_filter.mpr
      ⟨threePairChoiceRow_mem_blocker hK hq, threePairChoiceRow_card hq⟩
  rw [← hGeneratedCard]
  exact Finset.card_le_card hGeneratedSubset

theorem tripleChoiceRows_subset_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} {A B C : Row α}
    (hK : K = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    tripleChoiceRows
        (privatePart A B C)
        (privatePart B A C)
        (privatePart C A B) ⊆ blocker K := by
  intro T hT
  have hExact : T ∈ rowsCardExactly (blocker K) 3 := by
    rw [threeRow_triple_blockers hK hAB hAC hBC]
    exact hT
  exact (mem_rowsCardExactly.mp hExact).1

theorem threeGeneratedRows_card_le_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} {A B C : Row α}
    (hK : K = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    (sharedPart A B C).card * (sharedPart A C B).card +
      (sharedPart A B C).card * (sharedPart B C A).card +
      (sharedPart A C B).card * (sharedPart B C A).card +
      (sharedPart A B C).card * (privatePart C A B).card +
      (sharedPart A C B).card * (privatePart B A C).card +
      (sharedPart B C A).card * (privatePart A B C).card +
      (privatePart A B C).card *
        (privatePart B A C).card *
        (privatePart C A B).card ≤
      (blocker K).card := by
  classical
  let pairGenerated :=
    (threePairChoices A B C).image threePairChoiceRow
  let tripleGenerated :=
    tripleChoiceRows
      (privatePart A B C)
      (privatePart B A C)
      (privatePart C A B)
  have hPairCard : pairGenerated.card =
      (sharedPart A B C).card * (sharedPart A C B).card +
      (sharedPart A B C).card * (sharedPart B C A).card +
      (sharedPart A C B).card * (sharedPart B C A).card +
      (sharedPart A B C).card * (privatePart C A B).card +
      (sharedPart A C B).card * (privatePart B A C).card +
      (sharedPart B C A).card * (privatePart A B C).card := by
    change ((threePairChoices A B C).image threePairChoiceRow).card = _
    rw [Finset.card_image_iff.mpr (threePairChoiceRow_injective A B C)]
    exact threePairChoices_card A B C
  obtain ⟨hPQ, hPR, hQR⟩ := privatePart_pairwise_disjoint A B C
  have hTripleCard : tripleGenerated.card =
      (privatePart A B C).card *
        (privatePart B A C).card *
        (privatePart C A B).card := by
    exact tripleChoiceRows_card hPQ hPR hQR
  have hDisjoint : Disjoint pairGenerated tripleGenerated := by
    apply Finset.disjoint_left.mpr
    intro T hTPair hTTriple
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hTPair
    have hPairSize := threePairChoiceRow_card hq
    have hTripleExact : threePairChoiceRow q ∈ rowsCardExactly (blocker K) 3 := by
      rw [threeRow_triple_blockers hK hAB hAC hBC]
      exact hTTriple
    have hTripleSize := (mem_rowsCardExactly.mp hTripleExact).2
    omega
  have hUnionSubset : pairGenerated ∪ tripleGenerated ⊆ blocker K := by
    intro T hT
    rcases Finset.mem_union.mp hT with hTPair | hTTriple
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hTPair
      exact threePairChoiceRow_mem_blocker hK hq
    · exact tripleChoiceRows_subset_blocker hK hAB hAC hBC hTTriple
  calc
    (sharedPart A B C).card * (sharedPart A C B).card +
        (sharedPart A B C).card * (sharedPart B C A).card +
        (sharedPart A C B).card * (sharedPart B C A).card +
        (sharedPart A B C).card * (privatePart C A B).card +
        (sharedPart A C B).card * (privatePart B A C).card +
        (sharedPart B C A).card * (privatePart A B C).card +
        (privatePart A B C).card *
          (privatePart B A C).card *
          (privatePart C A B).card = pairGenerated.card + tripleGenerated.card := by
      rw [hPairCard, hTripleCard]
    _ = (pairGenerated ∪ tripleGenerated).card :=
      (Finset.card_union_of_disjoint hDisjoint).symm
    _ ≤ (blocker K).card := Finset.card_le_card hUnionSubset

def threeCap (n : Nat) : Fin 4 :=
  ⟨min n 3, by
    have h := Nat.min_le_right n 3
    omega⟩

theorem threeCap_le (n : Nat) : (threeCap n).val ≤ n := by
  exact Nat.min_le_left n 3

theorem threeCap_sum_three
    (a b c : Nat) (h : 3 ≤ a + b + c) :
    3 ≤ (threeCap a).val + (threeCap b).val + (threeCap c).val := by
  by_cases ha : a ≤ 3 <;> by_cases hb : b ≤ 3 <;> by_cases hc : c ≤ 3
  all_goals simp [threeCap, Nat.min_def, *] <;> omega

theorem threeCap_sum_pos
    (a b : Nat) (h : 0 < a + b) :
    0 < (threeCap a).val + (threeCap b).val := by
  by_cases ha : a ≤ 3 <;> by_cases hb : b ≤ 3
  all_goals simp [threeCap, Nat.min_def, *]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks all 4096 capped incidence vectors.
theorem seven_le_threePart_generated_count_finite :
    ∀ p q r x y z : Fin 4,
      3 ≤ p.val + x.val + y.val →
      3 ≤ q.val + x.val + z.val →
      3 ≤ r.val + y.val + z.val →
      0 < p.val + y.val → 0 < q.val + z.val →
      0 < p.val + x.val → 0 < r.val + z.val →
      0 < q.val + x.val → 0 < r.val + y.val →
      7 ≤ x.val * y.val + x.val * z.val + y.val * z.val +
        x.val * r.val + y.val * q.val + z.val * p.val + p.val * q.val * r.val := by
  decide

theorem seven_le_threePart_generated_count
    (p q r x y z : Nat)
    (hA : 3 ≤ p + x + y)
    (hB : 3 ≤ q + x + z)
    (hC : 3 ≤ r + y + z)
    (hAB : 0 < p + y) (hBA : 0 < q + z)
    (hAC : 0 < p + x) (hCA : 0 < r + z)
    (hBC : 0 < q + x) (hCB : 0 < r + y) :
    7 ≤ x * y + x * z + y * z + x * r + y * q + z * p + p * q * r := by
  have hFinite := seven_le_threePart_generated_count_finite
    (threeCap p) (threeCap q) (threeCap r)
    (threeCap x) (threeCap y) (threeCap z)
    (threeCap_sum_three p x y hA)
    (threeCap_sum_three q x z hB)
    (threeCap_sum_three r y z hC)
    (threeCap_sum_pos p y hAB) (threeCap_sum_pos q z hBA)
    (threeCap_sum_pos p x hAC) (threeCap_sum_pos r z hCA)
    (threeCap_sum_pos q x hBC) (threeCap_sum_pos r y hCB)
  apply hFinite.trans
  gcongr <;> exact threeCap_le _

theorem threeRow_blocker_card_ge_seven_explicit {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} {A B C : Row α}
    (hK : K = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hKClutter : IsClutter K)
    (hKRows : RowsCardAtLeast K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2) :
    7 ≤ (blocker K).card := by
  classical
  have hAK : A ∈ K := by simp [hK]
  have hBK : B ∈ K := by simp [hK]
  have hCK : C ∈ K := by simp [hK]
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBRows
  have hAnotB : ¬A ⊆ B := by
    intro hSubset
    exact hAB (hKClutter hAK hBK hSubset)
  have hBnotA : ¬B ⊆ A := by
    intro hSubset
    exact hAB (hKClutter hBK hAK hSubset).symm
  have hAnotC : ¬A ⊆ C := by
    intro hSubset
    exact hAC (hKClutter hAK hCK hSubset)
  have hCnotA : ¬C ⊆ A := by
    intro hSubset
    exact hAC (hKClutter hCK hAK hSubset).symm
  have hBnotC : ¬B ⊆ C := by
    intro hSubset
    exact hBC (hKClutter hBK hCK hSubset)
  have hCnotB : ¬C ⊆ B := by
    intro hSubset
    exact hBC (hKClutter hCK hBK hSubset).symm
  have hPYSum :
      0 < (privatePart A B C).card + (sharedPart A C B).card := by
    obtain ⟨u, huA, huB⟩ := Finset.not_subset.mp hAnotB
    by_cases huC : u ∈ C
    · have huY : u ∈ sharedPart A C B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huY⟩
      omega
    · have huP : u ∈ privatePart A B C :=
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huP⟩
      omega
  have hQZSum :
      0 < (privatePart B A C).card + (sharedPart B C A).card := by
    obtain ⟨u, huB, huA⟩ := Finset.not_subset.mp hBnotA
    by_cases huC : u ∈ C
    · have huZ : u ∈ sharedPart B C A :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huZ⟩
      omega
    · have huQ : u ∈ privatePart B A C :=
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huQ⟩
      omega
  have hPXSum :
      0 < (privatePart A B C).card + (sharedPart A B C).card := by
    obtain ⟨u, huA, huC⟩ := Finset.not_subset.mp hAnotC
    by_cases huB : u ∈ B
    · have huX : u ∈ sharedPart A B C :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huX⟩
      omega
    · have huP : u ∈ privatePart A B C :=
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huP⟩
      omega
  have hRZSum :
      0 < (privatePart C A B).card + (sharedPart B C A).card := by
    obtain ⟨u, huC, huA⟩ := Finset.not_subset.mp hCnotA
    by_cases huB : u ∈ B
    · have huZ : u ∈ sharedPart B C A :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huZ⟩
      omega
    · have huR : u ∈ privatePart C A B :=
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huR⟩
      omega
  have hQXSum :
      0 < (privatePart B A C).card + (sharedPart A B C).card := by
    obtain ⟨u, huB, huC⟩ := Finset.not_subset.mp hBnotC
    by_cases huA : u ∈ A
    · have huX : u ∈ sharedPart A B C :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huX⟩
      omega
    · have huQ : u ∈ privatePart B A C :=
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huQ⟩
      omega
  have hRYSum :
      0 < (privatePart C A B).card + (sharedPart A C B).card := by
    obtain ⟨u, huC, huB⟩ := Finset.not_subset.mp hCnotB
    by_cases huA : u ∈ A
    · have huY : u ∈ sharedPart A C B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huY⟩
      omega
    · have huR : u ∈ privatePart C A B :=
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩
      have hPositive := Finset.card_pos.mpr ⟨u, huR⟩
      omega
  have hACard := hKRows A hAK
  have hBCard := hKRows B hBK
  have hCCard := hKRows C hCK
  rw [threePart_union_card hNoCommon] at hACard
  rw [threePart_union_card_second hNoCommon] at hBCard
  rw [threePart_union_card_third hNoCommon] at hCCard
  have hSeven := seven_le_threePart_generated_count
    (privatePart A B C).card
    (privatePart B A C).card
    (privatePart C A B).card
    (sharedPart A B C).card
    (sharedPart A C B).card
    (sharedPart B C A).card
    hACard hBCard hCCard hPYSum hQZSum hPXSum hRZSum hQXSum hRYSum
  exact hSeven.trans (threeGeneratedRows_card_le_blocker hK hAB hAC hBC)

theorem threeRow_blocker_card_ge_seven {α : Type*}
    [Fintype α]
    {K : G413.Hypergraph α}
    (hKClutter : IsClutter K)
    (hKCard : K.card = 3)
    (hKRows : RowsCardAtLeast K 3)
    (hBRows : RowsCardAtLeast (blocker K) 2) :
    7 ≤ (blocker K).card := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  exact threeRow_blocker_card_ge_seven_explicit
    hK hAB hAC hBC hKClutter hKRows hBRows


end AiMathLab.P0054.G419
