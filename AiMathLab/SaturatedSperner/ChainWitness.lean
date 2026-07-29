import AiMathLab.SaturatedSperner.Basic

/-!
# Explicit strict-chain witnesses

Lists in this module are ordered from the least set to the greatest set.  The
public through predicate therefore means that one chosen chain actually
contains the distinguished set; it is deliberately different from the legacy
erase-critical predicate.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [DecidableEq α]

/-- An ascending list whose entries lie in `F` and whose adjacent entries are
strictly increasing.  The empty list is a valid chain. -/
def IsStrictChainIn (F : Family α) : List (Finset α) → Prop
  | [] => True
  | [A] => A ∈ F
  | A :: B :: tail =>
      A ∈ F ∧ A ⊂ B ∧ IsStrictChainIn F (B :: tail)

/-- A locally inspectable length-`r` chain in `F` containing `S`. -/
def IsStrictChainWitness
    (r : Nat) (F : Family α) (S : Finset α)
    (c : List (Finset α)) : Prop :=
  c.length = r ∧ IsStrictChainIn F c ∧ S ∈ c

/-- There exists an actual strict chain through `S`. -/
def HasStrictChainThrough
    (r : Nat) (F : Family α) (S : Finset α) : Prop :=
  ∃ c, IsStrictChainWitness r F S c

@[simp] theorem isStrictChainIn_nil (F : Family α) :
    IsStrictChainIn F [] := by
  trivial

@[simp] theorem isStrictChainIn_singleton_iff
    (F : Family α) (A : Finset α) :
    IsStrictChainIn F [A] ↔ A ∈ F := by
  rfl

theorem isStrictChainIn_cons_cons_iff
    (F : Family α) (A B : Finset α) (tail : List (Finset α)) :
    IsStrictChainIn F (A :: B :: tail) ↔
      A ∈ F ∧ A ⊂ B ∧ IsStrictChainIn F (B :: tail) := by
  rfl

theorem IsStrictChainIn.head_mem
    {F : Family α} {A : Finset α} {tail : List (Finset α)}
    (h : IsStrictChainIn F (A :: tail)) : A ∈ F := by
  cases tail with
  | nil => exact h
  | cons B rest => exact h.1

theorem isStrictChainIn_mono_family
    {F G : Family α} {c : List (Finset α)}
    (hFG : F ⊆ G) (hc : IsStrictChainIn F c) :
    IsStrictChainIn G c := by
  induction c with
  | nil => trivial
  | cons A tail ih =>
      cases tail with
      | nil => exact hFG hc
      | cons B rest =>
          exact ⟨hFG hc.1, hc.2.1, ih hc.2.2⟩

private theorem isStrictChainIn_append_singleton
    {F : Family α} {c : List (Finset α)} {B : Finset α}
    (hc : IsStrictChainIn F c) (hBF : B ∈ F)
    (hlast : ∀ A, c.getLast? = some A → A ⊂ B) :
    IsStrictChainIn F (c ++ [B]) := by
  induction c with
  | nil => simpa [IsStrictChainIn] using hBF
  | cons A tail ih =>
      cases tail with
      | nil =>
          have hAB : A ⊂ B := hlast A (by simp)
          exact ⟨hc, hAB, hBF⟩
      | cons C rest =>
          refine ⟨hc.1, hc.2.1, ih hc.2.2 ?_⟩
          intro L hL
          apply hlast L
          simpa using hL

/-- Recursive endpoint chains have ascending list representatives with the
same endpoint.  The reverse direction is supplied at the chain-length level,
where no arbitrary endpoint decomposition is needed. -/
theorem exists_list_of_hasStrictChainEndingAt
    {d : Nat} {F : Family α} {B : Finset α}
    (h : HasStrictChainEndingAt d F B) :
    ∃ c : List (Finset α),
      c.length = d + 1 ∧ IsStrictChainIn F c ∧
        c.getLast? = some B := by
  induction d generalizing B with
  | zero => exact ⟨[B], by simp, h, by simp⟩
  | succ d ih =>
      rcases h with ⟨hBF, A, hA, hAB⟩
      rcases ih hA with ⟨c, hlen, hc, hlast⟩
      refine ⟨c ++ [B], by simp [hlen, Nat.add_assoc], ?_, by simp⟩
      exact isStrictChainIn_append_singleton hc hBF fun C hC => by
        have hCA : C = A := by
          rw [hlast] at hC
          exact Option.some.inj hC.symm
        simpa [hCA] using hAB

private theorem endingAt_extend_tail
    {F : Family α} {d : Nat} {A : Finset α}
    {tail : List (Finset α)}
    (hA : HasStrictChainEndingAt d F A)
    (hc : IsStrictChainIn F (A :: tail)) :
    ∃ B, HasStrictChainEndingAt (d + tail.length) F B := by
  induction tail generalizing d A with
  | nil => exact ⟨A, by simpa using hA⟩
  | cons B rest ih =>
      have hB : HasStrictChainEndingAt (d + 1) F B :=
        ⟨IsStrictChainIn.head_mem hc.2.2, A, hA, hc.2.1⟩
      rcases ih hB hc.2.2 with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      convert hC using 1 <;> simp only [List.length_cons] <;> omega

private theorem endingAt_of_nonempty_list
    {F : Family α} {A : Finset α} {tail : List (Finset α)}
    (hc : IsStrictChainIn F (A :: tail)) :
    ∃ B, HasStrictChainEndingAt tail.length F B := by
  rcases endingAt_extend_tail (d := 0)
      (IsStrictChainIn.head_mem hc) hc with ⟨B, hB⟩
  exact ⟨B, by simpa using hB⟩

/-- Recursive chains and explicit ascending list chains are equivalent in both
directions, including the length-zero case. -/
theorem hasStrictChainLength_iff_exists_list
    (r : Nat) (F : Family α) :
    HasStrictChainLength r F ↔
      ∃ c : List (Finset α),
        c.length = r ∧ IsStrictChainIn F c := by
  constructor
  · cases r with
    | zero => exact fun _ => ⟨[], rfl, trivial⟩
    | succ d =>
        rintro ⟨B, hB⟩
        rcases exists_list_of_hasStrictChainEndingAt hB with
          ⟨c, hlen, hc, hlast⟩
        exact ⟨c, by simpa using hlen, hc⟩
  · rintro ⟨c, hlen, hc⟩
    rcases c with _ | ⟨A, tail⟩
    · cases r with
      | zero => trivial
      | succ r => simp at hlen
    · rw [← hlen]
      rcases endingAt_of_nonempty_list hc with ⟨B, hB⟩
      exact ⟨B, hB⟩

theorem isStrictChainIn_of_insert_of_not_mem
    {F : Family α} {S : Finset α} {c : List (Finset α)}
    (hc : IsStrictChainIn (insert S F) c) (hSc : S ∉ c) :
    IsStrictChainIn F c := by
  induction c with
  | nil => trivial
  | cons A tail ih =>
      have hAS : A ≠ S := by
        intro h
        subst A
        exact hSc (by simp)
      cases tail with
      | nil => simpa [hAS] using hc
      | cons B rest =>
          refine ⟨?_, hc.2.1, ih hc.2.2 ?_⟩
          · simpa [hAS] using hc.1
          · intro hS
            exact hSc (by simp [hS])

theorem hasStrictChainLength_insert_iff
    {r : Nat} {F : Family α} {S : Finset α} :
    HasStrictChainLength r (insert S F) ↔
      HasStrictChainLength r F ∨
        HasStrictChainThrough r (insert S F) S := by
  constructor
  · intro h
    rcases (hasStrictChainLength_iff_exists_list r (insert S F)).mp h with
      ⟨c, hlen, hc⟩
    by_cases hSc : S ∈ c
    · exact Or.inr ⟨c, hlen, hc, hSc⟩
    · exact Or.inl ((hasStrictChainLength_iff_exists_list r F).mpr
        ⟨c, hlen, isStrictChainIn_of_insert_of_not_mem hc hSc⟩)
  · rintro (h | ⟨c, hlen, hc, hSc⟩)
    · exact hasStrictChainLength_mono_family (Finset.subset_insert S F) h
    · exact (hasStrictChainLength_iff_exists_list r (insert S F)).mpr
        ⟨c, hlen, hc⟩

theorem hasEraseCriticalStrictChain_insert_iff_hasNewStrictChainAt
    {r : Nat} {F : Family α} {S : Finset α} (hSF : S ∉ F) :
    HasEraseCriticalStrictChain r (insert S F) S ↔
      HasNewStrictChainAt r F S := by
  simp [HasEraseCriticalStrictChain, HasNewStrictChainAt,
    Finset.erase_insert, hSF]

theorem hasNewStrictChainAt_iff_inserted_chain
    {r : Nat} {F : Family α} {S : Finset α}
    (hno : ¬ HasStrictChainLength r F) :
    HasNewStrictChainAt r F S ↔
      HasStrictChainLength r (insert S F) := by
  simp [HasNewStrictChainAt, hno]

theorem inserted_chain_iff_hasStrictChainThrough
    {r : Nat} {F : Family α} {S : Finset α}
    (hno : ¬ HasStrictChainLength r F) :
    HasStrictChainLength r (insert S F) ↔
      HasStrictChainThrough r (insert S F) S := by
  rw [hasStrictChainLength_insert_iff]
  simp [hno]

theorem hasNewStrictChainAt_iff_hasStrictChainThrough
    {r : Nat} {F : Family α} {S : Finset α}
    (hno : ¬ HasStrictChainLength r F) :
    HasNewStrictChainAt r F S ↔
      HasStrictChainThrough r (insert S F) S := by
  rw [hasNewStrictChainAt_iff_inserted_chain hno,
    inserted_chain_iff_hasStrictChainThrough hno]

theorem hasEraseCriticalStrictChain_insert_iff_hasStrictChainThrough
    {r : Nat} {F : Family α} {S : Finset α}
    (hSF : S ∉ F) (hno : ¬ HasStrictChainLength r F) :
    HasEraseCriticalStrictChain r (insert S F) S ↔
      HasStrictChainThrough r (insert S F) S := by
  rw [hasEraseCriticalStrictChain_insert_iff_hasNewStrictChainAt hSF,
    hasNewStrictChainAt_iff_hasStrictChainThrough hno]

theorem forbiddenChain_controlled_equivalences
    {k : Nat} {F : Family α} {S : Finset α}
    (hk : IsKSperner k F) (hSF : S ∉ F) :
    (HasEraseCriticalStrictChain (k + 1) (insert S F) S ↔
      HasNewStrictChainAt (k + 1) F S) ∧
    (HasNewStrictChainAt (k + 1) F S ↔
      HasStrictChainLength (k + 1) (insert S F)) ∧
    (HasStrictChainLength (k + 1) (insert S F) ↔
      HasStrictChainThrough (k + 1) (insert S F) S) := by
  exact ⟨hasEraseCriticalStrictChain_insert_iff_hasNewStrictChainAt hSF,
    hasNewStrictChainAt_iff_inserted_chain hk,
    inserted_chain_iff_hasStrictChainThrough hk⟩

theorem isSaturatedKSperner_iff_hasNewStrictChainAt
    (k : Nat) (F : Family α) :
    IsSaturatedKSperner k F ↔
      IsKSperner k F ∧
      ∀ S : Finset α, S ∉ F →
        HasNewStrictChainAt (k + 1) F S := by
  constructor
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF =>
      (hasNewStrictChainAt_iff_inserted_chain hk).mpr (hs S hSF)⟩
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF =>
      (hasNewStrictChainAt_iff_inserted_chain hk).mp (hs S hSF)⟩

theorem isSaturatedKSperner_iff_hasStrictChainThrough
    (k : Nat) (F : Family α) :
    IsSaturatedKSperner k F ↔
      IsKSperner k F ∧
      ∀ S : Finset α, S ∉ F →
        HasStrictChainThrough (k + 1) (insert S F) S := by
  constructor
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF =>
      (inserted_chain_iff_hasStrictChainThrough hk).mp (hs S hSF)⟩
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF =>
      (inserted_chain_iff_hasStrictChainThrough hk).mpr (hs S hSF)⟩

theorem isSaturatedKSperner_iff_hasEraseCriticalStrictChain
    (k : Nat) (F : Family α) :
    IsSaturatedKSperner k F ↔
      IsKSperner k F ∧
      ∀ S : Finset α, S ∉ F →
        HasEraseCriticalStrictChain (k + 1) (insert S F) S := by
  constructor
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF =>
      (hasEraseCriticalStrictChain_insert_iff_hasNewStrictChainAt hSF).mpr
        ⟨hs S hSF, hk⟩⟩
  · rintro ⟨hk, hs⟩
    exact ⟨hk, fun S hSF => (hs S hSF).1⟩

@[simp] theorem not_hasStrictChainThrough_zero
    (F : Family α) (S : Finset α) :
    ¬ HasStrictChainThrough 0 F S := by
  rintro ⟨c, hlen, hc, hSc⟩
  have : c = [] := List.eq_nil_of_length_eq_zero hlen
  subst c
  simp at hSc

@[simp] theorem not_hasNewStrictChainAt_zero
    (F : Family α) (S : Finset α) :
    ¬ HasNewStrictChainAt 0 F S := by
  simp [HasNewStrictChainAt]

@[simp] theorem not_hasEraseCriticalStrictChain_zero
    (F : Family α) (S : Finset α) :
    ¬ HasEraseCriticalStrictChain 0 F S := by
  simp [HasEraseCriticalStrictChain]

end AiMathLab.SaturatedSperner
