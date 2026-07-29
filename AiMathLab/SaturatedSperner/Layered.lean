import AiMathLab.SaturatedSperner.ChainWitness

/-!
# Layered saturated antichains

This module formalizes the layered-union theorem of Morrison--Noel--Scott.
Layers are indexed from bottom to top.  Every containment appearing in the
layering and chain APIs is strict containment.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [DecidableEq α]

/-- An antichain, expressed through the generic Sperner API. -/
def IsAntichain (F : Family α) : Prop :=
  IsKSperner 1 F

/-- A saturated antichain, expressed through the generic saturation API. -/
def IsSaturatedAntichain (F : Family α) : Prop :=
  IsSaturatedKSperner 1 F

/-- The indexed union of all layers. -/
def LayerUnion {k : Nat} (A : Fin k → Family α) : Family α :=
  Finset.univ.biUnion A

/-- Distinct indexed layers are disjoint as families. -/
def PairwiseDisjointLayers {k : Nat} (A : Fin k → Family α) : Prop :=
  ∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (A i) (A j)

/-- Source orientation: every member of layer `i + 1` strictly contains a
member of layer `i`. -/
def IsLayered {k : Nat} (A : Fin k → Family α) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < k) (D : Finset α),
    D ∈ A ⟨i + 1, hi⟩ →
      ∃ C : Finset α, C ∈ A ⟨i, by omega⟩ ∧ C ⊂ D

@[simp] theorem mem_layerUnion
    {k : Nat} (A : Fin k → Family α) (S : Finset α) :
    S ∈ LayerUnion A ↔ ∃ i : Fin k, S ∈ A i := by
  simp [LayerUnion]

theorem layer_index_unique
    {k : Nat} {A : Fin k → Family α}
    (hdisj : PairwiseDisjointLayers A)
    {S : Finset α} {i j : Fin k}
    (hi : S ∈ A i) (hj : S ∈ A j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj hij) hi hj

theorem IsAntichain.not_ssubset
    {F : Family α} (hF : IsAntichain F)
    {C D : Finset α} (hC : C ∈ F) (hD : D ∈ F) :
    ¬ C ⊂ D := by
  intro hCD
  exact hF ⟨D, hD, C, hC, hCD⟩

/-- Standard saturation of an antichain supplies a member strictly comparable
with every external set. -/
theorem exists_comparable_of_isSaturatedAntichain
    {F : Family α} (hsat : IsSaturatedAntichain F)
    {S : Finset α} (hSF : S ∉ F) :
    ∃ T : Finset α, T ∈ F ∧ (T ⊂ S ∨ S ⊂ T) := by
  rcases hsat.2 S hSF with ⟨B, hB, A, hA, hAB⟩
  change A ∈ insert S F at hA
  rw [Finset.mem_insert] at hA hB
  rcases hA with rfl | hAF
  · rcases hB with rfl | hBF
    · exact False.elim (lt_irrefl _ hAB)
    · exact ⟨B, hBF, Or.inr hAB⟩
  · rcases hB with rfl | hBF
    · exact ⟨A, hAF, Or.inl hAB⟩
    · exact False.elim (hsat.1 ⟨B, hBF, A, hAF, hAB⟩)

/-- MNS Lemma 13.  The wrong comparable direction `E ⊂ D` is excluded by
downward layering and the antichain property of the lower layer. -/
theorem layered_step_up
    {k : Nat} (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A)
    {i : Nat} (hi : i + 1 < k)
    {D : Finset α} (hD : D ∈ A ⟨i, by omega⟩) :
    ∃ E : Finset α, E ∈ A ⟨i + 1, hi⟩ ∧ D ⊂ E := by
  let lo : Fin k := ⟨i, by omega⟩
  let hi' : Fin k := ⟨i + 1, hi⟩
  have hlo_ne_hi : lo ≠ hi' := by
    intro h
    simp [lo, hi'] at h
  have hDlo : D ∈ A lo := by
    simpa [lo] using hD
  have hDnot : D ∉ A hi' := by
    intro hDhi
    exact Finset.disjoint_left.mp (hdisj hlo_ne_hi) hDlo hDhi
  rcases exists_comparable_of_isSaturatedAntichain
      (hsat hi') hDnot with ⟨E, hE, hED | hDE⟩
  · rcases hlayered i hi E hE with ⟨C, hC, hCE⟩
    have hClo : C ∈ A lo := by
      simpa [lo] using hC
    have hCD : C ⊂ D := strictSubset_trans hCE hED
    exact False.elim ((hsat lo).1 ⟨D, hDlo, C, hClo, hCD⟩)
  · exact ⟨E, hE, hDE⟩

theorem IsStrictChainIn.get_mem
    {F : Family α} {c : List (Finset α)}
    (hc : IsStrictChainIn F c) (i : Fin c.length) :
    c.get i ∈ F := by
  induction c with
  | nil => exact Fin.elim0 i
  | cons A tail ih =>
      cases tail with
      | nil =>
          simpa using hc
      | cons B rest =>
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hc.1
          · simpa using ih hc.2.2 j

theorem IsStrictChainIn.pairwise_ssubset
    {F : Family α} {c : List (Finset α)}
    (hc : IsStrictChainIn F c) :
    c.Pairwise (· ⊂ ·) := by
  induction c with
  | nil => exact List.Pairwise.nil
  | cons A tail ih =>
      cases tail with
      | nil => exact List.pairwise_singleton (· ⊂ ·) A
      | cons B rest =>
          have htail := ih hc.2.2
          refine List.Pairwise.cons ?_ htail
          intro X hX
          simp only [List.mem_cons] at hX
          rcases hX with rfl | hX
          · exact hc.2.1
          · exact strictSubset_trans hc.2.1
              ((List.pairwise_cons.mp htail).1 X hX)

theorem IsStrictChainIn.get_ssubset_get_of_lt
    {F : Family α} {c : List (Finset α)}
    (hc : IsStrictChainIn F c)
    {i j : Fin c.length} (hij : i < j) :
    c.get i ⊂ c.get j :=
  (IsStrictChainIn.pairwise_ssubset hc).rel_get_of_lt hij

theorem isStrictChainIn_iff_forall_mem_and_isChain
    (F : Family α) (c : List (Finset α)) :
    IsStrictChainIn F c ↔
      (∀ X ∈ c, X ∈ F) ∧ c.IsChain (· ⊂ ·) := by
  induction c with
  | nil => simp [IsStrictChainIn]
  | cons A tail ih =>
      cases tail with
      | nil => simp [IsStrictChainIn]
      | cons B rest =>
          simp only [IsStrictChainIn, List.chain_cons, ih,
            List.mem_cons, forall_eq_or_imp]
          aesop

theorem isStrictChainIn_ofFn
    {F : Family α} {n : Nat} (f : Fin n → Finset α)
    (hmem : ∀ i, f i ∈ F)
    (hadj : ∀ (i : Nat) (hi : i + 1 < n),
      f ⟨i, by omega⟩ ⊂ f ⟨i + 1, hi⟩) :
    IsStrictChainIn F (List.ofFn f) := by
  rw [isStrictChainIn_iff_forall_mem_and_isChain]
  exact ⟨List.forall_mem_ofFn_iff.mpr hmem,
    List.isChain_ofFn.mpr hadj⟩

/-- A strict chain in the union uses at most one member of each antichain
layer.  The finite layer-index pigeonhole argument therefore bounds its length
by the number of layers. -/
theorem layerUnion_isKSperner
    {k : Nat} (A : Fin k → Family α)
    (hanti : ∀ i, IsAntichain (A i)) :
    IsKSperner k (LayerUnion A) := by
  intro hchain
  rcases (hasStrictChainLength_iff_exists_list
      (k + 1) (LayerUnion A)).mp hchain with ⟨c, hlen, hc⟩
  classical
  let entry : Fin (k + 1) → Finset α := fun p =>
    c.get ⟨p.val, by omega⟩
  have hentry_mem (p : Fin (k + 1)) : entry p ∈ LayerUnion A := by
    exact IsStrictChainIn.get_mem hc ⟨p.val, by omega⟩
  let layer : Fin (k + 1) → Fin k := fun p =>
    Classical.choose ((mem_layerUnion A (entry p)).mp (hentry_mem p))
  have hlayer_mem (p : Fin (k + 1)) : entry p ∈ A (layer p) := by
    exact Classical.choose_spec
      ((mem_layerUnion A (entry p)).mp (hentry_mem p))
  have hinjective : Function.Injective layer := by
    intro p q hpq
    by_contra hpq_ne
    rcases lt_or_gt_of_ne hpq_ne with hpq_lt | hqp_lt
    · have hsubset : entry p ⊂ entry q := by
        apply IsStrictChainIn.get_ssubset_get_of_lt hc
        simpa [entry] using hpq_lt
      have hqmem : entry q ∈ A (layer p) := by
        simpa [hpq] using hlayer_mem q
      exact (hanti (layer p)).not_ssubset
        (hlayer_mem p) hqmem hsubset
    · have hsubset : entry q ⊂ entry p := by
        apply IsStrictChainIn.get_ssubset_get_of_lt hc
        simpa [entry] using hqp_lt
      have hpmem : entry p ∈ A (layer q) := by
        simpa [hpq] using hlayer_mem p
      exact (hanti (layer q)).not_ssubset
        (hlayer_mem q) hpmem hsubset
  have hcard := Fintype.card_le_of_injective layer hinjective
  simp only [Fintype.card_fin] at hcard
  omega

/-- A coherent strict selection from the consecutive layers
`start, ..., start + span`.  The separate range proof in the existence
theorems makes every `Fin k` construction explicit. -/
def IsLayerIntervalChain
    {k span : Nat} (A : Fin k → Family α) (start : Nat)
    (hbound : start + span < k)
    (f : Fin (span + 1) → Finset α) : Prop :=
  (∀ j : Fin (span + 1),
      f j ∈ A ⟨start + j.val, by omega⟩) ∧
    ∀ (j : Nat) (hj : j + 1 < span + 1),
      f ⟨j, by omega⟩ ⊂ f ⟨j + 1, hj⟩

theorem IsLayerIntervalChain.isStrictChainIn
    {k span start : Nat} {A : Fin k → Family α}
    {hbound : start + span < k}
    {f : Fin (span + 1) → Finset α}
    (hf : IsLayerIntervalChain A start hbound f) :
    IsStrictChainIn (LayerUnion A) (List.ofFn f) := by
  apply isStrictChainIn_ofFn f
  · intro i
    exact (mem_layerUnion A (f i)).mpr ⟨_, hf.1 i⟩
  · exact hf.2

/-- Downward layering selects a strict chain across any consecutive interval
ending at a prescribed member of its last layer. -/
theorem exists_downward_layer_chain
    {k : Nat} (A : Fin k → Family α)
    (hlayered : IsLayered A)
    (start span : Nat) (hbound : start + span < k)
    {D : Finset α}
    (hD : D ∈ A ⟨start + span, hbound⟩) :
    ∃ f : Fin (span + 1) → Finset α,
      IsLayerIntervalChain A start hbound f ∧ f (Fin.last span) = D := by
  induction span generalizing D with
  | zero =>
      let f : Fin 1 → Finset α := fun _ => D
      refine ⟨f, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro j
          have hj0 : j = 0 := Fin.eq_zero j
          subst j
          simpa [f] using hD
        · intro j hj
          omega
      · simp [f]
  | succ span ih =>
      have hprev : start + span + 1 < k := by omega
      rcases hlayered (start + span) hprev D
          (by simpa [Nat.add_assoc] using hD) with ⟨C, hC, hCD⟩
      have hprevBound : start + span < k := by omega
      rcases ih hprevBound hC with ⟨g, hg, hglast⟩
      let f : Fin (span + 1 + 1) → Finset α := Fin.snoc g D
      refine ⟨f, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro j
          refine Fin.lastCases ?_ (fun q => ?_) j
          · simpa [f, Nat.add_assoc] using hD
          · simpa [f] using hg.1 q
        · intro j hj
          by_cases hjlast : j < span
          · have hrel := hg.2 j (by omega)
            have hfirst :
                (⟨j, by omega⟩ : Fin (span + 1 + 1)) =
                  (⟨j, by omega⟩ : Fin (span + 1)).castSucc := Fin.ext rfl
            have hsecond :
                (⟨j + 1, hj⟩ : Fin (span + 1 + 1)) =
                  (⟨j + 1, by omega⟩ : Fin (span + 1)).castSucc := Fin.ext rfl
            rw [hfirst, hsecond]
            simp only [f, Fin.snoc_castSucc]
            exact hrel
          · have hjeq : j = span := by omega
            subst j
            have hfirst :
                (⟨span, by omega⟩ : Fin (span + 1 + 1)) =
                  (Fin.last span).castSucc := Fin.ext rfl
            have hsecond :
                (⟨span + 1, hj⟩ : Fin (span + 1 + 1)) =
                  Fin.last (span + 1) := Fin.ext rfl
            rw [hfirst, hsecond]
            simp only [f, Fin.snoc_castSucc, Fin.snoc_last, hglast]
            exact hCD
      · simp [f]

/-- The derived upward bridge selects a strict chain across any consecutive
interval beginning at a prescribed member of its first layer. -/
theorem exists_upward_layer_chain
    {k : Nat} (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A)
    (start span : Nat) (hbound : start + span < k)
    {D : Finset α}
    (hD : D ∈ A ⟨start, by omega⟩) :
    ∃ f : Fin (span + 1) → Finset α,
      IsLayerIntervalChain A start hbound f ∧ f 0 = D := by
  induction span generalizing start D with
  | zero =>
      let f : Fin 1 → Finset α := fun _ => D
      refine ⟨f, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro j
          have hj0 : j = 0 := Fin.eq_zero j
          subst j
          simpa [f] using hD
        · intro j hj
          omega
      · simp [f]

  | succ span ih =>
      have hstep : start + 1 < k := by omega
      rcases layered_step_up A hsat hdisj hlayered hstep hD with
        ⟨E, hE, hDE⟩
      have htailBound : start + 1 + span < k := by omega
      rcases ih (start := start + 1) htailBound hE with
        ⟨g, hg, hgzero⟩
      let f : Fin (span + 1 + 1) → Finset α := Fin.cons D g
      refine ⟨f, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro j
          refine Fin.cases ?_ (fun q => ?_) j
          · simpa [f] using hD
          · simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg.1 q
        · intro j hj
          cases j with
          | zero => simpa [f, hgzero] using hDE
          | succ j =>
              have hrel := hg.2 j (by omega)
              have hfirst :
                  (⟨j + 1, by omega⟩ : Fin (span + 1 + 1)) =
                    (⟨j, by omega⟩ : Fin (span + 1)).succ := Fin.ext rfl
              have hsecond :
                  (⟨j + 1 + 1, hj⟩ : Fin (span + 1 + 1)) =
                    (⟨j + 1, by omega⟩ : Fin (span + 1)).succ := Fin.ext rfl
              rw [hfirst, hsecond]
              simp only [f, Fin.cons_succ]
              exact hrel
      · simp [f]

/-- Besides `S`, the exact-length ascending witness selects exactly one member
from every layer.  The cut-indexed lower and upper functions cover the layer
indices `0, ..., cut - 1` and `cut, ..., k - 1` without overlap or omission. -/
def IsLayeredChainWitness
    {k : Nat} (A : Fin k → Family α) (S : Finset α)
    (c : List (Finset α)) : Prop :=
  IsStrictChainWitness (k + 1) (insert S (LayerUnion A)) S c ∧
    ∃ (cut : Nat) (hcut : cut ≤ k)
      (lower : Fin cut → Finset α)
      (upper : Fin (k - cut) → Finset α),
      (∀ i, lower i ∈ A ⟨i.val, lt_of_lt_of_le i.isLt hcut⟩) ∧
      (∀ i, upper i ∈ A ⟨cut + i.val, by omega⟩) ∧
      c.Perm (S :: (List.ofFn lower ++ List.ofFn upper))

private theorem IsLayerIntervalChain.all_ssubset_of_last_ssubset
    {k span start : Nat} {A : Fin k → Family α}
    {hbound : start + span < k}
    {f : Fin (span + 1) → Finset α}
    (hf : IsLayerIntervalChain A start hbound f)
    {S : Finset α} (hlast : f (Fin.last span) ⊂ S) :
    ∀ i, f i ⊂ S := by
  intro i
  by_cases hi : i = Fin.last span
  · simpa [hi] using hlast
  · have hilt : i < Fin.last span := lt_of_le_of_ne (Fin.le_last i) hi
    have hp := List.pairwise_ofFn.mp
      (IsStrictChainIn.pairwise_ssubset hf.isStrictChainIn)
    exact strictSubset_trans (hp hilt) hlast

private theorem IsLayerIntervalChain.all_ssuperset_of_ssubset_first
    {k span start : Nat} {A : Fin k → Family α}
    {hbound : start + span < k}
    {f : Fin (span + 1) → Finset α}
    (hf : IsLayerIntervalChain A start hbound f)
    {S : Finset α} (hfirst : S ⊂ f 0) :
    ∀ i, S ⊂ f i := by
  intro i
  by_cases hi : i = 0
  · simpa [hi] using hfirst
  · have hzero : (0 : Fin (span + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have hp := List.pairwise_ofFn.mp
      (IsStrictChainIn.pairwise_ssubset hf.isStrictChainIn)
    exact strictSubset_trans hfirst (hp hzero)

private theorem cutSelection_isLayeredChainWitness
    {k cut : Nat} (A : Fin k → Family α) (S : Finset α)
    (hcut : cut ≤ k)
    (lower : Fin cut → Finset α)
    (upper : Fin (k - cut) → Finset α)
    (hlmem : ∀ i, lower i ∈ A ⟨i.val, lt_of_lt_of_le i.isLt hcut⟩)
    (humem : ∀ i, upper i ∈ A ⟨cut + i.val, by omega⟩)
    (hlchain : IsStrictChainIn (LayerUnion A) (List.ofFn lower))
    (huchain : IsStrictChainIn (LayerUnion A) (List.ofFn upper))
    (hlow : ∀ i, lower i ⊂ S)
    (hupp : ∀ i, S ⊂ upper i) :
    IsLayeredChainWitness A S
      (List.ofFn lower ++ S :: List.ofFn upper) := by
  let l := List.ofFn lower
  let u := List.ofFn upper
  have hlIsChain : l.IsChain (· ⊂ ·) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hlchain |>.2
  have huIsChain : u.IsChain (· ⊂ ·) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp huchain |>.2
  have hlSChain : (l ++ [S]).IsChain (· ⊂ ·) := by
    rw [List.isChain_append]
    refine ⟨hlIsChain, by simp, ?_⟩
    intro X hX Y hY
    have hYS : Y = S := by simpa using hY.symm
    subst Y
    have hXl : X ∈ l := List.mem_of_mem_getLast? hX
    rcases List.mem_ofFn.mp (by simpa [l] using hXl) with ⟨i, rfl⟩
    exact hlow i
  have hallChain : (l ++ [S] ++ u).IsChain (· ⊂ ·) := by
    rw [List.isChain_append]
    refine ⟨hlSChain, huIsChain, ?_⟩
    intro X hX Y hY
    have hXS : X = S := by simpa using hX.symm
    subst X
    have hYu : Y ∈ u := List.mem_of_mem_head? hY
    rcases List.mem_ofFn.mp (by simpa [u] using hYu) with ⟨i, rfl⟩
    exact hupp i
  have hallMem :
      ∀ X ∈ l ++ [S] ++ u, X ∈ insert S (LayerUnion A) := by
    intro X hX
    simp only [List.mem_append, List.mem_singleton] at hX
    rcases hX with (hXl | rfl) | hXu
    · rcases List.mem_ofFn.mp (by simpa [l] using hXl) with ⟨i, rfl⟩
      exact Finset.mem_insert_of_mem
        ((mem_layerUnion A (lower i)).mpr ⟨_, hlmem i⟩)
    · exact Finset.mem_insert_self _ (LayerUnion A)
    · rcases List.mem_ofFn.mp (by simpa [u] using hXu) with ⟨i, rfl⟩
      exact Finset.mem_insert_of_mem
        ((mem_layerUnion A (upper i)).mpr ⟨_, humem i⟩)
  have hstrict :
      IsStrictChainIn (insert S (LayerUnion A)) (l ++ [S] ++ u) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mpr
      ⟨hallMem, hallChain⟩
  refine ⟨?_, cut, hcut, lower, upper, hlmem, humem, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [l, u]
      omega
    · simpa [l, u, List.append_assoc] using hstrict
    · simp [l, u]
  · simpa [l, u, List.append_assoc] using
      (List.perm_middle :
        (l ++ S :: u).Perm (S :: (l ++ u)))

/-- The finite set of layers containing a member strictly below `S`. -/
def LowerLayerIndices
    {k : Nat} (A : Fin k → Family α) (S : Finset α) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∃ D ∈ A i, D ⊂ S

@[simp] theorem mem_lowerLayerIndices
    {k : Nat} (A : Fin k → Family α) (S : Finset α) (i : Fin k) :
    i ∈ LowerLayerIndices A S ↔ ∃ D ∈ A i, D ⊂ S := by
  simp [LowerLayerIndices]

private theorem exists_downward_layer_chain_count
    {k : Nat} (A : Fin k → Family α) (hlayered : IsLayered A)
    (start count : Nat) (hcount : 0 < count)
    (hbound : start + count ≤ k)
    {D : Finset α}
    (hD : D ∈ A ⟨start + count - 1, by omega⟩) :
    ∃ f : Fin count → Finset α,
      (∀ i, f i ∈ A ⟨start + i.val, by omega⟩) ∧
      IsStrictChainIn (LayerUnion A) (List.ofFn f) ∧
      f ⟨count - 1, by omega⟩ = D := by
  have hspan : start + (count - 1) < k := by omega
  have hD' : D ∈ A ⟨start + (count - 1), hspan⟩ := by
    simpa [Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcount))]
      using hD
  rcases exists_downward_layer_chain A hlayered
      start (count - 1) hspan hD' with ⟨g, hg, hglast⟩
  have heq : count - 1 + 1 = count := by omega
  let f : Fin count → Finset α := fun i => g (Fin.cast heq.symm i)
  have hlist : List.ofFn g = List.ofFn f := by
    simpa [f] using List.ofFn_congr heq g
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    simpa [f] using hg.1 (Fin.cast heq.symm i)
  · rw [← hlist]
    exact hg.isStrictChainIn
  · change g (Fin.cast heq.symm ⟨count - 1, by omega⟩) = D
    have hidx : Fin.cast heq.symm ⟨count - 1, by omega⟩ =
        Fin.last (count - 1) := Fin.ext rfl
    rw [hidx]
    exact hglast

private theorem exists_upward_layer_chain_count
    {k : Nat} (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A)
    (start count : Nat) (hcount : 0 < count)
    (hbound : start + count ≤ k)
    {D : Finset α}
    (hD : D ∈ A ⟨start, by omega⟩) :
    ∃ f : Fin count → Finset α,
      (∀ i, f i ∈ A ⟨start + i.val, by omega⟩) ∧
      IsStrictChainIn (LayerUnion A) (List.ofFn f) ∧
      f ⟨0, hcount⟩ = D := by
  have hspan : start + (count - 1) < k := by omega
  rcases exists_upward_layer_chain A hsat hdisj hlayered
      start (count - 1) hspan hD with ⟨g, hg, hgzero⟩
  have heq : count - 1 + 1 = count := by omega
  let f : Fin count → Finset α := fun i => g (Fin.cast heq.symm i)
  have hlist : List.ofFn g = List.ofFn f := by
    simpa [f] using List.ofFn_congr heq g
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    simpa [f] using hg.1 (Fin.cast heq.symm i)
  · rw [← hlist]
    exact hg.isStrictChainIn
  · simpa [f] using hgzero

private theorem all_ssubset_of_last_ssubset
    {k n : Nat} {A : Fin k → Family α}
    (hn : 0 < n) (f : Fin n → Finset α)
    (hchain : IsStrictChainIn (LayerUnion A) (List.ofFn f))
    {S : Finset α} (hlast : f ⟨n - 1, by omega⟩ ⊂ S) :
    ∀ i, f i ⊂ S := by
  intro i
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hi : i = last
  · simpa [last, hi] using hlast
  · have hile : i ≤ last := by
      change i.val ≤ n - 1
      omega
    have hilt : i < last := lt_of_le_of_ne hile hi
    have hp := List.pairwise_ofFn.mp
      (IsStrictChainIn.pairwise_ssubset hchain)
    exact strictSubset_trans (hp hilt) (by simpa [last] using hlast)

private theorem all_ssuperset_of_ssubset_first
    {k n : Nat} {A : Fin k → Family α}
    (hn : 0 < n) (f : Fin n → Finset α)
    (hchain : IsStrictChainIn (LayerUnion A) (List.ofFn f))
    {S : Finset α} (hfirst : S ⊂ f ⟨0, hn⟩) :
    ∀ i, S ⊂ f i := by
  intro i
  let first : Fin n := ⟨0, hn⟩
  by_cases hi : i = first
  · simpa [first, hi] using hfirst
  · have hlt : first < i := by
      have hivpos : 0 < i.val := by
        by_contra hnot
        have hiv : i.val = 0 := by omega
        apply hi
        apply Fin.ext
        simpa [first] using hiv
      change first.val < i.val
      simpa [first] using hivpos
    have hp := List.pairwise_ofFn.mp
      (IsStrictChainIn.pairwise_ssubset hchain)
    exact strictSubset_trans (by simpa [first] using hfirst) (hp hlt)

/-- Every external set lies on an explicit ascending chain of length `k + 1`
which otherwise contains exactly one selected member of every layer.  The proof
splits before taking a maximum: no lower layer, an internal maximal lower
layer, and the top layer. -/
theorem layered_external_chain_through
    {k : Nat} (hk : 0 < k) (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A)
    {S : Finset α} (hS : S ∉ LayerUnion A) :
    ∃ c : List (Finset α), IsLayeredChainWitness A S c := by
  have hSnot (i : Fin k) : S ∉ A i := by
    intro hSi
    exact hS ((mem_layerUnion A S).mpr ⟨i, hSi⟩)
  let L := LowerLayerIndices A S
  by_cases hLempty : L = ∅
  · -- Empty lower-index set: force an upper member in layer zero.
    let zero : Fin k := ⟨0, hk⟩
    rcases exists_comparable_of_isSaturatedAntichain
        (hsat zero) (hSnot zero) with ⟨B, hB, hBS | hSB⟩
    · have hzL : zero ∈ L := by
        change zero ∈ LowerLayerIndices A S
        exact (mem_lowerLayerIndices A S zero).mpr ⟨B, hB, hBS⟩
      exact False.elim (by simpa [hLempty] using hzL)
    · rcases exists_upward_layer_chain_count A hsat hdisj hlayered
          0 k hk (by omega) (by simpa [zero] using hB) with
        ⟨upper, humem, huchain, huzero⟩
      let lower : Fin 0 → Finset α := fun i => Fin.elim0 i
      have hlmem : ∀ i, lower i ∈
          A ⟨i.val, lt_of_lt_of_le i.isLt (show 0 ≤ k by omega)⟩ := by
        intro i
        exact Fin.elim0 i
      have hlchain :
          IsStrictChainIn (LayerUnion A) (List.ofFn lower) := by
        simp [lower, IsStrictChainIn]
      have hlow : ∀ i, lower i ⊂ S := by
        intro i
        exact Fin.elim0 i
      have hfirst : S ⊂ upper ⟨0, hk⟩ := by
        rw [huzero]
        exact hSB
      have hupp : ∀ i, S ⊂ upper i :=
        all_ssuperset_of_ssubset_first hk upper huchain hfirst
      refine ⟨List.ofFn lower ++ S :: List.ofFn upper, ?_⟩
      apply cutSelection_isLayeredChainWitness A S (cut := 0)
        (by omega) lower upper hlmem
      · intro i
        simpa using humem i
      · exact hlchain
      · exact huchain
      · exact hlow
      · exact hupp
  · -- Nonempty lower-index set: only now take its maximum.
    have hLne : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLempty
    let t : Fin k := L.max' hLne
    have htL : t ∈ L := by
      exact Finset.max'_mem L hLne
    have htLower : t ∈ LowerLayerIndices A S := by
      simpa [L] using htL
    rcases (mem_lowerLayerIndices A S t).mp htLower with
      ⟨D, hD, hDS⟩
    by_cases htop : t.val + 1 = k
    · -- Top maximum: all `k` layers lie below `S`.
      have htval : t.val = k - 1 := by omega
      have hDtop : D ∈ A ⟨0 + k - 1, by omega⟩ := by
        have hidx : (⟨0 + k - 1, by omega⟩ : Fin k) = t := by
          apply Fin.ext
          simpa using htval.symm
        rw [hidx]
        exact hD
      rcases exists_downward_layer_chain_count A hlayered
          0 k hk (by omega) hDtop with
        ⟨lower, hlmem0, hlchain, hllast⟩
      let upper : Fin (k - k) → Finset α := fun i => Fin.elim0 (by simpa using i)
      have hlmem : ∀ i, lower i ∈
          A ⟨i.val, lt_of_lt_of_le i.isLt (show k ≤ k by omega)⟩ := by
        intro i
        simpa using hlmem0 i
      have humem : ∀ i, upper i ∈ A ⟨k + i.val, by omega⟩ := by
        intro i
        exact Fin.elim0 (by simpa using i)
      have huchain :
          IsStrictChainIn (LayerUnion A) (List.ofFn upper) := by
        simp [upper, IsStrictChainIn]
      have hlast : lower ⟨k - 1, by omega⟩ ⊂ S := by
        rw [hllast]
        exact hDS
      have hlow : ∀ i, lower i ⊂ S :=
        all_ssubset_of_last_ssubset hk lower hlchain hlast
      have hupp : ∀ i, S ⊂ upper i := by
        intro i
        exact Fin.elim0 (by simpa using i)
      refine ⟨List.ofFn lower ++ S :: List.ofFn upper, ?_⟩
      exact cutSelection_isLayeredChainWitness A S (cut := k)
        (by omega) lower upper hlmem humem hlchain huchain hlow hupp
    · -- Internal maximum: force an upper member in the successor layer.
      have hinter : t.val + 1 < k := by omega
      let cut := t.val + 1
      have hcutPos : 0 < cut := by omega
      have hcutLe : cut ≤ k := by omega
      have hDcut : D ∈ A ⟨0 + cut - 1, by omega⟩ := by
        have hidx : (⟨0 + cut - 1, by omega⟩ : Fin k) = t := by
          apply Fin.ext
          simp [cut]
        rw [hidx]
        exact hD
      rcases exists_downward_layer_chain_count A hlayered
          0 cut hcutPos (by omega) hDcut with
        ⟨lower, hlmem0, hlchain, hllast⟩
      let next : Fin k := ⟨cut, by omega⟩
      rcases exists_comparable_of_isSaturatedAntichain
          (hsat next) (hSnot next) with ⟨E, hE, hES | hSE⟩
      · have hnLower : next ∈ LowerLayerIndices A S :=
          (mem_lowerLayerIndices A S next).mpr ⟨E, hE, hES⟩
        have hnL : next ∈ L := by simpa [L] using hnLower
        have hnle : next ≤ t := Finset.le_max' L next hnL
        exact False.elim (by
          have := show next.val ≤ t.val from hnle
          simp [next, cut] at this)
      · have upperCountPos : 0 < k - cut := by omega
        have upperBound : cut + (k - cut) ≤ k := by omega
        rcases exists_upward_layer_chain_count A hsat hdisj hlayered
            cut (k - cut) upperCountPos upperBound
            (by simpa [next] using hE) with
          ⟨upper, humem, huchain, huzero⟩
        have hlmem : ∀ i, lower i ∈
            A ⟨i.val, lt_of_lt_of_le i.isLt hcutLe⟩ := by
          intro i
          simpa using hlmem0 i
        have hlast : lower ⟨cut - 1, by omega⟩ ⊂ S := by
          rw [hllast]
          exact hDS
        have hlow : ∀ i, lower i ⊂ S :=
          all_ssubset_of_last_ssubset hcutPos lower hlchain hlast
        have hfirst : S ⊂ upper ⟨0, upperCountPos⟩ := by
          rw [huzero]
          exact hSE
        have hupp : ∀ i, S ⊂ upper i :=
          all_ssuperset_of_ssubset_first
            upperCountPos upper huchain hfirst
        refine ⟨List.ofFn lower ++ S :: List.ofFn upper, ?_⟩
        exact cutSelection_isLayeredChainWitness A S (cut := cut)
          hcutLe lower upper hlmem humem hlchain huchain hlow hupp

/-- MNS Lemma 14 / Martin--Veldt Lemma 11, in the strongest representation
form: only decidable equality on the ground type is used. -/
theorem layered_saturated_antichains
    {k : Nat} (hk : 0 < k) (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedKSperner 1 (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A) :
    IsSaturatedKSperner k (LayerUnion A) := by
  apply (isSaturatedKSperner_iff_hasStrictChainThrough
    k (LayerUnion A)).mpr
  refine ⟨layerUnion_isKSperner A (fun i => (hsat i).1), ?_⟩
  intro S hS
  rcases layered_external_chain_through hk A hsat hdisj hlayered hS with
    ⟨c, hc⟩
  exact ⟨c, hc.1⟩

/-- The finite-ground specialization matching the Boolean-lattice source
statement.  This is a specialization of the symbolic theorem above. -/
theorem layered_saturated_antichains_finiteGround
    [Fintype α]
    {k : Nat} (hk : 0 < k) (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedKSperner 1 (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A) :
    IsSaturatedKSperner k (LayerUnion A) :=
  layered_saturated_antichains hk A hsat hdisj hlayered

end AiMathLab.SaturatedSperner
