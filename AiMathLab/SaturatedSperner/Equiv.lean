import AiMathLab.SaturatedSperner.ChainWitness

/-!
# Transport along equivalences of ground types

The saturation theorem below transports an arbitrary target subset through the
inverse equivalence.  It does not use cardinalities or finite enumeration.
-/

universe u v

namespace AiMathLab.SaturatedSperner

variable {α : Type u} {β : Type v}
  [DecidableEq α] [DecidableEq β]

/-- Transport one finite subset through a type equivalence. -/
def mapSubset (e : α ≃ β) (S : Finset α) : Finset β :=
  e.finsetCongr S

/-- The induced equivalence between finite families. -/
def familyEquiv (e : α ≃ β) : Family α ≃ Family β :=
  e.finsetCongr.finsetCongr

/-- Transport a finite family through a type equivalence. -/
def mapFamily (e : α ≃ β) (F : Family α) : Family β :=
  familyEquiv e F

/-- Transport every member of an explicit chain. -/
def mapChain (e : α ≃ β)
    (c : List (Finset α)) : List (Finset β) :=
  c.map (mapSubset e)

@[simp] theorem mapSubset_symm_apply
    (e : α ≃ β) (S : Finset α) :
    mapSubset e.symm (mapSubset e S) = S := by
  change e.finsetCongr.symm (e.finsetCongr S) = S
  exact e.finsetCongr.symm_apply_apply S

@[simp] theorem mapSubset_apply_symm
    (e : α ≃ β) (T : Finset β) :
    mapSubset e (mapSubset e.symm T) = T := by
  change e.finsetCongr (e.finsetCongr.symm T) = T
  exact e.finsetCongr.apply_symm_apply T

@[simp] theorem mapFamily_symm_apply
    (e : α ≃ β) (F : Family α) :
    mapFamily e.symm (mapFamily e F) = F := by
  change (familyEquiv e).symm (familyEquiv e F) = F
  exact (familyEquiv e).symm_apply_apply F

@[simp] theorem mapFamily_apply_symm
    (e : α ≃ β) (G : Family β) :
    mapFamily e (mapFamily e.symm G) = G := by
  change familyEquiv e ((familyEquiv e).symm G) = G
  exact (familyEquiv e).apply_symm_apply G

@[simp] theorem mem_mapFamily_iff
    (e : α ≃ β) (S : Finset α) (F : Family α) :
    mapSubset e S ∈ mapFamily e F ↔ S ∈ F := by
  change e.finsetCongr S ∈ Finset.map e.finsetCongr.toEmbedding F ↔ S ∈ F
  rw [Finset.mem_map_equiv]
  change mapSubset e.symm (mapSubset e S) ∈ F ↔ S ∈ F
  rw [mapSubset_symm_apply]

@[simp] theorem mem_mapFamily_symm_iff
    (e : α ≃ β) (T : Finset β) (F : Family α) :
    T ∈ mapFamily e F ↔ mapSubset e.symm T ∈ F := by
  constructor
  · intro hT
    have hm : mapSubset e.symm T ∈
        mapFamily e.symm (mapFamily e F) :=
      (mem_mapFamily_iff e.symm T (mapFamily e F)).mpr hT
    simpa using hm
  · intro hT
    have hm : mapSubset e (mapSubset e.symm T) ∈ mapFamily e F :=
      (mem_mapFamily_iff e (mapSubset e.symm T) F).mpr hT
    simpa using hm

@[simp] theorem mapSubset_ssubset_iff
    (e : α ≃ β) (A B : Finset α) :
    mapSubset e A ⊂ mapSubset e B ↔ A ⊂ B := by
  simp [mapSubset, Equiv.finsetCongr_apply, Finset.map_ssubset_map]

@[simp] theorem mapFamily_insert
    (e : α ≃ β) (S : Finset α) (F : Family α) :
    mapFamily e (insert S F) =
      insert (mapSubset e S) (mapFamily e F) := by
  simp [mapSubset, mapFamily, familyEquiv,
    Equiv.finsetCongr_apply, Finset.map_insert]

@[simp] theorem mapFamily_erase
    (e : α ≃ β) (F : Family α) (S : Finset α) :
    mapFamily e (F.erase S) =
      (mapFamily e F).erase (mapSubset e S) := by
  simp [mapSubset, mapFamily, familyEquiv,
    Equiv.finsetCongr_apply, Finset.map_erase]

@[simp] theorem mapChain_length
    (e : α ≃ β) (c : List (Finset α)) :
    (mapChain e c).length = c.length := by
  simp [mapChain]

@[simp] theorem mapChain_symm_apply
    (e : α ≃ β) (c : List (Finset α)) :
    mapChain e.symm (mapChain e c) = c := by
  induction c with
  | nil => rfl
  | cons A tail ih =>
      change mapSubset e.symm (mapSubset e A) ::
          mapChain e.symm (mapChain e tail) = A :: tail
      rw [mapSubset_symm_apply, ih]

theorem isStrictChainIn_mapChain_iff
    (e : α ≃ β) (F : Family α) (c : List (Finset α)) :
    IsStrictChainIn (mapFamily e F) (mapChain e c) ↔
      IsStrictChainIn F c := by
  induction c with
  | nil => simp [mapChain, IsStrictChainIn]
  | cons A tail ih =>
      cases tail with
      | nil =>
          change mapSubset e A ∈ mapFamily e F ↔ A ∈ F
          exact mem_mapFamily_iff e A F
      | cons B rest =>
          change
            (mapSubset e A ∈ mapFamily e F ∧
              mapSubset e A ⊂ mapSubset e B ∧
              IsStrictChainIn (mapFamily e F) (mapChain e (B :: rest))) ↔
            (A ∈ F ∧ A ⊂ B ∧ IsStrictChainIn F (B :: rest))
          rw [mem_mapFamily_iff, mapSubset_ssubset_iff, ih]

theorem hasStrictChainEndingAt_mapFamily_iff
    (e : α ≃ β) (d : Nat) (F : Family α) (B : Finset α) :
    HasStrictChainEndingAt d (mapFamily e F) (mapSubset e B) ↔
      HasStrictChainEndingAt d F B := by
  induction d generalizing B with
  | zero => exact mem_mapFamily_iff e B F
  | succ d ih =>
      constructor
      · rintro ⟨hBF, C, hC, hCB⟩
        let A := mapSubset e.symm C
        have hCA : mapSubset e A = C := by simp [A]
        have hA : HasStrictChainEndingAt d F A :=
          (ih A).mp (by simpa [hCA] using hC)
        have hAB : A ⊂ B :=
          (mapSubset_ssubset_iff e A B).mp (by simpa [hCA] using hCB)
        exact ⟨(mem_mapFamily_iff e B F).mp hBF, A, hA, hAB⟩
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨(mem_mapFamily_iff e B F).mpr hBF, mapSubset e A,
          (ih A).mpr hA, (mapSubset_ssubset_iff e A B).mpr hAB⟩

theorem hasStrictChainLength_mapFamily_iff
    (e : α ≃ β) (r : Nat) (F : Family α) :
    HasStrictChainLength r (mapFamily e F) ↔
      HasStrictChainLength r F := by
  cases r with
  | zero => simp
  | succ d =>
      constructor
      · rintro ⟨C, hC⟩
        let B := mapSubset e.symm C
        have hCB : mapSubset e B = C := by simp [B]
        exact ⟨B, (hasStrictChainEndingAt_mapFamily_iff e d F B).mp
          (by simpa [hCB] using hC)⟩
      · rintro ⟨B, hB⟩
        exact ⟨mapSubset e B,
          (hasStrictChainEndingAt_mapFamily_iff e d F B).mpr hB⟩

theorem hasStrictChainThrough_mapFamily_iff
    (e : α ≃ β) (r : Nat) (F : Family α) (S : Finset α) :
    HasStrictChainThrough r (mapFamily e F) (mapSubset e S) ↔
      HasStrictChainThrough r F S := by
  constructor
  · rintro ⟨c, hlen, hc, hSc⟩
    refine ⟨mapChain e.symm c, by simpa using hlen, ?_, ?_⟩
    · have hm := (isStrictChainIn_mapChain_iff e.symm (mapFamily e F) c).mpr hc
      simpa using hm
    · exact List.mem_map.mpr
        ⟨mapSubset e S, hSc, mapSubset_symm_apply e S⟩
  · rintro ⟨c, hlen, hc, hSc⟩
    exact ⟨mapChain e c, by simpa using hlen,
      (isStrictChainIn_mapChain_iff e F c).mpr hc,
      List.mem_map.mpr ⟨S, hSc, rfl⟩⟩

theorem hasNewStrictChainAt_mapFamily_iff
    (e : α ≃ β) (r : Nat) (F : Family α) (S : Finset α) :
    HasNewStrictChainAt r (mapFamily e F) (mapSubset e S) ↔
      HasNewStrictChainAt r F S := by
  simp only [HasNewStrictChainAt, ← mapFamily_insert]
  exact and_congr
    (hasStrictChainLength_mapFamily_iff e r (insert S F))
    (not_congr (hasStrictChainLength_mapFamily_iff e r F))

theorem hasEraseCriticalStrictChain_mapFamily_iff
    (e : α ≃ β) (r : Nat) (F : Family α) (S : Finset α) :
    HasEraseCriticalStrictChain r (mapFamily e F) (mapSubset e S) ↔
      HasEraseCriticalStrictChain r F S := by
  simp only [HasEraseCriticalStrictChain, ← mapFamily_erase]
  exact and_congr
    (hasStrictChainLength_mapFamily_iff e r F)
    (not_congr (hasStrictChainLength_mapFamily_iff e r (F.erase S)))

theorem isKSperner_mapFamily_iff
    (e : α ≃ β) (k : Nat) (F : Family α) :
    IsKSperner k (mapFamily e F) ↔ IsKSperner k F := by
  exact not_congr (hasStrictChainLength_mapFamily_iff e (k + 1) F)

private theorem isSaturatedKSperner_mapFamily_forward
    (e : α ≃ β) {k : Nat} {F : Family α}
    (h : IsSaturatedKSperner k F) :
    IsSaturatedKSperner k (mapFamily e F) := by
  refine ⟨(isKSperner_mapFamily_iff e k F).mpr h.1, ?_⟩
  intro T hTF
  let S := mapSubset e.symm T
  have hST : mapSubset e S = T := by simp [S]
  have hSF : S ∉ F := by
    intro hmem
    apply hTF
    rw [← hST]
    exact (mem_mapFamily_iff e S F).mpr hmem
  have hchain := h.2 S hSF
  have hmapped :
      HasStrictChainLength (k + 1) (mapFamily e (insert S F)) :=
    (hasStrictChainLength_mapFamily_iff e (k + 1) (insert S F)).mpr hchain
  simpa [mapFamily_insert, hST] using hmapped

theorem isSaturatedKSperner_mapFamily_iff
    (e : α ≃ β) (k : Nat) (F : Family α) :
    IsSaturatedKSperner k (mapFamily e F) ↔
      IsSaturatedKSperner k F := by
  constructor
  · intro h
    have hm := isSaturatedKSperner_mapFamily_forward e.symm h
    simpa using hm
  · exact isSaturatedKSperner_mapFamily_forward e

end AiMathLab.SaturatedSperner
