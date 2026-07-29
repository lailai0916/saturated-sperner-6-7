import AiMathLab.P0054AdjacentExact
import AiMathLab.P0054CanonicalProfiles

/-!
# The canonical seven-layer baseline

For a saturated seven-Sperner family with a homogeneous atom and an external
set, the canonical profile is bounded below by
`[1, 6, 12, 14, 12, 6, 1]`.  This module also records the two adjacent-layer
relations used by the strict low-total exclusions.
-/

universe u

namespace AiMathLab.P0054.SevenBaseline

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413
open AiMathLab.P0054.CanonicalBlocker
open AiMathLab.P0054.CanonicalProfiles

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The componentwise profile available before any strict low-total
exclusion is used. -/
def baselineProfile : Fin 7 → Nat := ![1, 6, 12, 14, 12, 6, 1]

theorem adjacent_large_strict
    {F : Family α} {H : Finset α}
    (hsat : IsSaturatedKSperner 7 F)
    (hH : IsHomogeneousAtom F H)
    (i : Nat) (hi : i + 1 < 7) :
    ∀ G ∈ largeComplementTrace (canonicalLayers 7 F ⟨i, by omega⟩) H,
      ∃ K ∈ largeComplementTrace
          (canonicalLayers 7 F ⟨i + 1, by omega⟩) H,
        K ⊂ G := by
  classical
  intro G hG
  rcases mem_largeComplementTrace_iff.mp hG with ⟨L, hL, hHL, rfl⟩
  have hsaturated := canonicalLayers_saturated_of_homogeneousAtom
    (by decide : 0 < 7) F H hsat hH
  rcases layered_step_up (canonicalLayers 7 F) hsaturated
      (canonicalLayers_pairwiseDisjoint 7 F)
      (canonicalLayers_layered 7 F) hi hL with
    ⟨M, hM, hLM⟩
  let K : Finset α := Finset.univ \ M
  have hHM : H ⊆ M := hHL.trans hLM.1
  refine ⟨K, mem_largeComplementTrace_iff.mpr ⟨M, hM, hHM, rfl⟩, ?_⟩
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hxK
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxK).1,
      fun hxL => (Finset.mem_sdiff.mp hxK).2 (hLM.1 hxL)⟩
  · intro hEq
    have hComp : M = L := by
      apply Finset.ext
      intro x
      have hx := Finset.ext_iff.mp hEq x
      simpa [K] using not_congr hx
    exact hLM.2 (by simpa [hComp])

theorem adjacent_small_disjoint
    {F : Family α} {H : Finset α} (i : Nat) (hi : i + 1 < 7) :
    Disjoint
      (smallTrace (canonicalLayers 7 F ⟨i, by omega⟩) H)
      (smallTrace (canonicalLayers 7 F ⟨i + 1, by omega⟩) H) := by
  rw [Finset.disjoint_left]
  intro S hSi hSnext
  have hLayerI := (mem_smallTrace_iff.mp hSi).1
  have hLayerNext := (mem_smallTrace_iff.mp hSnext).1
  have hindices :
      (⟨i, by omega⟩ : Fin 7) ≠ ⟨i + 1, by omega⟩ := by
    intro hEq
    have hval : i = i + 1 := congrArg (fun j : Fin 7 => j.val) hEq
    omega
  exact Finset.disjoint_left.mp
    (canonicalLayers_pairwiseDisjoint 7 F hindices) hLayerI hLayerNext

theorem canonical_profile_lower
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α) :
    ∀ i : Fin 7,
      baselineProfile i ≤ (canonicalLayers 7 F i).card := by
  classical
  rcases exists_homogeneousAtom_of_signature_bound F hground with ⟨H, hH⟩
  rcases exists_external_of_card_lt_powerset hexternal with ⟨T, hTF⟩
  have hnonempty := canonicalLayers_nonempty_of_external hsat hTF
  have hsaturated := canonicalLayers_saturated_of_homogeneousAtom
    (by decide : 0 < 7) F H hsat hH
  let S : Fin 7 → G413.Hypergraph α := fun i =>
    smallTrace (canonicalLayers 7 F i) H
  let C : Fin 7 → G413.Hypergraph α := fun i =>
    largeComplementTrace (canonicalLayers 7 F i) H
  have htrace (i : Fin 7) :
      (S i).card + (C i).card = (canonicalLayers 7 F i).card :=
    canonicalLayer_trace_card_sum hH i
  have hSRows (i : Fin 7) : RowsCardAtLeast (S i) i.val :=
    smallTrace_rows_cardAtLeast i
  have hCRows (i : Fin 7) : RowsCardAtLeast (C i) (6 - i.val) := by
    simpa using largeComplementTrace_rows_cardAtLeast
      (k := 7) (F := F) (H := H) (by decide : 0 < 7) hsat hH i
  have hSClutter (i : Fin 7) : IsClutter (S i) :=
    smallTrace_isClutter (H := H) (hsaturated i).1
  have hCClutter (i : Fin 7) : IsClutter (C i) :=
    largeComplementTrace_isClutter (H := H) (hsaturated i).1
  have hmutual (i : Fin 7) (hi : 0 < i.val) (hitop : i.val + 1 < 7) :
      S i = blocker (C i) ∧ C i = blocker (S i) :=
    canonicalLayer_mutual_blockers (k := 7) (F := F) (H := H)
      (by decide : 0 < 7) hsat hH i hi hitop
  have hboth (i : Fin 7) (hi : 0 < i.val) (hitop : i.val + 1 < 7) :
      (S i).Nonempty ∧ (C i).Nonempty := by
    have hpositive : 0 < (S i).card + (C i).card := by
      rw [htrace i]
      exact Finset.card_pos.mpr (hnonempty i)
    exact both_nonempty_of_mutual_blockers (hmutual i hi hitop).1
      (hmutual i hi hitop).2
      (rowsNonempty_of_rowsCardAtLeast hi (hSRows i))
      (rowsNonempty_of_rowsCardAtLeast (by omega) (hCRows i)) hpositive
  have hLayer0 : 1 ≤ (canonicalLayers 7 F (0 : Fin 7)).card :=
    Finset.card_pos.mpr (hnonempty 0)
  have hLayer6 : 1 ≤ (canonicalLayers 7 F (6 : Fin 7)).card :=
    Finset.card_pos.mpr (hnonempty 6)
  have hLayer1 : 6 ≤ (canonicalLayers 7 F (1 : Fin 7)).card := by
    have h := mutual_blocker_total_card_lower
      (hmutual 1 (by decide) (by decide)).1
      (hmutual 1 (by decide) (by decide)).2
      (hboth 1 (by decide) (by decide)).1
      (hboth 1 (by decide) (by decide)).2 (hSRows 1) (hCRows 1)
    rwa [htrace 1] at h
  have hLayer5 : 6 ≤ (canonicalLayers 7 F (5 : Fin 7)).card := by
    have h := mutual_blocker_total_card_lower
      (hmutual 5 (by decide) (by decide)).1
      (hmutual 5 (by decide) (by decide)).2
      (hboth 5 (by decide) (by decide)).1
      (hboth 5 (by decide) (by decide)).2 (hSRows 5) (hCRows 5)
    rwa [htrace 5] at h
  have hLayer2 : 12 ≤ (canonicalLayers 7 F (2 : Fin 7)).card := by
    have h := AdjacentExact.mutual_blocker_total_card_ge_twelve
      (hSClutter 2) (hSRows 2) (by
        rw [← (hmutual 2 (by decide) (by decide)).2]
        exact hCRows 2)
    rw [← (hmutual 2 (by decide) (by decide)).2, htrace 2] at h
    exact h
  have hLayer4 : 12 ≤ (canonicalLayers 7 F (4 : Fin 7)).card := by
    have h := AdjacentExact.mutual_blocker_total_card_ge_twelve
      (hCClutter 4) (hCRows 4) (by
        rw [← (hmutual 4 (by decide) (by decide)).1]
        exact hSRows 4)
    rw [← (hmutual 4 (by decide) (by decide)).1,
      Nat.add_comm, htrace 4] at h
    exact h
  have hLayer3 : 14 ≤ (canonicalLayers 7 F (3 : Fin 7)).card := by
    have h := MiddleLower.mutual_blocker_total_card_ge_fourteen
      (hSClutter 3) (hCClutter 3)
      (hmutual 3 (by decide) (by decide)).1
      (hmutual 3 (by decide) (by decide)).2
      (hboth 3 (by decide) (by decide)).1
      (hboth 3 (by decide) (by decide)).2 (hSRows 3) (hCRows 3)
    rwa [htrace 3] at h
  intro i
  fin_cases i
  · simpa [baselineProfile] using hLayer0
  · simpa [baselineProfile] using hLayer1
  · simpa [baselineProfile] using hLayer2
  · simpa [baselineProfile] using hLayer3
  · simpa [baselineProfile] using hLayer4
  · simpa [baselineProfile] using hLayer5
  · simpa [baselineProfile] using hLayer6

theorem family_card_lower
    {F : Family α} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α) :
    52 ≤ F.card := by
  have hprofile := canonical_profile_lower hsat hground hexternal
  have hsum : (∑ i : Fin 7, baselineProfile i) ≤
      ∑ i : Fin 7, (canonicalLayers 7 F i).card :=
    Finset.sum_le_sum fun i _ => hprofile i
  have hprofileSum : (∑ i : Fin 7, baselineProfile i) = 52 := by decide
  rw [hprofileSum, sum_canonicalLayer_cards_eq hsat.1] at hsum
  exact hsum

end AiMathLab.P0054.SevenBaseline
