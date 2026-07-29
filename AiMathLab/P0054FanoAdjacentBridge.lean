import AiMathLab.P0054MiddleFourteenFano
import AiMathLab.P0054SevenBaseline

/-!
# Reducing the fourteen-member middle layer to one Fano-adjacent principle

If the middle canonical layer has fourteen members, its two trace clutters
are the same Fano clutter.  At least one of the two adjacent canonical layers
has at most thirteen members.  Downward layering, or upward layering followed
by complementation, then puts a distinct proper predecessor below every Fano
line.  This file isolates the remaining finite Fano-adjacent exclusion behind
one arbitrary-finite principle.
-/

universe u

namespace AiMathLab.P0054.FanoAdjacentBridge

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413
open AiMathLab.P0054.CanonicalBlocker
open AiMathLab.P0054.CanonicalProfiles
open AiMathLab.P0054.MiddleSevenEightFinite

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

def FanoAdjacentImpossiblePrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] : Prop :=
  ∀ {middle small large : G413.Hypergraph alpha}
      {pointMap : alpha → G420.MiddleFourModelPoint},
    middle.card = 7 →
    (∀ line ∈ middle, line.card = 3) →
    (∀ first ∈ middle, ∀ second ∈ middle, first ≠ second →
      (first ∩ second).card = 1) →
    Set.InjOn pointMap (middle.biUnion id) →
    sevenEightFanoBase =
      middle.image (fun row ↦ row.image pointMap) →
    small = blocker large →
    large = blocker small →
    RowsCardAtLeast small 2 →
    RowsCardAtLeast large 4 →
    (∀ line ∈ middle, ∃ row ∈ small, row ⊂ line) →
    (∀ row ∈ large, ∃ line ∈ middle, line ⊂ row) →
    small.card + large.card ≤ 13 → False

theorem smallTrace_step_down
    {F : Family alpha} {H : Finset alpha}
    (i : Nat) (hi : i + 1 < 7)
    {line : Row alpha}
    (hLine : line ∈ smallTrace
      (canonicalLayers 7 F ⟨i + 1, hi⟩) H) :
    ∃ row ∈ smallTrace (canonicalLayers 7 F ⟨i, by omega⟩) H,
      row ⊂ line := by
  obtain ⟨hLineLayer, hLineDisjoint⟩ := mem_smallTrace_iff.mp hLine
  obtain ⟨row, hRowLayer, hRowLine⟩ :=
    canonicalLayer_succ_predecessor F i hLineLayer
  refine ⟨row, mem_smallTrace_iff.mpr ⟨hRowLayer, ?_⟩, hRowLine⟩
  exact Finset.disjoint_left.mpr fun point hPointRow hPointH ↦
    Finset.disjoint_left.mp hLineDisjoint (hRowLine.1 hPointRow) hPointH

theorem largeComplementTrace_step_up
    {F : Family alpha} {H : Finset alpha}
    (hsat : IsSaturatedKSperner 7 F)
    (hhomogeneous : IsHomogeneousAtom F H)
    (i : Nat) (hi : i + 1 < 7)
    {line : Row alpha}
    (hLine : line ∈
      largeComplementTrace (canonicalLayers 7 F ⟨i, by omega⟩) H) :
    ∃ row ∈ largeComplementTrace
        (canonicalLayers 7 F ⟨i + 1, hi⟩) H,
      row ⊂ line := by
  classical
  obtain ⟨source, hSourceLayer, hHSource, rfl⟩ :=
    mem_largeComplementTrace_iff.mp hLine
  let layers := canonicalLayers 7 F
  have hSaturated : ∀ i, IsSaturatedAntichain (layers i) :=
    canonicalLayers_saturated_of_homogeneousAtom
      (by decide : 0 < 7) F H hsat hhomogeneous
  obtain ⟨target, hTargetLayer, hSourceTarget⟩ :=
    layered_step_up layers hSaturated
      (canonicalLayers_pairwiseDisjoint 7 F)
      (canonicalLayers_layered 7 F)
      (i := i) hi (by simpa [layers] using hSourceLayer)
  let row : Row alpha := Finset.univ \ target
  have hHTarget : H ⊆ target := hHSource.trans hSourceTarget.1
  have hRowMember : row ∈
      largeComplementTrace (canonicalLayers 7 F ⟨i + 1, hi⟩) H := by
    apply mem_largeComplementTrace_iff.mpr
    exact ⟨target, by simpa [layers] using hTargetLayer, hHTarget, rfl⟩
  refine ⟨row, hRowMember, ?_⟩
  change (Finset.univ \ target) ⊂ (Finset.univ \ source)
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro point hPoint
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ point, fun hPointSource ↦
      (Finset.mem_sdiff.mp hPoint).2 (hSourceTarget.1 hPointSource)⟩
  · intro hRowsEqual
    exact hSourceTarget.ne (complement_injective hRowsEqual).symm

theorem fourteen_middle_impossible_of_fano_adjacent
    (hAdjacent : FanoAdjacentImpossiblePrinciple alpha)
    {F : Family alpha} (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card alpha)
    (hFamilyCard : F.card ≤ 54)
    (hMiddle : (canonicalLayers 7 F (3 : Fin 7)).card = 14) : False := by
  classical
  rcases exists_homogeneousAtom_of_signature_bound F hground with
    ⟨H, hHomogeneous⟩
  let S : Fin 7 → G413.Hypergraph alpha := fun i ↦
    smallTrace (canonicalLayers 7 F i) H
  let C : Fin 7 → G413.Hypergraph alpha := fun i ↦
    largeComplementTrace (canonicalLayers 7 F i) H
  have hTrace (i : Fin 7) :
      (S i).card + (C i).card = (canonicalLayers 7 F i).card := by
    exact canonicalLayer_trace_card_sum hHomogeneous i
  have hSRows (i : Fin 7) : RowsCardAtLeast (S i) i.val := by
    exact smallTrace_rows_cardAtLeast (F := F) (H := H) i
  have hCRows (i : Fin 7) : RowsCardAtLeast (C i) (6 - i.val) := by
    simpa using largeComplementTrace_rows_cardAtLeast
      (k := 7) (F := F) (H := H) (by decide : 0 < 7)
        hsat hHomogeneous i
  have hSClutter (i : Fin 7) : IsClutter (S i) := by
    exact smallTrace_isClutter (H := H)
      (canonicalLayers_saturated_of_homogeneousAtom
        (by decide : 0 < 7) F H hsat hHomogeneous i).1
  have hMutual (i : Fin 7) (hi : 0 < i.val) (hitop : i.val + 1 < 7) :
      S i = blocker (C i) ∧ C i = blocker (S i) := by
    exact canonicalLayer_mutual_blockers
      (k := 7) (F := F) (H := H) (by decide : 0 < 7)
        hsat hHomogeneous i hi hitop
  have hMiddleTotal : (S 3).card + (blocker (S 3)).card = 14 := by
    rw [← (hMutual 3 (by decide) (by decide)).2, hTrace 3, hMiddle]
  obtain ⟨hS3Card, _hB3Card, hSelf, hFanoRows, hFanoPairs,
      pointMap, hPointMap, hModel⟩ :=
    AiMathLab.P0054.MiddleFourteenFano.middle_fourteen_is_fano
      (hSClutter 3) hMiddleTotal (hSRows 3)
        (by
          rw [← (hMutual 3 (by decide) (by decide)).2]
          simpa using hCRows 3)
  have hC3Eq : C 3 = S 3 := by
    exact (hMutual 3 (by decide) (by decide)).2.trans hSelf.symm
  have hLayerSum :
      (canonicalLayers 7 F (2 : Fin 7)).card +
        (canonicalLayers 7 F (4 : Fin 7)).card ≤ 26 := by
    have hProfile :=
      AiMathLab.P0054.SevenBaseline.canonical_profile_lower
        hsat hground
        (by
          have hFamilyGround : F.card < Fintype.card alpha := by
            have hPower := F.card.lt_two_pow_self
            omega
          exact hFamilyGround.trans
            (Fintype.card alpha).lt_two_pow_self)
    have h0 := hProfile (0 : Fin 7)
    have h1 := hProfile (1 : Fin 7)
    have h5 := hProfile (5 : Fin 7)
    have h6 := hProfile (6 : Fin 7)
    have hSum := sum_canonicalLayer_cards_eq hsat.1
    change 1 ≤ (canonicalLayers 7 F (0 : Fin 7)).card at h0
    change 1 ≤ (canonicalLayers 7 F (6 : Fin 7)).card at h6
    simp [AiMathLab.P0054.SevenBaseline.baselineProfile,
      Fin.sum_univ_succ] at h1 h5 hSum
    omega
  by_cases hLower :
      (canonicalLayers 7 F (2 : Fin 7)).card ≤ 13
  · have hAdjacentTotal : (S 2).card + (C 2).card ≤ 13 := by
      rw [hTrace 2]
      exact hLower
    exact hAdjacent hS3Card hFanoRows hFanoPairs hPointMap hModel
      (hMutual 2 (by decide) (by decide)).1
      (hMutual 2 (by decide) (by decide)).2
      (by simpa using hSRows 2) (by simpa using hCRows 2)
      (by
        intro line hLine
        exact smallTrace_step_down (F := F) (H := H) 2 (by decide)
          (by simpa [S] using hLine))
      (by
        intro row hRow
        obtain ⟨line, hLine, hLineRow⟩ :=
          largeComplementTrace_step_up
            (F := F) (H := H) hsat hHomogeneous 2 (by decide)
            (by simpa [C] using hRow)
        have hLine' : line ∈ S 3 := by
          rw [← hC3Eq]
          simpa [C] using hLine
        exact ⟨line, hLine', hLineRow⟩)
      hAdjacentTotal
  · have hUpper :
        (canonicalLayers 7 F (4 : Fin 7)).card ≤ 13 := by
      omega
    have hAdjacentTotal : (C 4).card + (S 4).card ≤ 13 := by
      rw [Nat.add_comm, hTrace 4]
      exact hUpper
    have hUpperPointMap : Set.InjOn pointMap ((C 3).biUnion id) := by
      simpa [hC3Eq] using hPointMap
    have hUpperModel : sevenEightFanoBase =
        (C 3).image (fun row ↦ row.image pointMap) := by
      simpa [hC3Eq] using hModel
    have hC3Card : (C 3).card = 7 := by
      rw [hC3Eq]
      exact hS3Card
    have hC3Rows : ∀ line ∈ C 3, line.card = 3 := by
      rw [hC3Eq]
      exact hFanoRows
    have hC3Pairs : ∀ first ∈ C 3, ∀ second ∈ C 3,
        first ≠ second → (first ∩ second).card = 1 := by
      rw [hC3Eq]
      exact hFanoPairs
    exact hAdjacent hC3Card hC3Rows hC3Pairs
      hUpperPointMap hUpperModel
      (hMutual 4 (by decide) (by decide)).2
      (hMutual 4 (by decide) (by decide)).1
      (by simpa using hCRows 4) (by simpa using hSRows 4)
      (by
        intro line hLine
        exact largeComplementTrace_step_up
          (F := F) (H := H) hsat hHomogeneous 3 (by decide)
          (by simpa [C] using hLine))
      (by
        intro row hRow
        obtain ⟨line, hLine, hLineRow⟩ :=
          smallTrace_step_down (F := F) (H := H) 3 (by decide)
            (by simpa [S] using hRow)
        exact ⟨line, by simpa [S, hC3Eq] using hLine, hLineRow⟩)
      hAdjacentTotal

end AiMathLab.P0054.FanoAdjacentBridge
