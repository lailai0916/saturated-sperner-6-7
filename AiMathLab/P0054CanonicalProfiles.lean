import AiMathLab.P0054CanonicalBlocker
import AiMathLab.SaturatedSperner.HomogeneousAtomExistence

/-!
# Quantitative canonical profiles

This file turns the canonical decomposition around a homogeneous atom into
the numerical profile used in the lower-bound arguments.  Every member of
layer `i` has at least `i` points; following the saturated layers upward
shows that the complement of a large member has at least `k - 1 - i`
points.  The small traces and complementary large traces are mutual
blockers and their cardinalities add to the cardinality of the layer.
-/

universe u

namespace AiMathLab.P0054.CanonicalProfiles

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413
open AiMathLab.P0054.CanonicalBlocker

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem hasStrictChainEndingAt_card_lower
    {d : Nat} {F : Family α} {B : Finset α}
    (hB : HasStrictChainEndingAt d F B) :
    d ≤ B.card := by
  induction d generalizing B with
  | zero => omega
  | succ d ih =>
      rcases hB with ⟨hBF, A, hA, hAB⟩
      have hAcard := ih hA
      have hlt := Finset.card_lt_card hAB
      omega

theorem canonicalLayer_row_card_lower
    {F : Family α} {i : Nat} {D : Finset α}
    (hD : D ∈ canonicalLayer F i) :
    i ≤ D.card :=
  hasStrictChainEndingAt_card_lower
    (canonicalLayer_hasStrictChainEndingAt F hD)

theorem layer_member_card_add_span_le_ground
    {k : Nat} (A : Fin k → Family α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hlayered : IsLayered A)
    (start span : Nat) (hbound : start + span < k)
    {D : Finset α} (hD : D ∈ A ⟨start, by omega⟩) :
    D.card + span ≤ Fintype.card α := by
  induction span generalizing start D with
  | zero =>
      simpa using Finset.card_le_univ D
  | succ span ih =>
      have hstep : start + 1 < k := by omega
      rcases layered_step_up A hsat hdisj hlayered hstep hD with
        ⟨E, hE, hDE⟩
      have htailBound : start + 1 + span < k := by omega
      have htail := ih (start := start + 1) htailBound hE
      have hcard := Finset.card_lt_card hDE
      omega

theorem canonicalLayer_largeComplement_card_lower
    {k : Nat} (hk : 0 < k) {F : Family α} {H : Finset α}
    (hsat : IsSaturatedKSperner k F)
    (hH : IsHomogeneousAtom F H)
    {i : Fin k} {L : Finset α}
    (hL : L ∈ canonicalLayers k F i) :
    k - 1 - i.val ≤ (Finset.univ \ L).card := by
  let A := canonicalLayers k F
  have hsaturated : ∀ j, IsSaturatedAntichain (A j) :=
    canonicalLayers_saturated_of_homogeneousAtom hk F H hsat hH
  have hbound : i.val + (k - 1 - i.val) < k := by omega
  have hgrowth := layer_member_card_add_span_le_ground A hsaturated
    (canonicalLayers_pairwiseDisjoint k F)
    (canonicalLayers_layered k F) i.val (k - 1 - i.val) hbound hL
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ L)]
  simpa using (by omega : k - 1 - i.val ≤ Fintype.card α - L.card)

theorem complement_injective :
    Function.Injective (fun S : Finset α => Finset.univ \ S) := by
  intro S T hST
  apply Finset.ext
  intro x
  have hx := Finset.ext_iff.mp hST x
  simpa using not_congr hx

theorem largeComplementTrace_card
    (A : Family α) (H : Finset α) :
    (largeComplementTrace A H).card = (LargePart A H).card := by
  exact Finset.card_image_iff.mpr complement_injective.injOn

theorem trace_card_sum
    {A : Family α} {H : Finset α}
    (hblock : IsAtomBlock A H) (hHne : H.Nonempty) :
    (smallTrace A H).card + (largeComplementTrace A H).card = A.card := by
  rw [smallTrace, largeComplementTrace_card]
  rw [← Finset.card_union_of_disjoint (smallPart_largePart_disjoint hHne)]
  rw [atomBlock_small_large_cover hblock]

theorem canonicalLayer_trace_card_sum
    {k : Nat} {F : Family α} {H : Finset α}
    (hH : IsHomogeneousAtom F H) (i : Fin k) :
    (smallTrace (canonicalLayers k F i) H).card +
        (largeComplementTrace (canonicalLayers k F i) H).card =
      (canonicalLayers k F i).card := by
  have hblockLayer : IsAtomBlock (canonicalLayers k F i) H := by
    intro S hS
    exact hH.1.1 S (canonicalLayer_subset F i.val hS)
  have hHpos : 0 < H.card := lt_trans (by decide : 0 < 2) hH.2
  exact trace_card_sum hblockLayer (Finset.card_pos.mp hHpos)

theorem sum_canonicalLayer_cards_eq
    {k : Nat} {F : Family α} (hsp : IsKSperner k F) :
    (∑ i : Fin k, (canonicalLayers k F i).card) = F.card := by
  have hpairwise :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (canonicalLayers k F) := by
    intro i hi j hj hij
    exact canonicalLayers_pairwiseDisjoint k F hij
  rw [← Finset.card_biUnion hpairwise]
  exact congrArg Finset.card (layerUnion_canonicalLayers_eq hsp)

theorem exists_external_of_card_lt_powerset
    {F : Family α} (hcard : F.card < 2 ^ Fintype.card α) :
    ∃ T : Finset α, T ∉ F := by
  have hpowerset :
      (Finset.univ.powerset : Finset (Finset α)).card =
        2 ^ Fintype.card α := by simp
  have hlt : F.card <
      (Finset.univ.powerset : Finset (Finset α)).card := by
    simpa [hpowerset] using hcard
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨T, hTp, hTF⟩
  exact ⟨T, hTF⟩

theorem both_nonempty_of_mutual_blockers
    {S C : AiMathLab.P0054.G413.Hypergraph α}
    (hSC : S = blocker C) (hCS : C = blocker S)
    (hSRows : RowsNonempty S) (hCRows : RowsNonempty C)
    (hpositive : 0 < S.card + C.card) :
    S.Nonempty ∧ C.Nonempty := by
  have hsome : S.Nonempty ∨ C.Nonempty := by
    by_contra hnone
    push Not at hnone
    have hSempty : S = ∅ := hnone.1
    have hCempty : C = ∅ := hnone.2
    simp [hSempty, hCempty] at hpositive
  rcases hsome with hS | hC
  · refine ⟨hS, ?_⟩
    rw [hCS]
    exact blocker_nonempty hSRows
  · refine ⟨?_, hC⟩
    rw [hSC]
    exact blocker_nonempty hCRows

theorem mutual_blocker_total_card_lower
    {S C : AiMathLab.P0054.G413.Hypergraph α} {a b : Nat}
    (hSC : S = blocker C) (hCS : C = blocker S)
    (hS : S.Nonempty) (hC : C.Nonempty)
    (hSRows : RowsCardAtLeast S a)
    (hCRows : RowsCardAtLeast C b) :
    a + b ≤ S.card + C.card := by
  rcases hS with ⟨P, hPS⟩
  rcases hC with ⟨Q, hQC⟩
  have hPb : P ∈ blocker C := by simpa [← hSC] using hPS
  have hQb : Q ∈ blocker S := by simpa [← hCS] using hQC
  have hPle := minimalTransversal_card_le_rows (mem_blocker.mp hPb)
  have hQle := minimalTransversal_card_le_rows (mem_blocker.mp hQb)
  have haC : a ≤ C.card := (hSRows P hPS).trans hPle
  have hbS : b ≤ S.card := (hCRows Q hQC).trans hQle
  omega

theorem canonicalLayers_nonempty_of_external
    {k : Nat} {F : Family α} (hsat : IsSaturatedKSperner k F)
    {T : Finset α} (hTF : T ∉ F) :
    ∀ i : Fin k, (canonicalLayers k F i).Nonempty := by
  have hthrough :=
    (isSaturatedKSperner_iff_hasStrictChainThrough k F).mp hsat |>.2 T hTF
  rcases hthrough with ⟨c, hc⟩
  rcases erase_inserted_of_strictChainWitness hTF hc with
    ⟨hlen, hchain, hmemErase, hcomparable⟩
  intro i
  let d := c.erase T
  let idx : Fin d.length := Fin.cast hlen.symm i
  let U := d.get idx
  refine ⟨U, ?_⟩
  have halign := strictChainList_uses_each_canonical_layer
    hsat.1 hchain hlen i i
  exact halign.mpr rfl

theorem smallTrace_rows_cardAtLeast
    {k : Nat} {F : Family α} {H : Finset α} (i : Fin k) :
    RowsCardAtLeast (smallTrace (canonicalLayers k F i) H) i.val := by
  intro S hS
  exact canonicalLayer_row_card_lower (mem_smallTrace_iff.mp hS).1

theorem largeComplementTrace_rows_cardAtLeast
    {k : Nat} (hk : 0 < k) {F : Family α} {H : Finset α}
    (hsat : IsSaturatedKSperner k F)
    (hH : IsHomogeneousAtom F H) (i : Fin k) :
    RowsCardAtLeast (largeComplementTrace (canonicalLayers k F i) H)
      (k - 1 - i.val) := by
  intro C hC
  rcases mem_largeComplementTrace_iff.mp hC with ⟨L, hL, hHL, rfl⟩
  exact canonicalLayer_largeComplement_card_lower hk hsat hH hL

theorem rowsNonempty_of_rowsCardAtLeast
    {G : AiMathLab.P0054.G413.Hypergraph α} {r : Nat}
    (hr : 0 < r) (hG : RowsCardAtLeast G r) : RowsNonempty G := by
  intro E hE
  exact Finset.card_pos.mp (by have := hG E hE; omega)

theorem canonicalLayer_mutual_blockers
    {k : Nat} (hk : 0 < k) {F : Family α} {H : Finset α}
    (hsat : IsSaturatedKSperner k F)
    (hH : IsHomogeneousAtom F H)
    (i : Fin k) (hi : 0 < i.val) (hitop : i.val + 1 < k) :
    smallTrace (canonicalLayers k F i) H =
        blocker (largeComplementTrace (canonicalLayers k F i) H) ∧
      largeComplementTrace (canonicalLayers k F i) H =
        blocker (smallTrace (canonicalLayers k F i) H) := by
  have hlayers := canonicalLayers_saturated_of_homogeneousAtom hk F H hsat hH
  have hsmallRows := smallTrace_rows_cardAtLeast (F := F) (H := H) i
  have hlargeRows := largeComplementTrace_rows_cardAtLeast hk hsat hH i
  have hblockLayer : IsAtomBlock (canonicalLayers k F i) H := by
    intro S hS
    exact hH.1.1 S (canonicalLayer_subset F i.val hS)
  have hHcard : 1 < H.card := lt_trans (by decide) hH.2
  apply mutual_blockers (A := canonicalLayers k F i) (H := H)
    (hlayers i) hblockLayer hHcard
  · exact rowsNonempty_of_rowsCardAtLeast hi hsmallRows
  · exact rowsNonempty_of_rowsCardAtLeast (by omega) hlargeRows

end AiMathLab.P0054.CanonicalProfiles
