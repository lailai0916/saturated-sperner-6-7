import AiMathLab.P0054CanonicalProfiles
import AiMathLab.P0054Sat6Parameterized30
import AiMathLab.P0054Sat6

/-!
# The exact stable six-Sperner bound

The lower bound is proved for every finite ground set on which the incidence
pigeonhole supplies a homogeneous atom and an external set exists.  The six
canonical layers then contribute at least `1, 5, 9, 9, 5, 1` members.
-/

universe u

namespace AiMathLab.P0054.Sat6Exact

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413
open AiMathLab.P0054.CanonicalBlocker
open AiMathLab.P0054.CanonicalProfiles

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem family_card_lower
    {F : Family α} (hsat : IsSaturatedKSperner 6 F)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α)
    (hexternal : F.card < 2 ^ Fintype.card α) :
    30 ≤ F.card := by
  classical
  rcases exists_homogeneousAtom_of_signature_bound F hground with ⟨H, hH⟩
  rcases exists_external_of_card_lt_powerset hexternal with ⟨T, hTF⟩
  have hnonempty := canonicalLayers_nonempty_of_external hsat hTF
  have hsaturated :=
    canonicalLayers_saturated_of_homogeneousAtom (by decide : 0 < 6)
      F H hsat hH

  let S : Fin 6 → AiMathLab.P0054.G413.Hypergraph α := fun i =>
    smallTrace (canonicalLayers 6 F i) H
  let C : Fin 6 → AiMathLab.P0054.G413.Hypergraph α := fun i =>
    largeComplementTrace (canonicalLayers 6 F i) H

  have htrace (i : Fin 6) :
      (S i).card + (C i).card = (canonicalLayers 6 F i).card := by
    exact canonicalLayer_trace_card_sum hH i
  have hSRows (i : Fin 6) : RowsCardAtLeast (S i) i.val := by
    exact smallTrace_rows_cardAtLeast (F := F) (H := H) i
  have hCRows (i : Fin 6) : RowsCardAtLeast (C i) (5 - i.val) := by
    simpa using largeComplementTrace_rows_cardAtLeast
      (k := 6) (F := F) (H := H) (by decide : 0 < 6) hsat hH i
  have hSClutter (i : Fin 6) : IsClutter (S i) := by
    exact smallTrace_isClutter (H := H) (hsaturated i).1
  have hCClutter (i : Fin 6) : IsClutter (C i) := by
    exact largeComplementTrace_isClutter (H := H) (hsaturated i).1

  have hLayer0 : 1 ≤ (canonicalLayers 6 F (0 : Fin 6)).card :=
    Finset.card_pos.mpr (hnonempty 0)
  have hLayer5 : 1 ≤ (canonicalLayers 6 F (5 : Fin 6)).card :=
    Finset.card_pos.mpr (hnonempty 5)

  have hLayer1 : 5 ≤ (canonicalLayers 6 F (1 : Fin 6)).card := by
    have hm := canonicalLayer_mutual_blockers (k := 6) (F := F) (H := H)
      (by decide : 0 < 6) hsat hH (1 : Fin 6) (by decide) (by decide)
    have hSN := rowsNonempty_of_rowsCardAtLeast (by decide : 0 < 1) (hSRows 1)
    have hCN := rowsNonempty_of_rowsCardAtLeast (by decide : 0 < 4) (hCRows 1)
    have hpositive : 0 < (S 1).card + (C 1).card := by
      rw [htrace 1]
      exact Finset.card_pos.mpr (hnonempty 1)
    have hboth := both_nonempty_of_mutual_blockers hm.1 hm.2 hSN hCN hpositive
    have hlower := mutual_blocker_total_card_lower hm.1 hm.2
      hboth.1 hboth.2 (hSRows 1) (hCRows 1)
    rw [htrace 1] at hlower
    simpa using hlower

  have hLayer4 : 5 ≤ (canonicalLayers 6 F (4 : Fin 6)).card := by
    have hm := canonicalLayer_mutual_blockers (k := 6) (F := F) (H := H)
      (by decide : 0 < 6) hsat hH (4 : Fin 6) (by decide) (by decide)
    have hSN := rowsNonempty_of_rowsCardAtLeast (by decide : 0 < 4) (hSRows 4)
    have hCN := rowsNonempty_of_rowsCardAtLeast (by decide : 0 < 1) (hCRows 4)
    have hpositive : 0 < (S 4).card + (C 4).card := by
      rw [htrace 4]
      exact Finset.card_pos.mpr (hnonempty 4)
    have hboth := both_nonempty_of_mutual_blockers hm.1 hm.2 hSN hCN hpositive
    have hlower := mutual_blocker_total_card_lower hm.1 hm.2
      hboth.1 hboth.2 (hSRows 4) (hCRows 4)
    rw [htrace 4] at hlower
    simpa using hlower

  have hLayer2 : 9 ≤ (canonicalLayers 6 F (2 : Fin 6)).card := by
    have hm := canonicalLayer_mutual_blockers (k := 6) (F := F) (H := H)
      (by decide : 0 < 6) hsat hH (2 : Fin 6) (by decide) (by decide)
    have hlower := AiMathLab.P0054.Sat6.local_lower (S 2) (C 2)
      (hSClutter 2) (hCClutter 2) hm.1 hm.2 (hSRows 2) (hCRows 2)
    rw [htrace 2] at hlower
    exact hlower

  have hLayer3 : 9 ≤ (canonicalLayers 6 F (3 : Fin 6)).card := by
    have hm := canonicalLayer_mutual_blockers (k := 6) (F := F) (H := H)
      (by decide : 0 < 6) hsat hH (3 : Fin 6) (by decide) (by decide)
    have hlower := AiMathLab.P0054.Sat6.local_lower (C 3) (S 3)
      (hCClutter 3) (hSClutter 3) hm.2 hm.1 (hCRows 3) (hSRows 3)
    rw [Nat.add_comm, htrace 3] at hlower
    exact hlower

  let profile : Fin 6 → Nat := ![1, 5, 9, 9, 5, 1]
  have hprofileLower (i : Fin 6) :
      profile i ≤ (canonicalLayers 6 F i).card := by
    fin_cases i
    · simpa [profile] using hLayer0
    · simpa [profile] using hLayer1
    · simpa [profile] using hLayer2
    · simpa [profile] using hLayer3
    · simpa [profile] using hLayer4
    · simpa [profile] using hLayer5
  have hsumLower :
      (∑ i : Fin 6, profile i) ≤
        ∑ i : Fin 6, (canonicalLayers 6 F i).card := by
    exact Finset.sum_le_sum fun i hi => hprofileLower i
  have hprofileSum : (∑ i : Fin 6, profile i) = 30 := by
    decide
  rw [hprofileSum, sum_canonicalLayer_cards_eq hsat.1] at hsumLower
  exact hsumLower

end AiMathLab.P0054.Sat6Exact
