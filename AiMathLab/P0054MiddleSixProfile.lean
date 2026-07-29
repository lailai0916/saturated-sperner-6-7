import AiMathLab.P0054G419
import AiMathLab.P0054MiddleLower

/-!
# Common three-row kernel profile for six middle rows
-/

namespace AiMathLab.P0054.MiddleSixProfile

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem degreeThree_kernel_profile {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    {x : α} (hDegree : degree H x = 3)
    (hPairUpper : (pairRows (blocker (avoidPoint H x))).card ≤ 6)
    (hKernelBlockerUpper : (blocker (avoidPoint H x)).card ≤ 10) :
    ∃ A B C : Row α,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      avoidPoint H x = {A, B, C} ∧
      OrderedThreeKernelProfile
        (privatePart A B C).card
        (privatePart B A C).card
        (privatePart C A B).card
        (sharedPart A B C).card
        (sharedPart A C B).card
        (sharedPart B C A).card := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBKRows
  have hAK : A ∈ K := by simp [hK]
  have hBK : B ∈ K := by simp [hK]
  have hCK : C ∈ K := by simp [hK]
  have hAnotB : ¬A ⊆ B := fun h ↦ hAB (hKClutter hAK hBK h)
  have hBnotA : ¬B ⊆ A := fun h ↦ hAB (hKClutter hBK hAK h).symm
  have hAnotC : ¬A ⊆ C := fun h ↦ hAC (hKClutter hAK hCK h)
  have hCnotA : ¬C ⊆ A := fun h ↦ hAC (hKClutter hCK hAK h).symm
  have hBnotC : ¬B ⊆ C := fun h ↦ hBC (hKClutter hBK hCK h)
  have hCnotB : ¬C ⊆ B := fun h ↦ hBC (hKClutter hCK hBK h).symm
  have hPY : 0 < (privatePart A B C).card + (sharedPart A C B).card := by
    obtain ⟨u, huA, huB⟩ := Finset.not_subset.mp hAnotB
    by_cases huC : u ∈ C
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩⟩) _
  have hQZ : 0 < (privatePart B A C).card + (sharedPart B C A).card := by
    obtain ⟨u, huB, huA⟩ := Finset.not_subset.mp hBnotA
    by_cases huC : u ∈ C
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩⟩) _
  have hPX : 0 < (privatePart A B C).card + (sharedPart A B C).card := by
    obtain ⟨u, huA, huC⟩ := Finset.not_subset.mp hAnotC
    by_cases huB : u ∈ B
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩⟩) _
  have hRZ : 0 < (privatePart C A B).card + (sharedPart B C A).card := by
    obtain ⟨u, huC, huA⟩ := Finset.not_subset.mp hCnotA
    by_cases huB : u ∈ B
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩⟩) _
  have hQX : 0 < (privatePart B A C).card + (sharedPart A B C).card := by
    obtain ⟨u, huB, huC⟩ := Finset.not_subset.mp hBnotC
    by_cases huA : u ∈ A
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩⟩) _
  have hRY : 0 < (privatePart C A B).card + (sharedPart A C B).card := by
    obtain ⟨u, huC, huB⟩ := Finset.not_subset.mp hCnotB
    by_cases huA : u ∈ A
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩⟩) _
  have hACard := hKRows A hAK
  have hBCard := hKRows B hBK
  have hCCard := hKRows C hCK
  rw [threePart_union_card hNoCommon] at hACard
  rw [threePart_union_card_second hNoCommon] at hBCard
  rw [threePart_union_card_third hNoCommon] at hCCard
  have hPair :
      (sharedPart A B C).card * (sharedPart A C B).card +
        (sharedPart A B C).card * (sharedPart B C A).card +
        (sharedPart A C B).card * (sharedPart B C A).card +
        (sharedPart A B C).card * (privatePart C A B).card +
        (sharedPart A C B).card * (privatePart B A C).card +
        (sharedPart B C A).card * (privatePart A B C).card ≤ 6 :=
    (threePairGenerated_card_le_pairRows hK).trans
      (by simpa [K] using hPairUpper)
  have hTotal :
      (sharedPart A B C).card * (sharedPart A C B).card +
        (sharedPart A B C).card * (sharedPart B C A).card +
        (sharedPart A C B).card * (sharedPart B C A).card +
        (sharedPart A B C).card * (privatePart C A B).card +
        (sharedPart A C B).card * (privatePart B A C).card +
        (sharedPart B C A).card * (privatePart A B C).card +
        (privatePart A B C).card * (privatePart B A C).card *
          (privatePart C A B).card ≤ 10 :=
    (threeGeneratedRows_card_le_blocker hK hAB hAC hBC).trans
      (by simpa [K] using hKernelBlockerUpper)
  refine ⟨A, B, C, hAB, hAC, hBC, by simpa [K] using hK, ?_⟩
  exact orderedThreeKernelProfile_of_bounds
    (privatePart A B C).card (privatePart B A C).card
    (privatePart C A B).card (sharedPart A B C).card
    (sharedPart A C B).card (sharedPart B C A).card
    hACard hBCard hCCard hPY hQZ hPX hRZ hQX hRY hPair hTotal

end AiMathLab.P0054.MiddleSixProfile
