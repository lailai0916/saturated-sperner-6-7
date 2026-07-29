import AiMathLab.P0054G419.KernelCStar

namespace AiMathLab.P0054.G419

open G413

theorem sixTen_degreeThree_kernelC_impossible_explicit {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3)
    {A B C : Row α}
    (hK : avoidPoint H x = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hPrivateA : (privatePart A B C).card = 1)
    (hPrivateB : (privatePart B A C).card = 1)
    (hPrivateC : (privatePart C A B).card = 3)
    (hSharedAB : (sharedPart A B C).card = 2)
    (hSharedAC : (sharedPart A C B).card = 0)
    (hSharedBC : (sharedPart B C A).card = 0) : False := by
  classical
  let K := avoidPoint H x
  let PA := privatePart A B C
  let PB := privatePart B A C
  let PC := privatePart C A B
  have hPairExpression :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card = 6 := by
    simp [hPrivateA, hPrivateB, hPrivateC, hSharedAB, hSharedAC, hSharedBC]
  have hPrivateProduct :
      (privatePart A B C).card *
          (privatePart B A C).card *
          (privatePart C A B).card = 3 := by
    simp [hPrivateA, hPrivateB, hPrivateC]
  obtain ⟨hPairCard, hTripleCard, hBKCard, hBlockerDegree,
      hAvoidCard, hTripleSubset⟩ :=
    sixTen_degreeThree_kernelC_counts
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC hPairExpression hPrivateProduct
  obtain ⟨a, hPAEq⟩ := Finset.card_eq_one.mp (by simpa [PA] using hPrivateA)
  obtain ⟨b, hPBEq⟩ := Finset.card_eq_one.mp (by simpa [PB] using hPrivateB)
  have hPCCard : PC.card = 3 := by simpa [PC] using hPrivateC
  obtain ⟨hPAPB, hPAPC, hPBPC⟩ := privatePart_pairwise_disjoint A B C
  have haPA : a ∈ PA := by change a ∈ privatePart A B C; rw [hPAEq]; simp
  have hbPB : b ∈ PB := by change b ∈ privatePart B A C; rw [hPBEq]; simp
  have hab : a ≠ b := by
    intro hab
    exact Finset.disjoint_left.mp hPAPB haPA (hab ▸ hbPB)
  have haPC : a ∉ PC := fun haPC ↦ Finset.disjoint_left.mp hPAPC haPA haPC
  have hbPC : b ∉ PC := fun hbPC ↦ Finset.disjoint_left.mp hPBPC hbPB hbPC
  have hTripleEq :
      rowsCardExactly (blocker K) 3 = threeStarRows a b PC := by
    rw [threeRow_triple_blockers (by simpa [K] using hK) hAB hAC hBC]
    ext E
    constructor
    · intro hE
      obtain ⟨u, huPA, v, hvPB, c, hcPC, huvcE⟩ := mem_tripleChoiceRows.mp hE
      have hua : u = a := by rw [hPAEq] at huPA; simpa using huPA
      have hvb : v = b := by rw [hPBEq] at hvPB; simpa using hvPB
      exact mem_threeStarRows.mpr ⟨c, hcPC, by simpa [hua, hvb] using huvcE⟩
    · intro hE
      obtain ⟨c, hcPC, habcE⟩ := mem_threeStarRows.mp hE
      exact mem_tripleChoiceRows.mpr
        ⟨a, by simp [hPAEq], b, by simp [hPBEq], c, hcPC, habcE⟩
  let T := avoidPoint (blocker H) x
  have hStarSubset : threeStarRows a b PC ⊆ T := by
    intro E hE
    apply hTripleSubset
    rw [hTripleEq]
    exact hE
  have hStarCard : (threeStarRows a b PC).card = 3 := by
    rw [← hTripleEq]
    simpa [K] using hTripleCard
  have hStrict : threeStarRows a b PC ⊂ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hStarSubset, ?_⟩
    intro hEq
    have hCardEq := congrArg Finset.card hEq
    have hTCard : T.card = 4 := by simpa [T] using hAvoidCard
    omega
  obtain ⟨Q, hQT, hQNotStar⟩ := Finset.exists_of_ssubset hStrict
  have hTForm : T = insert Q (threeStarRows a b PC) := by
    have hInsertSubset : insert Q (threeStarRows a b PC) ⊆ T := by
      intro E hE
      simp only [Finset.mem_insert] at hE
      rcases hE with rfl | hEStar
      · exact hQT
      · exact hStarSubset hEStar
    have hInsertCard : (insert Q (threeStarRows a b PC)).card = 4 := by
      rw [Finset.card_insert_of_notMem hQNotStar, hStarCard]
    have hTCard : T.card = 4 := by simpa [T] using hAvoidCard
    exact (Finset.eq_of_subset_of_card_le hInsertSubset (by omega)).symm
  have hTRows : RowsCardAtLeast T 3 := by
    intro E hET
    exact hBRows E (mem_avoidPoint.mp (by simpa [T] using hET)).1
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  have hBlockerTRows : RowsCardAtLeast (blocker T) 2 := by
    simpa [T] using blocker_avoidPoint_rows_cardAtLeast_two hDualRows x
  have hSeven : 7 ≤ (blocker T).card :=
    kernelC_star_blocker_card_ge_seven hTForm hPCCard hab haPC hbPC hTRows hBlockerTRows
  have hBlockerT : blocker T = residual H x := by
    calc
      blocker T = blocker (avoidPoint (blocker H) x) := by rfl
      _ = residual (blocker (blocker H)) x := blocker_avoidPoint (blocker_isClutter H) x
      _ = residual H x := by rw [blocker_involution hHClutter]
  have hUpper : (blocker T).card ≤ 6 := by
    rw [hBlockerT]
    exact (residual_card_le H x).trans_eq hHCard
  omega

def IsKernelCProfile
    (p q r x12 x13 x23 : Nat) : Prop :=
  (p = 1 ∧ q = 1 ∧ r = 3 ∧ x12 = 2 ∧ x13 = 0 ∧ x23 = 0) ∨
  (p = 1 ∧ q = 3 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 2 ∧ x23 = 0) ∨
  (p = 3 ∧ q = 1 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 0 ∧ x23 = 2)

theorem sixTen_degreeThree_kernelC_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3)
    {A B C : Row α}
    (hK : avoidPoint H x = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hProfile : IsKernelCProfile
      (privatePart A B C).card
      (privatePart B A C).card
      (privatePart C A B).card
      (sharedPart A B C).card
      (sharedPart A C B).card
      (sharedPart B C A).card) : False := by
  unfold IsKernelCProfile at hProfile
  rcases hProfile with hProfile | hProfile | hProfile
  · exact sixTen_degreeThree_kernelC_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK hAB hAC hBC
      hProfile.1 hProfile.2.1 hProfile.2.2.1
      hProfile.2.2.2.1 hProfile.2.2.2.2.1 hProfile.2.2.2.2.2
  · have hK' : avoidPoint H x = {A, C, B} := by
      rw [hK]
      ext E
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact sixTen_degreeThree_kernelC_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK' hAC hAB hBC.symm
      (by simpa [privatePart, Finset.union_comm] using hProfile.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.2)
  · have hK' : avoidPoint H x = {B, C, A} := by
      rw [hK]
      ext E
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact sixTen_degreeThree_kernelC_impossible_explicit
      hHClutter hHCard hHRows hBRows hBCard hDegree
      hK' hBC hAB.symm hAC.symm
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.2.2.1)
      (by simpa [privatePart, Finset.union_comm] using hProfile.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.2)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.1)
      (by simpa [sharedPart, Finset.inter_comm] using hProfile.2.2.2.2.1)

end AiMathLab.P0054.G419
