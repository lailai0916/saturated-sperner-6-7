import AiMathLab.P0054G418.SixDegreeBounds
import AiMathLab.P0054G419.ThreeRowSeven

namespace AiMathLab.P0054.G419

open G413

noncomputable def avoidBlockerLift {α : Type*} [DecidableEq α]
    (G : G413.Hypergraph α) (y : α) (T : Row α) : Row α := by
  classical
  exact if IsTransversal G T then T else insert y T

theorem blocker_avoidPoint_avoids {α : Type*}
    [Fintype α] [DecidableEq α]
    (G : G413.Hypergraph α) (y : α)
    {T : Row α} (hT : T ∈ blocker (avoidPoint G y)) :
    y ∉ T := by
  exact blocker_rows_avoid_inactive
    (fun E hE ↦ (mem_avoidPoint.mp hE).2) T hT

theorem avoidBlockerLift_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {G : G413.Hypergraph α} {y : α}
    {T : Row α} (hT : T ∈ blocker (avoidPoint G y)) :
    avoidBlockerLift G y T ∈ blocker G := by
  classical
  have hTmin := mem_blocker.mp hT
  by_cases hTransversal : IsTransversal G T
  · change (if IsTransversal G T then T else insert y T) ∈ blocker G
    rw [if_pos hTransversal]
    apply mem_blocker.mpr
    apply hTransversal.minimal_of_privateRows
    intro x hxT
    obtain ⟨E, hEPrivate⟩ := hTmin.exists_privateRow hxT
    exact ⟨E, (mem_avoidPoint.mp hEPrivate.1).1,
      hEPrivate.2.1, hEPrivate.2.2.1, hEPrivate.2.2.2⟩
  · change (if IsTransversal G T then T else insert y T) ∈ blocker G
    rw [if_neg hTransversal]
    have hLiftTransversal : IsTransversal G (insert y T) := by
      intro E hEG
      by_cases hyE : y ∈ E
      · exact ⟨y, by simp, hyE⟩
      · obtain ⟨x, hxT, hxE⟩ :=
          hTmin.prop E (mem_avoidPoint.mpr ⟨hEG, hyE⟩)
        exact ⟨x, by simp [hxT], hxE⟩
    apply mem_blocker.mpr
    apply hLiftTransversal.minimal_of_privateRows
    intro x hxLift
    simp only [Finset.mem_insert] at hxLift
    rcases hxLift with rfl | hxT
    · simp only [IsTransversal] at hTransversal
      push Not at hTransversal
      obtain ⟨E, hEG, hMiss⟩ := hTransversal
      have hyE : x ∈ E := by
        by_contra hyE
        obtain ⟨x, hxT, hxE⟩ :=
          hTmin.prop E (mem_avoidPoint.mpr ⟨hEG, hyE⟩)
        exact hMiss x hxT hxE
      refine ⟨E, hEG, by simp, hyE, ?_⟩
      intro z hzLift hzE
      simp only [Finset.mem_insert] at hzLift
      rcases hzLift with hzy | hzT
      · exact hzy
      · exact (hMiss z hzT hzE).elim
    · obtain ⟨E, hEPrivate⟩ := hTmin.exists_privateRow hxT
      have hyE : y ∉ E := (mem_avoidPoint.mp hEPrivate.1).2
      refine ⟨E, (mem_avoidPoint.mp hEPrivate.1).1,
        by simp [hxT], hEPrivate.2.2.1, ?_⟩
      intro z hzLift hzE
      simp only [Finset.mem_insert] at hzLift
      rcases hzLift with hzy | hzT'
      · exact (hyE (hzy ▸ hzE)).elim
      · exact hEPrivate.2.2.2 hzT' hzE

theorem avoidBlockerLift_erase {α : Type*}
    [Fintype α] [DecidableEq α]
    (G : G413.Hypergraph α) (y : α)
    {T : Row α} (hT : T ∈ blocker (avoidPoint G y)) :
    (avoidBlockerLift G y T).erase y = T := by
  classical
  have hyT := blocker_avoidPoint_avoids G y hT
  unfold avoidBlockerLift
  split
  · exact Finset.erase_eq_of_notMem hyT
  · simp [hyT]

theorem avoidBlockerLift_injective {α : Type*}
    [Fintype α] [DecidableEq α]
    (G : G413.Hypergraph α) (y : α) :
    Set.InjOn (avoidBlockerLift G y)
      (↑(blocker (avoidPoint G y)) : Set (Row α)) := by
  intro T hT U hU hEq
  calc
    T = (avoidBlockerLift G y T).erase y := (avoidBlockerLift_erase G y hT).symm
    _ = (avoidBlockerLift G y U).erase y := by rw [hEq]
    _ = U := avoidBlockerLift_erase G y hU

theorem blocker_avoidPoint_card_le_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    (G : G413.Hypergraph α) (y : α) :
    (blocker (avoidPoint G y)).card ≤ (blocker G).card := by
  classical
  let lifts := (blocker (avoidPoint G y)).image (avoidBlockerLift G y)
  have hLiftsSubset : lifts ⊆ blocker G := by
    intro T hT
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
    exact avoidBlockerLift_mem_blocker hU
  calc
    (blocker (avoidPoint G y)).card = lifts.card :=
      (Finset.card_image_iff.mpr (avoidBlockerLift_injective G y)).symm
    _ ≤ (blocker G).card := Finset.card_le_card hLiftsSubset

theorem avoidBlockerLift_card_le {α : Type*}
    [DecidableEq α]
    (G : G413.Hypergraph α) (y : α) (T : Row α) :
    (avoidBlockerLift G y T).card ≤ T.card + 1 := by
  classical
  unfold avoidBlockerLift
  split
  · omega
  · exact Finset.card_insert_le y T

theorem blocker_avoidPoint_rows_cardAtLeast_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {G : G413.Hypergraph α}
    (hBRows : RowsCardAtLeast (blocker G) 3) (y : α) :
    RowsCardAtLeast (blocker (avoidPoint G y)) 2 := by
  intro T hT
  have hLiftMember := avoidBlockerLift_mem_blocker hT
  have hLiftLarge := hBRows _ hLiftMember
  have hLiftUpper := avoidBlockerLift_card_le G y T
  omega

theorem avoidPoint_isClutter {α : Type*} [DecidableEq α]
    {G : G413.Hypergraph α} (hG : IsClutter G) (y : α) :
    IsClutter (avoidPoint G y) := by
  intro A hA B hB hAB
  exact hG (mem_avoidPoint.mp hA).1 (mem_avoidPoint.mp hB).1 hAB

theorem blockerSide_maxDegreeAtMost_six {α : Type*}
    [Fintype α] [DecidableEq α]
    {G : G413.Hypergraph α}
    (hGClutter : IsClutter G)
    (hGCard : G.card = 10)
    (hGRows : RowsCardAtLeast G 3)
    (hBRows : RowsCardAtLeast (blocker G) 3)
    (hBCard : (blocker G).card = 6) :
    MaxDegreeAtMost G 6 := by
  classical
  intro y
  by_contra hDegree
  have hDegreeLower : 7 ≤ degree G y := by omega
  let K := avoidPoint G y
  have hKCardUpper : K.card ≤ 3 := by
    have hPartition := card_avoidPoint_add_degree G y
    simpa [K, hGCard] using (show (avoidPoint G y).card ≤ 3 by omega)
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hGRows E (mem_avoidPoint.mp hEK).1
  have hKRowsNonempty : RowsNonempty K := by
    intro E hEK
    exact Finset.card_pos.mp ((show 0 < E.card by
      have := hKRows E hEK
      omega))
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows y
  have hBKNonempty : (blocker K).Nonempty := blocker_nonempty hKRowsNonempty
  obtain ⟨T, hTBK⟩ := hBKNonempty
  have hKCardLower : 2 ≤ K.card := by
    have hTLower := hBKRows T hTBK
    have hTUpper := minimalTransversal_card_le_rows (mem_blocker.mp hTBK)
    omega
  have hKCardCases : K.card = 2 ∨ K.card = 3 := by omega
  rcases hKCardCases with hKCard | hKCard
  · obtain ⟨P, Q, hPQ, hKForm⟩ := Finset.card_eq_two.mp hKCard
    have hPK : P ∈ K := by simp [hKForm]
    have hQK : Q ∈ K := by simp [hKForm]
    have hPLarge := hKRows P hPK
    have hQLarge := hKRows Q hQK
    have hPairRows : RowsCardAtLeast (blocker ({P, Q} : G413.Hypergraph α)) 2 := by
      simpa [hKForm] using hBKRows
    have hProduct := twoRow_blocker_card_ge_product hPairRows
    have hAvoidLower : 9 ≤ (blocker K).card := by
      rw [hKForm]
      calc
        9 = 3 * 3 := rfl
        _ ≤ P.card * Q.card := Nat.mul_le_mul hPLarge hQLarge
        _ ≤ (blocker ({P, Q} : G413.Hypergraph α)).card := hProduct
    have hLiftUpper : (blocker K).card ≤ (blocker G).card := by
      simpa [K] using blocker_avoidPoint_card_le_blocker G y
    omega
  · have hKClutter : IsClutter K := by
      simpa [K] using avoidPoint_isClutter hGClutter y
    have hAvoidLower : 7 ≤ (blocker K).card :=
      threeRow_blocker_card_ge_seven hKClutter hKCard hKRows hBKRows
    have hLiftUpper : (blocker K).card ≤ (blocker G).card := by
      simpa [K] using blocker_avoidPoint_card_le_blocker G y
    omega

end AiMathLab.P0054.G419
