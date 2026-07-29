import AiMathLab.P0054FanoAdjacentEightFiveSound

/-!
# Structural tools for the Fano eight-plus-five branch

An extra row containing a point inactive in a base family cannot decrease
the number of minimal transversals.  The proof below gives the explicit
injection used later for the non-core branch.
-/

namespace AiMathLab.P0054.FanoAdjacentEightFiveBasics

open AiMathLab.P0054.G413

noncomputable def inactiveExtensionLift {alpha : Type*}
    [DecidableEq alpha] (extra : G413.Row alpha) (fresh : alpha)
    (row : G413.Row alpha) : G413.Row alpha :=
  if Disjoint row extra then insert fresh row else row

theorem inactiveExtensionLift_mem_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {extra : G413.Row alpha} {fresh : alpha}
    (hFreshExtra : fresh ∈ extra)
    (hFreshInactive : ∀ row ∈ H, fresh ∉ row)
    {row : G413.Row alpha} (hRow : row ∈ blocker H) :
    inactiveExtensionLift extra fresh row ∈ blocker (insert extra H) := by
  classical
  have hFreshRow : fresh ∉ row :=
    blocker_rows_avoid_inactive hFreshInactive row hRow
  have hRowMinimal := mem_blocker.mp hRow
  by_cases hDisjoint : Disjoint row extra
  · rw [inactiveExtensionLift, if_pos hDisjoint]
    apply mem_blocker.mpr
    have hTransversal : IsTransversal (insert extra H) (insert fresh row) := by
      intro source hSource
      simp only [Finset.mem_insert] at hSource
      rcases hSource with rfl | hSource
      · exact ⟨fresh, by simp, hFreshExtra⟩
      · obtain ⟨point, hPointRow, hPointSource⟩ :=
          hRowMinimal.prop source hSource
        exact ⟨point, by simp [hPointRow], hPointSource⟩
    apply hTransversal.minimal_of_privateRows
    intro point hPointLift
    simp only [Finset.mem_insert] at hPointLift
    rcases hPointLift with rfl | hPointRow
    · refine ⟨extra, by simp, by simp, hFreshExtra, ?_⟩
      intro other hOtherLift hOtherExtra
      simp only [Finset.mem_insert] at hOtherLift
      rcases hOtherLift with hOtherFresh | hOtherRow
      · exact hOtherFresh
      · exact (Finset.disjoint_left.mp hDisjoint
          hOtherRow hOtherExtra).elim
    · obtain ⟨source, hPrivate⟩ :=
        hRowMinimal.exists_privateRow hPointRow
      refine ⟨source, by simp [hPrivate.1], by simp [hPointRow],
        hPrivate.2.2.1, ?_⟩
      intro other hOtherLift hOtherSource
      simp only [Finset.mem_insert] at hOtherLift
      rcases hOtherLift with hOtherFresh | hOtherRow
      · subst other
        exact (hFreshInactive source hPrivate.1 hOtherSource).elim
      · exact hPrivate.2.2.2 hOtherRow hOtherSource
  · rw [inactiveExtensionLift, if_neg hDisjoint]
    apply mem_blocker.mpr
    have hTransversal : IsTransversal (insert extra H) row := by
      intro source hSource
      simp only [Finset.mem_insert] at hSource
      rcases hSource with rfl | hSource
      · obtain ⟨point, hPointRow, hPointExtra⟩ :=
          Finset.not_disjoint_iff.mp hDisjoint
        exact ⟨point, hPointRow, hPointExtra⟩
      · exact hRowMinimal.prop source hSource
    apply hTransversal.minimal_of_privateRows
    intro point hPointRow
    obtain ⟨source, hPrivate⟩ :=
      hRowMinimal.exists_privateRow hPointRow
    exact ⟨source, by simp [hPrivate.1], hPrivate.2.1,
      hPrivate.2.2.1, hPrivate.2.2.2⟩

theorem blocker_card_le_blocker_insert_of_inactive_point
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {extra : G413.Row alpha} {fresh : alpha}
    (hFreshExtra : fresh ∈ extra)
    (hFreshInactive : ∀ row ∈ H, fresh ∉ row) :
    (blocker H).card ≤ (blocker (insert extra H)).card := by
  classical
  let lift : G413.Row alpha → G413.Row alpha :=
    inactiveExtensionLift extra fresh
  have hFreshBlocker : ∀ row ∈ blocker H, fresh ∉ row := by
    intro row hRow
    exact blocker_rows_avoid_inactive hFreshInactive row hRow
  have hLiftInj : Set.InjOn lift (blocker H) := by
    intro left hLeft right hRight hEq
    have hFreshLeft := hFreshBlocker left hLeft
    have hFreshRight := hFreshBlocker right hRight
    by_cases hLeftDisjoint : Disjoint left extra <;>
        by_cases hRightDisjoint : Disjoint right extra
    · have hErase := congrArg (Finset.erase · fresh) hEq
      simpa [lift, inactiveExtensionLift, hLeftDisjoint,
        hRightDisjoint, hFreshLeft, hFreshRight] using hErase
    · have hFreshRightMem : fresh ∈ right := by
        have : fresh ∈ lift left := by
          simp [lift, inactiveExtensionLift, hLeftDisjoint]
        rw [hEq] at this
        simpa [lift, inactiveExtensionLift, hRightDisjoint] using this
      exact (hFreshRight hFreshRightMem).elim
    · have hFreshLeftMem : fresh ∈ left := by
        have : fresh ∈ lift right := by
          simp [lift, inactiveExtensionLift, hRightDisjoint]
        rw [← hEq] at this
        simpa [lift, inactiveExtensionLift, hLeftDisjoint] using this
      exact (hFreshLeft hFreshLeftMem).elim
    · simpa [lift, inactiveExtensionLift, hLeftDisjoint,
        hRightDisjoint] using hEq
  have hImageSubset : (blocker H).image lift ⊆
      blocker (insert extra H) := by
    intro imageRow hImageRow
    obtain ⟨row, hRow, rfl⟩ := Finset.mem_image.mp hImageRow
    exact inactiveExtensionLift_mem_blocker
      hFreshExtra hFreshInactive hRow
  calc
    (blocker H).card = ((blocker H).image lift).card :=
      (Finset.card_image_of_injOn hLiftInj).symm
    _ ≤ (blocker (insert extra H)).card :=
      Finset.card_le_card hImageSubset

/-- Replacing one row by a larger row does not lose any blocker row when
the newly added points are inactive in all the other rows.  A blocker row
of `insert reduced H` avoids those inactive points, so its private witness
`reduced` (when it is needed) may be replaced by `full`. -/
theorem blocker_insert_subset_of_row_extension
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {reduced full : G413.Row alpha}
    (hReducedFull : reduced ⊆ full)
    (hNewInactive : ∀ point ∈ full \ reduced,
      ∀ row ∈ H, point ∉ row) :
    blocker (insert reduced H) ⊆ blocker (insert full H) := by
  classical
  intro transversal hTransversal
  have hMinimal := mem_blocker.mp hTransversal
  have hAvoidNew : ∀ point ∈ full \ reduced, point ∉ transversal := by
    intro point hPointNew
    exact blocker_rows_avoid_inactive (H := insert reduced H) (by
      intro row hRow
      simp only [Finset.mem_insert] at hRow
      rcases hRow with rfl | hRowH
      · exact (Finset.mem_sdiff.mp hPointNew).2
      · exact hNewInactive point hPointNew row hRowH)
      transversal hTransversal
  apply mem_blocker.mpr
  have hMeetsFull : IsTransversal (insert full H) transversal := by
    intro row hRow
    simp only [Finset.mem_insert] at hRow
    rcases hRow with rfl | hRowH
    · obtain ⟨point, hPointTransversal, hPointReduced⟩ :=
        hMinimal.prop reduced (by simp)
      exact ⟨point, hPointTransversal, hReducedFull hPointReduced⟩
    · exact hMinimal.prop row (by simp [hRowH])
  apply hMeetsFull.minimal_of_privateRows
  intro point hPointTransversal
  obtain ⟨row, hPrivate⟩ :=
    hMinimal.exists_privateRow hPointTransversal
  have hRowFamily := hPrivate.1
  simp only [Finset.mem_insert] at hRowFamily
  rcases hRowFamily with hRowReduced | hRowH
  · subst row
    refine ⟨full, by simp, hPrivate.2.1,
      hReducedFull hPrivate.2.2.1, ?_⟩
    intro other hOtherTransversal hOtherFull
    by_cases hOtherReduced : other ∈ reduced
    · exact hPrivate.2.2.2 hOtherTransversal hOtherReduced
    · exact (hAvoidNew other
        (Finset.mem_sdiff.mpr ⟨hOtherFull, hOtherReduced⟩)
        hOtherTransversal).elim
  · exact ⟨row, by simp [hRowH], hPrivate.2.1,
      hPrivate.2.2.1, hPrivate.2.2.2⟩

theorem blocker_card_le_of_row_extension
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {reduced full : G413.Row alpha}
    (hReducedFull : reduced ⊆ full)
    (hNewInactive : ∀ point ∈ full \ reduced,
      ∀ row ∈ H, point ∉ row) :
    (blocker (insert reduced H)).card ≤
      (blocker (insert full H)).card :=
  Finset.card_le_card
    (blocker_insert_subset_of_row_extension hReducedFull hNewInactive)

theorem isClutter_insert_row_reduction
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {reduced full : G413.Row alpha}
    {fresh : alpha}
    (hFullClutter : IsClutter (insert full H))
    (hReducedFull : reduced ⊆ full)
    (hFreshReduced : fresh ∈ reduced)
    (hFreshInactive : ∀ row ∈ H, fresh ∉ row) :
    IsClutter (insert reduced H) := by
  intro left hLeft right hRight hSubset
  simp only [Finset.mem_insert] at hLeft hRight
  rcases hLeft with rfl | hLeftH <;>
      rcases hRight with rfl | hRightH
  · rfl
  · exact (hFreshInactive right hRightH
      (hSubset hFreshReduced)).elim
  · have hLeftFull : left ⊆ full := hSubset.trans hReducedFull
    have hLeftEqFull : left = full :=
      hFullClutter (by simp [hLeftH]) (by simp) hLeftFull
    have hFreshLeft : fresh ∈ left := by
      rw [hLeftEqFull]
      exact hReducedFull hFreshReduced
    exact (hFreshInactive left hLeftH hFreshLeft).elim
  · exact hFullClutter (by simp [hLeftH]) (by simp [hRightH]) hSubset

theorem isClutter_image_of_injOn_biUnion
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    {family : G413.Hypergraph alpha} (pointMap : alpha → beta)
    (hClutter : IsClutter family)
    (hPointMap : Set.InjOn pointMap (family.biUnion id)) :
    IsClutter (family.image fun row ↦ row.image pointMap) := by
  intro imageLeft hImageLeft imageRight hImageRight hSubset
  obtain ⟨left, hLeft, rfl⟩ := Finset.mem_image.mp hImageLeft
  obtain ⟨right, hRight, rfl⟩ := Finset.mem_image.mp hImageRight
  have hSourceSubset : left ⊆ right := by
    intro point hPointLeft
    have hMappedLeft : pointMap point ∈ left.image pointMap :=
      Finset.mem_image.mpr ⟨point, hPointLeft, rfl⟩
    obtain ⟨other, hOtherRight, hOtherEq⟩ :=
      Finset.mem_image.mp (hSubset hMappedLeft)
    have hPointActive : point ∈ family.biUnion id :=
      Finset.mem_biUnion.mpr ⟨left, hLeft, hPointLeft⟩
    have hOtherActive : other ∈ family.biUnion id :=
      Finset.mem_biUnion.mpr ⟨right, hRight, hOtherRight⟩
    have hPointEq : point = other :=
      hPointMap hPointActive hOtherActive hOtherEq.symm
    simpa [hPointEq] using hOtherRight
  rw [hClutter hLeft hRight hSourceSubset]

end AiMathLab.P0054.FanoAdjacentEightFiveBasics
