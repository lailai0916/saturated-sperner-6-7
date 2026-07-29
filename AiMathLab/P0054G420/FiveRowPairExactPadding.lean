import AiMathLab.P0054G420.FiveRowPairExactFiniteActual

namespace AiMathLab.P0054.G420

open G413 G419

def optionImageRow {alpha : Type*} [DecidableEq alpha]
    (E : G413.Row alpha) : G413.Row (Option alpha) :=
  E.image some

def padWithSingleton {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) : G413.Hypergraph (Option alpha) :=
  insert {none} (H.image optionImageRow)

def paddedBlockerRow {alpha : Type*} [DecidableEq alpha]
    (T : G413.Row alpha) : G413.Row (Option alpha) :=
  insert none (optionImageRow T)

theorem optionImageRow_injective {alpha : Type*} [DecidableEq alpha] :
    Function.Injective (optionImageRow : G413.Row alpha → G413.Row (Option alpha)) := by
  intro E F hEF
  apply Finset.image_injective (Option.some_injective alpha) hEF

theorem paddedBlockerRow_injective {alpha : Type*} [DecidableEq alpha] :
    Function.Injective (paddedBlockerRow : G413.Row alpha → G413.Row (Option alpha)) := by
  intro E F hEF
  have hErase := congrArg (fun S ↦ S.erase none) hEF
  apply Finset.image_injective (Option.some_injective alpha)
  simpa [paddedBlockerRow, optionImageRow] using hErase

@[simp]
theorem none_not_mem_optionImageRow {alpha : Type*} [DecidableEq alpha]
    (E : G413.Row alpha) : none ∉ optionImageRow E := by
  simp [optionImageRow]

@[simp]
theorem optionImageRow_card {alpha : Type*} [DecidableEq alpha]
    (E : G413.Row alpha) : (optionImageRow E).card = E.card := by
  exact Finset.card_image_of_injective _ (Option.some_injective alpha)

@[simp]
theorem paddedBlockerRow_card {alpha : Type*} [DecidableEq alpha]
    (E : G413.Row alpha) : (paddedBlockerRow E).card = E.card + 1 := by
  rw [paddedBlockerRow, Finset.card_insert_of_notMem, optionImageRow_card]
  exact none_not_mem_optionImageRow E

theorem blocker_insert_singleton_eq_image_insert
    {beta : Type*} [Fintype beta] [DecidableEq beta]
    {J : G413.Hypergraph beta} {z : beta}
    (hAvoid : ∀ E ∈ J, z ∉ E) :
    blocker (insert {z} J) = (blocker J).image (insert z) := by
  classical
  ext S
  constructor
  · intro hS
    have hSMin := mem_blocker.mp hS
    have hzS : z ∈ S := by
      obtain ⟨y, hyS, hySingleton⟩ := hSMin.prop {z} (by simp)
      have hyz : y = z := by simpa using hySingleton
      simpa [hyz] using hyS
    let T := S.erase z
    have hTTransversal : IsTransversal J T := by
      intro E hEJ
      obtain ⟨y, hyS, hyE⟩ := hSMin.prop E (by simp [hEJ])
      have hyz : y ≠ z := fun hyz ↦ hAvoid E hEJ (hyz ▸ hyE)
      exact ⟨y, Finset.mem_erase.mpr ⟨hyz, hyS⟩, hyE⟩
    have hTMinimal : IsMinimalTransversal J T := by
      apply hTTransversal.minimal_of_privateRows
      intro y hyT
      have hyS : y ∈ S := Finset.mem_of_mem_erase hyT
      obtain ⟨E, hEPad, hyS', hyE, hUnique⟩ :=
        hSMin.exists_privateRow hyS
      have hEJ : E ∈ J := by
        simp only [Finset.mem_insert] at hEPad
        rcases hEPad with hESingleton | hEJ
        · have hyz : y ≠ z := (Finset.mem_erase.mp hyT).1
          have : y = z := by simpa [hESingleton] using hyE
          exact (hyz this).elim
        · exact hEJ
      refine ⟨E, hEJ, hyT, hyE, ?_⟩
      intro u huT huE
      exact hUnique (Finset.mem_of_mem_erase huT) huE
    apply Finset.mem_image.mpr
    refine ⟨T, mem_blocker.mpr hTMinimal, ?_⟩
    exact Finset.insert_erase hzS
  · intro hS
    obtain ⟨T, hTBlocker, rfl⟩ := Finset.mem_image.mp hS
    have hzT : z ∉ T := (mem_blocker.mp hTBlocker).avoids_inactive hAvoid
    apply mem_blocker.mpr
    have hTransversal : IsTransversal (insert {z} J) (insert z T) := by
      intro E hE
      simp only [Finset.mem_insert] at hE
      rcases hE with rfl | hEJ
      · exact ⟨z, by simp, by simp⟩
      · obtain ⟨y, hyT, hyE⟩ := (mem_blocker.mp hTBlocker).prop E hEJ
        exact ⟨y, by simp [hyT], hyE⟩
    apply hTransversal.minimal_of_privateRows
    intro y hyLift
    simp only [Finset.mem_insert] at hyLift
    rcases hyLift with hyz | hyT
    · subst y
      refine ⟨{z}, by simp, by simp, by simp, ?_⟩
      intro u huLift huSingleton
      simpa using huSingleton
    · obtain ⟨E, hEJ, hyT', hyE, hUnique⟩ :=
        (mem_blocker.mp hTBlocker).exists_privateRow hyT
      refine ⟨E, by simp [hEJ], by simp [hyT'], hyE, ?_⟩
      intro u huLift huE
      simp only [Finset.mem_insert] at huLift
      rcases huLift with rfl | huT
      · exact (hAvoid E hEJ huE).elim
      · exact hUnique huT huE

theorem blocker_padWithSingleton
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) :
    blocker (padWithSingleton H) =
      (blocker H).image paddedBlockerRow := by
  classical
  rw [padWithSingleton, blocker_insert_singleton_eq_image_insert]
  · have hImageBlocker :
        blocker (H.image optionImageRow) =
          (blocker H).image optionImageRow := by
      unfold optionImageRow
      exact blocker_image_eq_of_injective (H := H)
        (g := Option.some) (Option.some_injective alpha)
    rw [hImageBlocker]
    ext S
    simp [paddedBlockerRow]
  · intro E hE
    obtain ⟨R, -, rfl⟩ := Finset.mem_image.mp hE
    exact none_not_mem_optionImageRow R

theorem blocker_padWithSingleton_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) :
    (blocker (padWithSingleton H)).card = (blocker H).card := by
  classical
  rw [blocker_padWithSingleton, Finset.card_image_iff.mpr]
  exact paddedBlockerRow_injective.injOn

theorem blocker_padWithSingleton_rows
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {n : Nat}
    (hRows : RowsCardAtLeast (blocker H) n) :
    RowsCardAtLeast (blocker (padWithSingleton H)) (n + 1) := by
  classical
  intro E hE
  rw [blocker_padWithSingleton] at hE
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hE
  rw [paddedBlockerRow_card]
  exact Nat.add_le_add_right (hRows T hT) 1

theorem pairRows_padWithSingleton
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) :
    pairRows (padWithSingleton H) =
      (pairRows H).image optionImageRow := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨hEPad, hECard⟩ := Finset.mem_filter.mp hE
    simp only [padWithSingleton, Finset.mem_insert] at hEPad
    rcases hEPad with hESingleton | hEImage
    · subst E
      simp at hECard
    · obtain ⟨T, hTH, rfl⟩ := Finset.mem_image.mp hEImage
      exact Finset.mem_image.mpr
        ⟨T, Finset.mem_filter.mpr ⟨hTH, by simpa using hECard⟩, rfl⟩
  · intro hE
    obtain ⟨T, hTPair, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hTH, hTCard⟩ := Finset.mem_filter.mp hTPair
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa using hTCard⟩
    simp only [padWithSingleton, Finset.mem_insert]
    exact Or.inr (Finset.mem_image.mpr ⟨T, hTH, rfl⟩)

theorem pairRows_padWithSingleton_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) :
    (pairRows (padWithSingleton H)).card = (pairRows H).card := by
  classical
  rw [pairRows_padWithSingleton, Finset.card_image_iff.mpr]
  exact optionImageRow_injective.injOn

theorem pairRows_blocker_padWithSingleton_eq_empty
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hRows : RowsCardAtLeast (blocker H) 2) :
    pairRows (blocker (padWithSingleton H)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro E hE
  obtain ⟨hEBlocker, hECard⟩ := Finset.mem_filter.mp hE
  rw [blocker_padWithSingleton] at hEBlocker
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hEBlocker
  rw [paddedBlockerRow_card] at hECard
  have hLower := hRows T hT
  omega

theorem padWithSingleton_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (hRows : RowsCardAtLeast H 1) :
    (padWithSingleton H).card = H.card + 1 := by
  classical
  rw [padWithSingleton, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_iff.mpr]
    exact optionImageRow_injective.injOn
  · intro hSingleton
    obtain ⟨E, hEH, hImage⟩ := Finset.mem_image.mp hSingleton
    have hNone : none ∈ optionImageRow E := by
      rw [hImage]
      simp
    exact none_not_mem_optionImageRow E hNone

theorem padWithSingleton_isClutter
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} (hH : IsClutter H)
    (hRows : RowsCardAtLeast H 1) :
    IsClutter (padWithSingleton H) := by
  classical
  intro A hA B hB hAB
  simp only [padWithSingleton, Finset.mem_insert] at hA hB
  rcases hA with rfl | hA <;> rcases hB with rfl | hB
  · rfl
  · exfalso
    obtain ⟨E, hEH, rfl⟩ := Finset.mem_image.mp hB
    exact none_not_mem_optionImageRow E (hAB (by simp))
  · obtain ⟨E, hEH, rfl⟩ := Finset.mem_image.mp hA
    have hEmpty : E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxE
      have : some x ∈ ({none} : G413.Row (Option alpha)) :=
        hAB (Finset.mem_image.mpr ⟨x, hxE, rfl⟩)
      simp at this
    have hLower := hRows E hEH
    simp [hEmpty] at hLower
  · obtain ⟨E, hEH, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨F, hFH, hImageEq⟩ := Finset.mem_image.mp hB
    have hEF : E ⊆ F := by
      intro x hxE
      have hSome : some x ∈ optionImageRow F := by
        rw [hImageEq]
        exact hAB (Finset.mem_image.mpr ⟨x, hxE, rfl⟩)
      simpa [optionImageRow] using hSome
    have hEq := hH hEH hFH hEF
    calc
      optionImageRow E = optionImageRow F := congrArg optionImageRow hEq
      _ = B := hImageEq

end AiMathLab.P0054.G420
