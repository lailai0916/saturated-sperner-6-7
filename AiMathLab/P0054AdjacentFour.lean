import AiMathLab.P0054AdjacentLower

/-!
# The four-set branch of the adjacent blocker bound

For a distinguished row `E` in a four-row clutter, blockers are separated by
their unique point in `E`.  The corresponding local residual families keep
all actual points and therefore support exact cardinality injections.
-/

namespace AiMathLab.P0054.AdjacentFour

open AiMathLab.P0054.G413
open AiMathLab.P0054
open AiMathLab.P0054.AdjacentLower

noncomputable def localResidual {alpha : Type*} [DecidableEq alpha]
    (E A B C : G413.Row alpha) (x : alpha) : G413.Hypergraph alpha := by
  classical
  exact (({A, B, C} : G413.Hypergraph alpha).filter fun R ↦ x ∉ R).image
    fun R ↦ R \ E

theorem localResidual_rows_avoid_base {alpha : Type*} [DecidableEq alpha]
    (E A B C : G413.Row alpha) (x : alpha) :
    ∀ R ∈ localResidual E A B C x, ∀ y ∈ R, y ∉ E := by
  classical
  intro R hR y hyR hyE
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
  exact (Finset.mem_sdiff.mp hyR).2 hyE

theorem card_base_sdiff_le_residual {alpha : Type*} [DecidableEq alpha]
    {E A : G413.Row alpha} (hCard : E.card ≤ A.card) :
    (E \ A).card ≤ (A \ E).card := by
  have hE := Finset.card_sdiff_add_card_inter E A
  have hA := Finset.card_sdiff_add_card_inter A E
  rw [Finset.inter_comm A E] at hA
  omega

theorem blocker_card_ge_of_rows_cardAtLeast {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {D : G413.Hypergraph alpha} {k : Nat}
    (hD : D.Nonempty) (hRows : RowsCardAtLeast D k) :
    k ≤ (blocker D).card := by
  classical
  obtain ⟨R, hRD⟩ := hD
  obtain ⟨M, hMMin, hMR⟩ := exists_minimize_subset hRD
  have hMRow : M ∈ D := minimize_subset D hMMin
  have hMCard : k ≤ M.card := hRows M hMRow
  have hMDual : M ∈ blocker (blocker (minimize D)) := by
    rw [blocker_involution (minimize_isClutter D)]
    exact hMMin
  have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hMDual)
  rw [blocker_minimize] at hUpper
  exact hMCard.trans hUpper

theorem localResidual_nonempty {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha} {x : alpha}
    (hH : H = {E, A, B, C}) (hxE : x ∈ E)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    (localResidual E A B C x).Nonempty := by
  classical
  by_contra hEmpty
  have hxA : x ∈ A := by
    by_contra hxA
    have hMember : A \ E ∈ localResidual E A B C x := by
      apply Finset.mem_image.mpr
      exact ⟨A, Finset.mem_filter.mpr ⟨by simp, hxA⟩, rfl⟩
    exact hEmpty ⟨A \ E, hMember⟩
  have hxB : x ∈ B := by
    by_contra hxB
    have hMember : B \ E ∈ localResidual E A B C x := by
      apply Finset.mem_image.mpr
      exact ⟨B, Finset.mem_filter.mpr ⟨by simp, hxB⟩, rfl⟩
    exact hEmpty ⟨B \ E, hMember⟩
  have hxC : x ∈ C := by
    by_contra hxC
    have hMember : C \ E ∈ localResidual E A B C x := by
      apply Finset.mem_image.mpr
      exact ⟨C, Finset.mem_filter.mpr ⟨by simp, hxC⟩, rfl⟩
    exact hEmpty ⟨C \ E, hMember⟩
  have hSingleton : IsTransversal H {x} := by
    intro R hRH
    have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
      simpa [hH] using hRH
    rcases hCases with hRE | hRA | hRB | hRC
    · exact ⟨x, by simp, hRE ▸ hxE⟩
    · exact ⟨x, by simp, hRA ▸ hxA⟩
    · exact ⟨x, by simp, hRB ▸ hxB⟩
    · exact ⟨x, by simp, hRC ▸ hxC⟩
  exact false_of_small_transversal hBRows hSingleton (by simp)

theorem localBlocker_rows_avoid_base {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E A B C R : G413.Row alpha} {x : alpha}
    (hR : R ∈ blocker (localResidual E A B C x)) :
    ∀ y ∈ R, y ∉ E := by
  intro y hyR hyE
  have hyInactive : ∀ P ∈ localResidual E A B C x, y ∉ P := by
    intro P hP hyP
    exact localResidual_rows_avoid_base E A B C x P hP y hyP hyE
  exact (blocker_rows_avoid_inactive hyInactive R hR) hyR

theorem localResidual_lift_mem_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C R : G413.Row alpha} {x : alpha}
    (hH : H = {E, A, B, C}) (hxE : x ∈ E)
    (hR : R ∈ blocker (localResidual E A B C x)) :
    insert x R ∈ blocker H := by
  classical
  let D := localResidual E A B C x
  have hRMin := mem_blocker.mp hR
  have hRAvoidE : ∀ y ∈ R, y ∉ E := localBlocker_rows_avoid_base hR
  apply mem_blocker.mpr
  have hTransversal : IsTransversal H (insert x R) := by
    have hitOther (Q : G413.Row alpha) (hQABC : Q ∈ ({A, B, C} : G413.Hypergraph alpha)) :
        ∃ y ∈ insert x R, y ∈ Q := by
      by_cases hxQ : x ∈ Q
      · exact ⟨x, by simp, hxQ⟩
      · have hQD : Q \ E ∈ D := by
          apply Finset.mem_image.mpr
          exact ⟨Q, Finset.mem_filter.mpr ⟨hQABC, hxQ⟩, rfl⟩
        obtain ⟨y, hyR, hyQE⟩ := hRMin.prop (Q \ E) hQD
        exact ⟨y, by simp [hyR], (Finset.mem_sdiff.mp hyQE).1⟩
    intro Q hQH
    have hCases : Q = E ∨ Q = A ∨ Q = B ∨ Q = C := by
      simpa [hH] using hQH
    rcases hCases with hQE | hQA | hQB | hQC
    · exact ⟨x, by simp, hQE ▸ hxE⟩
    · exact hitOther Q (by simpa [hQA])
    · exact hitOther Q (by simpa [hQB])
    · exact hitOther Q (by simpa [hQC])
  apply hTransversal.minimal_of_privateRows
  intro y hyLift
  simp only [Finset.mem_insert] at hyLift
  rcases hyLift with rfl | hyR
  · refine ⟨E, by simp [hH], by simp, hxE, ?_⟩
    intro y hyLift hyE
    simp only [Finset.mem_insert] at hyLift
    rcases hyLift with rfl | hyR
    · rfl
    · exact (hRAvoidE y hyR hyE).elim
  · obtain ⟨P, hPPrivate⟩ := hRMin.exists_privateRow hyR
    obtain ⟨hPD, hyR', hyP, hUnique⟩ := hPPrivate
    obtain ⟨Q, hQFilter, hQDiff⟩ := Finset.mem_image.mp hPD
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    have hQH : Q ∈ H := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
      rcases hQABC with rfl | rfl | rfl <;> simp [hH]
    have hyQ : y ∈ Q := by
      exact (Finset.mem_sdiff.mp (hQDiff ▸ hyP)).1
    refine ⟨Q, hQH, by simp [hyR], hyQ, ?_⟩
    intro z hzLift hzQ
    simp only [Finset.mem_insert] at hzLift
    rcases hzLift with rfl | hzR
    · exact (hxQ hzQ).elim
    · have hzNotE := hRAvoidE z hzR
      have hzDiff : z ∈ P := by
        rw [← hQDiff]
        exact Finset.mem_sdiff.mpr ⟨hzQ, hzNotE⟩
      exact hUnique hzR hzDiff

noncomputable def localChoices {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (E A B C : G413.Row alpha) :
    Finset (Sigma fun _x : alpha ↦ G413.Row alpha) := by
  classical
  exact E.sigma fun x ↦ blocker (localResidual E A B C x)

noncomputable def localLift {alpha : Type*} [DecidableEq alpha]
    (q : Sigma fun _x : alpha ↦ G413.Row alpha) : G413.Row alpha :=
  insert q.1 q.2

theorem localLift_inter_base {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E A B C : G413.Row alpha}
    {q : Sigma fun _x : alpha ↦ G413.Row alpha}
    (hq : q ∈ localChoices E A B C) :
    localLift q ∩ E = {q.1} := by
  classical
  obtain ⟨hxE, hR⟩ := Finset.mem_sigma.mp hq
  have hAvoid : ∀ y ∈ q.2, y ∉ E := localBlocker_rows_avoid_base hR
  ext y
  constructor
  · intro hy
    obtain ⟨hyLift, hyE⟩ := Finset.mem_inter.mp hy
    simp only [localLift, Finset.mem_insert] at hyLift
    rcases hyLift with rfl | hyR
    · simp
    · exact (hAvoid y hyR hyE).elim
  · intro hy
    have hyq : y = q.1 := by simpa using hy
    subst y
    exact Finset.mem_inter.mpr ⟨by simp [localLift], hxE⟩

theorem localLift_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (E A B C : G413.Row alpha) :
    Set.InjOn localLift
      (↑(localChoices E A B C) : Set (Sigma fun _x : alpha ↦ G413.Row alpha)) := by
  classical
  intro q hq r hr hEq
  have hInter := congrArg (fun T : G413.Row alpha ↦ T ∩ E) hEq
  rw [localLift_inter_base hq, localLift_inter_base hr] at hInter
  have hFirst : q.1 = r.1 := Finset.singleton_inj.mp hInter
  cases q with
  | mk x Q =>
    cases r with
    | mk y R =>
      dsimp at hFirst
      subst y
      obtain ⟨hxE, hQ⟩ := Finset.mem_sigma.mp hq
      obtain ⟨-, hR⟩ := Finset.mem_sigma.mp hr
      have hxQ : x ∉ Q := by
        intro hxQ
        exact localBlocker_rows_avoid_base hQ x hxQ hxE
      have hxR : x ∉ R := by
        intro hxR
        exact localBlocker_rows_avoid_base hR x hxR hxE
      have hSecond : Q = R := by
        simpa [localLift, hxQ, hxR] using congrArg (Finset.erase · x) hEq
      subst R
      rfl

noncomputable def localImage {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (E A B C : G413.Row alpha) : G413.Hypergraph alpha :=
  (localChoices E A B C).image localLift

theorem localImage_subset_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C}) :
    localImage E A B C ⊆ blocker H := by
  classical
  intro T hT
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨hxE, hR⟩ := Finset.mem_sigma.mp hq
  simpa [localLift] using localResidual_lift_mem_blocker hH hxE hR

theorem localImage_card {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (E A B C : G413.Row alpha) :
    (localImage E A B C).card = (localChoices E A B C).card := by
  classical
  exact Finset.card_image_iff.mpr (localLift_injective E A B C)

theorem two_set_not_mem_localImage {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E A B C P : G413.Row alpha}
    (hPE : P ⊆ E) (hPCard : P.card = 2) :
    P ∉ localImage E A B C := by
  classical
  intro hP
  obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hP
  have hInter := localLift_inter_base hq
  rw [hEq] at hInter
  have hPEq : P ∩ E = P := Finset.inter_eq_left.mpr hPE
  rw [hPEq] at hInter
  have hOne : P.card = 1 := by
    simpa using congrArg Finset.card hInter
  omega

theorem blocker_card_ge_eight_of_local_seven_and_pair {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C P : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hLocal : 7 ≤ (localChoices E A B C).card)
    (hPTransversal : IsTransversal H P)
    (hPE : P ⊆ E) (hPCard : P.card = 2) :
    8 ≤ (blocker H).card := by
  classical
  have hPBlocker := mem_blocker_of_transversal_card_le hBRows hPTransversal (by omega)
  have hPNot := two_set_not_mem_localImage (E := E) (A := A) (B := B) (C := C)
    hPE hPCard
  have hSubset : insert P (localImage E A B C) ⊆ blocker H := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hPBlocker
    · exact localImage_subset_blocker hH hT
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_insert_of_notMem hPNot, localImage_card] at hCard
  omega

theorem blocker_card_ge_eight_of_local_six_and_two_pairs {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C P Q : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hLocal : 6 ≤ (localChoices E A B C).card)
    (hPTransversal : IsTransversal H P)
    (hQTransversal : IsTransversal H Q)
    (hPE : P ⊆ E) (hQE : Q ⊆ E)
    (hPCard : P.card = 2) (hQCard : Q.card = 2)
    (hPQ : P ≠ Q) :
    8 ≤ (blocker H).card := by
  classical
  have hPBlocker := mem_blocker_of_transversal_card_le hBRows hPTransversal (by omega)
  have hQBlocker := mem_blocker_of_transversal_card_le hBRows hQTransversal (by omega)
  have hPNot := two_set_not_mem_localImage (E := E) (A := A) (B := B) (C := C)
    hPE hPCard
  have hQNot := two_set_not_mem_localImage (E := E) (A := A) (B := B) (C := C)
    hQE hQCard
  have hPNotInsert : P ∉ insert Q (localImage E A B C) := by
    simp [hPQ, hPNot]
  have hSubset : insert P (insert Q (localImage E A B C)) ⊆ blocker H := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hPBlocker
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · exact hQBlocker
      · exact localImage_subset_blocker hH hT
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_insert_of_notMem hPNotInsert,
    Finset.card_insert_of_notMem hQNot, localImage_card] at hCard
  omega

theorem localChoices_card_le_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C}) :
    (localChoices E A B C).card ≤ (blocker H).card := by
  classical
  calc
    (localChoices E A B C).card = (localImage E A B C).card :=
      (localImage_card E A B C).symm
    _ ≤ (blocker H).card := Finset.card_le_card (localImage_subset_blocker hH)

theorem remaining_base_subset_third_omission {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hH : H = {E, A, B, C})
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    E \ ((E \ A) ∪ (E \ B)) ⊆ E \ C := by
  classical
  intro x hx
  have hxE := (Finset.mem_sdiff.mp hx).1
  have hxNotUnion := (Finset.mem_sdiff.mp hx).2
  have hxA : x ∈ A := by
    by_contra hxA
    exact hxNotUnion (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩))
  have hxB : x ∈ B := by
    by_contra hxB
    exact hxNotUnion (Finset.mem_union_right _
      (Finset.mem_sdiff.mpr ⟨hxE, hxB⟩))
  have hDNonempty := localResidual_nonempty hH hxE hBRows
  obtain ⟨R, hR⟩ := hDNonempty
  obtain ⟨Q, hQFilter, hQDiff⟩ := Finset.mem_image.mp hR
  obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
  simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
  rcases hQABC with rfl | rfl | rfl
  · exact (hxQ hxA).elim
  · exact (hxQ hxB).elim
  · exact Finset.mem_sdiff.mpr ⟨hxE, hxQ⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The six bounded omission parameters have 8^6 possible tuples.
theorem omission_count_arithmetic_finite :
    ∀ n a b c t u : Fin 8,
      4 ≤ n.val → 1 ≤ a.val → a.val ≤ b.val → b.val ≤ c.val →
      n.val = a.val + t.val + u.val → t.val ≤ b.val → u.val ≤ c.val →
      8 ≤ a.val * a.val + t.val * b.val + u.val * c.val ∨
        (n.val = 4 ∧
          (a.val + 8 * b.val + 64 * c.val + 512 * t.val + 4096 * u.val = 8841 ∨
           a.val + 8 * b.val + 64 * c.val + 512 * t.val + 4096 * u.val = 8849 ∨
           a.val + 8 * b.val + 64 * c.val + 512 * t.val + 4096 * u.val = 5265)) := by
  decide

theorem ordered_four_set_blocker_card_ge_eight {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {E A B C : G413.Row alpha}
    (hClutter : IsClutter H)
    (hH : H = {E, A, B, C})
    (hEA : E ≠ A) (hEB : E ≠ B) (hEC : E ≠ C)
    (hECard : 4 ≤ E.card)
    (hEMinA : E.card ≤ A.card)
    (hEMinB : E.card ≤ B.card)
    (hEMinC : E.card ≤ C.card)
    (hOrderAB : (E \ A).card ≤ (E \ B).card)
    (hOrderBC : (E \ B).card ≤ (E \ C).card)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    8 ≤ (blocker H).card := by
  classical
  by_cases hLarge : 8 ≤ (blocker H).card
  · exact hLarge
  have hBlockerUpper : (blocker H).card ≤ 7 := by omega
  have hEH : E ∈ H := by simp [hH]
  have hEDual : E ∈ blocker (blocker H) := by
    rw [blocker_involution hClutter]
    exact hEH
  have hEUpper : E.card ≤ 7 := by
    have := minimalTransversal_card_le_rows (mem_blocker.mp hEDual)
    omega
  let O1 := E \ A
  let O2 := E \ B
  let O3 := E \ C
  let X2 := O2 \ O1
  let X3 := E \ (O1 ∪ O2)
  let a := O1.card
  let b := O2.card
  let c := O3.card
  let t := X2.card
  let u := X3.card
  have hO1Subset : O1 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO2Subset : O2 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO3Subset : O3 ⊆ E := by intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have hO1Positive : 0 < a := by
    apply Finset.card_pos.mpr
    by_contra hEmpty
    have hSubset : E ⊆ A := by
      intro x hxE
      by_contra hxA
      exact hEmpty ⟨x, Finset.mem_sdiff.mpr ⟨hxE, hxA⟩⟩
    exact hEA (hClutter hEH (by simp [hH]) hSubset)
  have hResidualA : a ≤ (A \ E).card := by
    exact card_base_sdiff_le_residual hEMinA
  have hResidualB : b ≤ (B \ E).card := by
    exact card_base_sdiff_le_residual hEMinB
  have hResidualC : c ≤ (C \ E).card := by
    exact card_base_sdiff_le_residual hEMinC
  have hPointFirst (x : alpha) (hx : x ∈ O1) :
      a ≤ (blocker (localResidual E A B C x)).card := by
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH (hO1Subset hx) hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact hResidualA
    · exact hOrderAB.trans hResidualB
    · exact hOrderAB.trans (hOrderBC.trans hResidualC)
  have hPointSecond (x : alpha) (hx : x ∈ X2) :
      b ≤ (blocker (localResidual E A B C x)).card := by
    have hxO2 := (Finset.mem_sdiff.mp hx).1
    have hxE := hO2Subset hxO2
    have hxNotO1 := (Finset.mem_sdiff.mp hx).2
    have hxA : x ∈ A := by
      by_contra hxA
      exact hxNotO1 (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩)
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH hxE hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact (hxQ hxA).elim
    · exact hResidualB
    · exact hOrderBC.trans hResidualC
  have hPointThird (x : alpha) (hx : x ∈ X3) :
      c ≤ (blocker (localResidual E A B C x)).card := by
    have hxE := (Finset.mem_sdiff.mp hx).1
    have hxNotUnion := (Finset.mem_sdiff.mp hx).2
    have hxNotO1 : x ∉ O1 := fun hxO1 ↦ hxNotUnion (Finset.mem_union_left _ hxO1)
    have hxNotO2 : x ∉ O2 := fun hxO2 ↦ hxNotUnion (Finset.mem_union_right _ hxO2)
    have hxA : x ∈ A := by
      by_contra hxA
      exact hxNotO1 (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩)
    have hxB : x ∈ B := by
      by_contra hxB
      exact hxNotO2 (Finset.mem_sdiff.mpr ⟨hxE, hxB⟩)
    apply blocker_card_ge_of_rows_cardAtLeast
      (localResidual_nonempty hH hxE hBRows)
    intro R hR
    obtain ⟨Q, hQFilter, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hQABC, hxQ⟩ := Finset.mem_filter.mp hQFilter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQABC
    rcases hQABC with rfl | rfl | rfl
    · exact (hxQ hxA).elim
    · exact (hxQ hxB).elim
    · exact hResidualC
  have hX3SubsetO3 : X3 ⊆ O3 := by
    exact remaining_base_subset_third_omission hH hBRows
  have hFirstSum : a * a ≤ ∑ x ∈ O1,
      (blocker (localResidual E A B C x)).card := by
    calc
      a * a = ∑ _x ∈ O1, a := by simp [a]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointFirst x hx
  have hSecondSum : t * b ≤ ∑ x ∈ X2,
      (blocker (localResidual E A B C x)).card := by
    calc
      t * b = ∑ _x ∈ X2, b := by simp [t]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointSecond x hx
  have hThirdSum : u * c ≤ ∑ x ∈ X3,
      (blocker (localResidual E A B C x)).card := by
    calc
      u * c = ∑ _x ∈ X3, c := by simp [u]
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦ hPointThird x hx
  have hDisjoint12 : Disjoint O1 X2 := by
    exact Finset.disjoint_sdiff
  have hUnion12 : O1 ∪ X2 = O1 ∪ O2 := by
    ext x
    simp [X2]
  have hDisjoint123 : Disjoint (O1 ∪ X2) X3 := by
    rw [hUnion12]
    exact Finset.disjoint_sdiff
  have hPartition : (O1 ∪ X2) ∪ X3 = E := by
    rw [hUnion12]
    exact Finset.union_sdiff_of_subset (Finset.union_subset hO1Subset hO2Subset)
  have hSumPartition :
      (∑ x ∈ E, (blocker (localResidual E A B C x)).card) =
        (∑ x ∈ O1, (blocker (localResidual E A B C x)).card) +
        (∑ x ∈ X2, (blocker (localResidual E A B C x)).card) +
      (∑ x ∈ X3, (blocker (localResidual E A B C x)).card) := by
    rw [← hPartition, Finset.sum_union hDisjoint123, Finset.sum_union hDisjoint12]
  have hGeneratedLower : a * a + t * b + u * c ≤
      (localChoices E A B C).card := by
    rw [localChoices, Finset.card_sigma]
    rw [hSumPartition]
    omega
  have hGeneratedUpper := localChoices_card_le_blocker hH
  have hCountUpper : a * a + t * b + u * c ≤ 7 := by
    omega
  have hNPartition : E.card = a + t + u := by
    have hCardPartition := congrArg Finset.card hPartition
    rw [Finset.card_union_of_disjoint hDisjoint123,
      Finset.card_union_of_disjoint hDisjoint12] at hCardPartition
    simpa [a, t, u, Nat.add_assoc] using hCardPartition.symm
  have ha7 : a ≤ 7 := (Finset.card_le_card hO1Subset).trans hEUpper
  have hb7 : b ≤ 7 := (Finset.card_le_card hO2Subset).trans hEUpper
  have hc7 : c ≤ 7 := (Finset.card_le_card hO3Subset).trans hEUpper
  have ht7 : t ≤ 7 := by
    have : X2 ⊆ E := (Finset.sdiff_subset.trans hO2Subset)
    exact (Finset.card_le_card this).trans hEUpper
  have hu7 : u ≤ 7 := by
    have : X3 ⊆ E := Finset.sdiff_subset
    exact (Finset.card_le_card this).trans hEUpper
  have htB : t ≤ b := Finset.card_le_card Finset.sdiff_subset
  have huC : u ≤ c := Finset.card_le_card hX3SubsetO3
  have hArithmetic := omission_count_arithmetic_finite
    ⟨E.card, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩
    ⟨c, by omega⟩ ⟨t, by omega⟩ ⟨u, by omega⟩
    hECard hO1Positive hOrderAB hOrderBC hNPartition htB huC
  rcases hArithmetic with hEight | hExceptional
  · have hEight' : 8 ≤ a * a + t * b + u * c := by
      simpa using hEight
    omega
  · have hExceptional' : E.card = 4 ∧
        (a + 8 * b + 64 * c + 512 * t + 4096 * u = 8841 ∨
         a + 8 * b + 64 * c + 512 * t + 4096 * u = 8849 ∨
         a + 8 * b + 64 * c + 512 * t + 4096 * u = 5265) := by
      simpa using hExceptional
    rcases hExceptional' with ⟨-, hSix | hSevenFirst | hSevenSecond⟩
    · have ha : a = 1 := by omega
      have hb : b = 1 := by omega
      have hc : c = 2 := by omega
      have ht : t = 1 := by omega
      have hu : u = 2 := by omega
      have hO1Card : O1.card = 1 := by simpa [a] using ha
      have hO2Card : O2.card = 1 := by simpa [b] using hb
      have hO3Card : O3.card = 2 := by simpa [c] using hc
      have hX2Card : X2.card = 1 := by simpa [t] using ht
      have hX3Card : X3.card = 2 := by simpa [u] using hu
      have hX2EqO2 : X2 = O2 :=
        Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by omega)
      have hX3EqO3 : X3 = O3 :=
        Finset.eq_of_subset_of_card_le hX3SubsetO3 (by omega)
      obtain ⟨p, hpO1⟩ := Finset.card_pos.mp (by omega : 0 < O1.card)
      obtain ⟨q, hqX2⟩ := Finset.card_pos.mp (by omega : 0 < X2.card)
      obtain ⟨r, hrX3⟩ := Finset.card_pos.mp (by omega : 0 < X3.card)
      have hpE := hO1Subset hpO1
      have hqO2 := (Finset.mem_sdiff.mp hqX2).1
      have hqNotO1 := (Finset.mem_sdiff.mp hqX2).2
      have hqE := hO2Subset hqO2
      have hrE := (Finset.mem_sdiff.mp hrX3).1
      have hrNotUnion := (Finset.mem_sdiff.mp hrX3).2
      have hrNotO1 : r ∉ O1 := fun hr ↦ hrNotUnion (Finset.mem_union_left _ hr)
      have hrNotO2 : r ∉ O2 := fun hr ↦ hrNotUnion (Finset.mem_union_right _ hr)
      have hqA : q ∈ A := by
        by_contra hqA
        exact hqNotO1 (Finset.mem_sdiff.mpr ⟨hqE, hqA⟩)
      have hrA : r ∈ A := by
        by_contra hrA
        exact hrNotO1 (Finset.mem_sdiff.mpr ⟨hrE, hrA⟩)
      have hrB : r ∈ B := by
        by_contra hrB
        exact hrNotO2 (Finset.mem_sdiff.mpr ⟨hrE, hrB⟩)
      have hpNotX2 : p ∉ X2 := fun hp ↦ (Finset.mem_sdiff.mp hp).2 hpO1
      have hpNotO2 : p ∉ O2 := by
        rw [← hX2EqO2]
        exact hpNotX2
      have hpB : p ∈ B := by
        by_contra hpB
        exact hpNotO2 (Finset.mem_sdiff.mpr ⟨hpE, hpB⟩)
      have hpNotX3 : p ∉ X3 := fun hp ↦
        (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_left _ hpO1)
      have hpNotO3 : p ∉ O3 := by
        rw [← hX3EqO3]
        exact hpNotX3
      have hpC : p ∈ C := by
        by_contra hpC
        exact hpNotO3 (Finset.mem_sdiff.mpr ⟨hpE, hpC⟩)
      have hpq : p ≠ q := fun hpq ↦ hqNotO1 (hpq ▸ hpO1)
      have hpr : p ≠ r := fun hpr ↦ hrNotO1 (hpr ▸ hpO1)
      have hqr : q ≠ r := fun hqr ↦ hrNotO2 (hqr ▸ hqO2)
      have hPTransversal : IsTransversal H ({p, q} : G413.Row alpha) := by
        intro R hRH
        have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
          simpa [hH] using hRH
        rcases hCases with rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpE⟩
        · exact ⟨q, by simp, hqA⟩
        · exact ⟨p, by simp, hpB⟩
        · exact ⟨p, by simp, hpC⟩
      have hQTransversal : IsTransversal H ({p, r} : G413.Row alpha) := by
        intro R hRH
        have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
          simpa [hH] using hRH
        rcases hCases with rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpE⟩
        · exact ⟨r, by simp, hrA⟩
        · exact ⟨r, by simp, hrB⟩
        · exact ⟨p, by simp, hpC⟩
      have hPE : ({p, q} : G413.Row alpha) ⊆ E := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpE
        · exact hqE
      have hQE : ({p, r} : G413.Row alpha) ⊆ E := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpE
        · exact hrE
      have hPairNe : ({p, q} : G413.Row alpha) ≠ {p, r} := by
        intro hEq
        have hqRight : q ∈ ({p, r} : G413.Row alpha) := by
          rw [← hEq]
          simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqRight
        rcases hqRight with hqp | hqr'
        · exact hpq hqp.symm
        · exact hqr hqr'
      have hLocalSix : 6 ≤ (localChoices E A B C).card := by
        simpa [ha, hb, hc, ht, hu] using hGeneratedLower
      exact blocker_card_ge_eight_of_local_six_and_two_pairs
        hH hBRows hLocalSix hPTransversal hQTransversal hPE hQE
        (by simp [hpq]) (by simp [hpr]) hPairNe
    · have ha : a = 1 := by omega
      have hb : b = 2 := by omega
      have hc : c = 2 := by omega
      have ht : t = 1 := by omega
      have hu : u = 2 := by omega
      have hO1Card : O1.card = 1 := by simpa [a] using ha
      have hO3Card : O3.card = 2 := by simpa [c] using hc
      have hX3Card : X3.card = 2 := by simpa [u] using hu
      have hX3EqO3 : X3 = O3 :=
        Finset.eq_of_subset_of_card_le hX3SubsetO3 (by omega)
      obtain ⟨p, hpO1⟩ := Finset.card_pos.mp (by omega : 0 < O1.card)
      obtain ⟨r, hrX3⟩ := Finset.card_pos.mp (by omega : 0 < X3.card)
      have hpE := hO1Subset hpO1
      have hrE := (Finset.mem_sdiff.mp hrX3).1
      have hrNotUnion := (Finset.mem_sdiff.mp hrX3).2
      have hrNotO1 : r ∉ O1 := fun hr ↦ hrNotUnion (Finset.mem_union_left _ hr)
      have hrNotO2 : r ∉ O2 := fun hr ↦ hrNotUnion (Finset.mem_union_right _ hr)
      have hrA : r ∈ A := by
        by_contra hrA
        exact hrNotO1 (Finset.mem_sdiff.mpr ⟨hrE, hrA⟩)
      have hrB : r ∈ B := by
        by_contra hrB
        exact hrNotO2 (Finset.mem_sdiff.mpr ⟨hrE, hrB⟩)
      have hpNotX3 : p ∉ X3 := fun hp ↦
        (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_left _ hpO1)
      have hpNotO3 : p ∉ O3 := by
        rw [← hX3EqO3]
        exact hpNotX3
      have hpC : p ∈ C := by
        by_contra hpC
        exact hpNotO3 (Finset.mem_sdiff.mpr ⟨hpE, hpC⟩)
      have hpr : p ≠ r := fun hpr ↦ hrNotO1 (hpr ▸ hpO1)
      have hPTransversal : IsTransversal H ({p, r} : G413.Row alpha) := by
        intro R hRH
        have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
          simpa [hH] using hRH
        rcases hCases with rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpE⟩
        · exact ⟨r, by simp, hrA⟩
        · exact ⟨r, by simp, hrB⟩
        · exact ⟨p, by simp, hpC⟩
      have hPE : ({p, r} : G413.Row alpha) ⊆ E := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpE
        · exact hrE
      have hLocalSeven : 7 ≤ (localChoices E A B C).card := by
        simpa [ha, hb, hc, ht, hu] using hGeneratedLower
      exact blocker_card_ge_eight_of_local_seven_and_pair
        hH hBRows hLocalSeven hPTransversal hPE (by simp [hpr])
    · have ha : a = 1 := by omega
      have hb : b = 2 := by omega
      have hc : c = 2 := by omega
      have ht : t = 2 := by omega
      have hu : u = 1 := by omega
      have hO1Card : O1.card = 1 := by simpa [a] using ha
      have hO2Card : O2.card = 2 := by simpa [b] using hb
      have hO3Card : O3.card = 2 := by simpa [c] using hc
      have hX2Card : X2.card = 2 := by simpa [t] using ht
      have hX3Card : X3.card = 1 := by simpa [u] using hu
      have hX2EqO2 : X2 = O2 :=
        Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by omega)
      have hDisjoint23 : Disjoint X2 X3 := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx2 hx3
        have hxO2 := (Finset.mem_sdiff.mp hx2).1
        exact (Finset.mem_sdiff.mp hx3).2 (Finset.mem_union_right _ hxO2)
      have hX2NotSubsetO3 : ¬ X2 ⊆ O3 := by
        intro hX2Subset
        have hUnionSubset : X2 ∪ X3 ⊆ O3 :=
          Finset.union_subset hX2Subset hX3SubsetO3
        have hCard := Finset.card_le_card hUnionSubset
        rw [Finset.card_union_of_disjoint hDisjoint23] at hCard
        omega
      obtain ⟨p, hpO1⟩ := Finset.card_pos.mp (by omega : 0 < O1.card)
      obtain ⟨q, hqX2, hqNotO3⟩ := Finset.not_subset.mp hX2NotSubsetO3
      have hpE := hO1Subset hpO1
      have hqO2 := (Finset.mem_sdiff.mp hqX2).1
      have hqNotO1 := (Finset.mem_sdiff.mp hqX2).2
      have hqE := hO2Subset hqO2
      have hqA : q ∈ A := by
        by_contra hqA
        exact hqNotO1 (Finset.mem_sdiff.mpr ⟨hqE, hqA⟩)
      have hpNotX2 : p ∉ X2 := fun hp ↦ (Finset.mem_sdiff.mp hp).2 hpO1
      have hpNotO2 : p ∉ O2 := by
        rw [← hX2EqO2]
        exact hpNotX2
      have hpB : p ∈ B := by
        by_contra hpB
        exact hpNotO2 (Finset.mem_sdiff.mpr ⟨hpE, hpB⟩)
      have hqC : q ∈ C := by
        by_contra hqC
        exact hqNotO3 (Finset.mem_sdiff.mpr ⟨hqE, hqC⟩)
      have hpq : p ≠ q := fun hpq ↦ hqNotO1 (hpq ▸ hpO1)
      have hPTransversal : IsTransversal H ({p, q} : G413.Row alpha) := by
        intro R hRH
        have hCases : R = E ∨ R = A ∨ R = B ∨ R = C := by
          simpa [hH] using hRH
        rcases hCases with rfl | rfl | rfl | rfl
        · exact ⟨p, by simp, hpE⟩
        · exact ⟨q, by simp, hqA⟩
        · exact ⟨p, by simp, hpB⟩
        · exact ⟨q, by simp, hqC⟩
      have hPE : ({p, q} : G413.Row alpha) ⊆ E := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpE
        · exact hqE
      have hLocalSeven : 7 ≤ (localChoices E A B C).card := by
        simpa [ha, hb, hc, ht, hu] using hGeneratedLower
      exact blocker_card_ge_eight_of_local_seven_and_pair
        hH hBRows hLocalSeven hPTransversal hPE (by simp [hpq])

theorem four_set_blocker_card_ge_eight {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hClutter : IsClutter H)
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 4)
    (hBRows : RowsCardAtLeast (blocker H) 2) :
    8 ≤ (blocker H).card := by
  classical
  obtain ⟨A, B, C, D, hABne, hACne, hADne, hBCne, hBDne, hCDne, hH⟩ :=
    Finset.card_eq_four.mp hHCard
  have ordered (E P Q R : G413.Row alpha)
      (hFamily : H = {E, P, Q, R})
      (hEP : E ≠ P) (hEQ : E ≠ Q) (hER : E ≠ R)
      (hECard : 4 ≤ E.card)
      (hEMinP : E.card ≤ P.card)
      (hEMinQ : E.card ≤ Q.card)
      (hEMinR : E.card ≤ R.card) :
      8 ≤ (blocker H).card := by
    have hSort :
        ((E \ P).card ≤ (E \ Q).card ∧ (E \ Q).card ≤ (E \ R).card) ∨
        ((E \ P).card ≤ (E \ R).card ∧ (E \ R).card ≤ (E \ Q).card) ∨
        ((E \ Q).card ≤ (E \ P).card ∧ (E \ P).card ≤ (E \ R).card) ∨
        ((E \ Q).card ≤ (E \ R).card ∧ (E \ R).card ≤ (E \ P).card) ∨
        ((E \ R).card ≤ (E \ P).card ∧ (E \ P).card ≤ (E \ Q).card) ∨
        ((E \ R).card ≤ (E \ Q).card ∧ (E \ Q).card ≤ (E \ P).card) := by
      omega
    rcases hSort with hPQR | hPRQ | hQPR | hQRP | hRPQ | hRQP
    · exact ordered_four_set_blocker_card_ge_eight hClutter hFamily
        hEP hEQ hER hECard hEMinP hEMinQ hEMinR hPQR.1 hPQR.2 hBRows
    · exact ordered_four_set_blocker_card_ge_eight
        (E := E) (A := P) (B := R) (C := Q) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEP hER hEQ hECard hEMinP hEMinR hEMinQ hPRQ.1 hPRQ.2 hBRows
    · exact ordered_four_set_blocker_card_ge_eight
        (E := E) (A := Q) (B := P) (C := R) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEQ hEP hER hECard hEMinQ hEMinP hEMinR hQPR.1 hQPR.2 hBRows
    · exact ordered_four_set_blocker_card_ge_eight
        (E := E) (A := Q) (B := R) (C := P) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hEQ hER hEP hECard hEMinQ hEMinR hEMinP hQRP.1 hQRP.2 hBRows
    · exact ordered_four_set_blocker_card_ge_eight
        (E := E) (A := R) (B := P) (C := Q) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hER hEP hEQ hECard hEMinR hEMinP hEMinQ hRPQ.1 hRPQ.2 hBRows
    · exact ordered_four_set_blocker_card_ge_eight
        (E := E) (A := R) (B := Q) (C := P) hClutter
        (by rw [hFamily]; ext T; simp [or_comm, or_left_comm])
        hER hEQ hEP hECard hEMinR hEMinQ hEMinP hRQP.1 hRQP.2 hBRows
  have hAH : A ∈ H := by simp [hH]
  have hBH : B ∈ H := by simp [hH]
  have hCH : C ∈ H := by simp [hH]
  have hDH : D ∈ H := by simp [hH]
  have hACard := hHRows A hAH
  have hBCard := hHRows B hBH
  have hCCard := hHRows C hCH
  have hDCard := hHRows D hDH
  have hMinimum :
      (A.card ≤ B.card ∧ A.card ≤ C.card ∧ A.card ≤ D.card) ∨
      (B.card ≤ A.card ∧ B.card ≤ C.card ∧ B.card ≤ D.card) ∨
      (C.card ≤ A.card ∧ C.card ≤ B.card ∧ C.card ≤ D.card) ∨
      (D.card ≤ A.card ∧ D.card ≤ B.card ∧ D.card ≤ C.card) := by
    omega
  rcases hMinimum with hAmin | hBmin | hCmin | hDmin
  · exact ordered A B C D hH hABne hACne hADne hACard
      hAmin.1 hAmin.2.1 hAmin.2.2
  · exact ordered B A C D
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hABne.symm hBCne hBDne hBCard hBmin.1 hBmin.2.1 hBmin.2.2
  · exact ordered C A B D
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hACne.symm hBCne.symm hCDne hCCard hCmin.1 hCmin.2.1 hCmin.2.2
  · exact ordered D A B C
      (by rw [hH]; ext T; simp [or_comm, or_left_comm])
      hADne.symm hBDne.symm hCDne.symm hDCard hDmin.1 hDmin.2.1 hDmin.2.2

end AiMathLab.P0054.AdjacentFour
