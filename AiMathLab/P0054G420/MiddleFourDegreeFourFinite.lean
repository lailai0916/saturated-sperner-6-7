import AiMathLab.P0054G420.MiddleFourActualEnumerated

namespace AiMathLab.P0054.G420

open G413 G419

def supportPrivateBlockerCertificate {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (T : G413.Row alpha) : Bool :=
  decide (∀ E ∈ H, ¬Disjoint T E) &&
    decide (∀ x, x ∈ T → ∃ E, E ∈ H ∧ T ∩ E = {x})

def supportBlocker {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) : G413.Hypergraph alpha :=
  (H.biUnion id).powerset.filter fun T =>
    supportPrivateBlockerCertificate H T = true

theorem supportPrivateBlockerCertificate_eq_true_iff {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {T : G413.Row alpha} :
    supportPrivateBlockerCertificate H T = true ↔ T ∈ blocker H := by
  constructor
  · intro hCertificate
    simp only [supportPrivateBlockerCertificate, Bool.and_eq_true,
      decide_eq_true_eq] at hCertificate
    obtain ⟨hNotDisjoint, hPrivate⟩ := hCertificate
    have hTransversal : IsTransversal H T := by
      intro E hEH
      by_contra hNoIntersection
      apply hNotDisjoint E hEH
      apply Finset.disjoint_left.mpr
      intro x hxT hxE
      exact hNoIntersection ⟨x, hxT, hxE⟩
    apply mem_blocker.mpr
    apply hTransversal.minimal_of_privateRows
    intro x hxT
    obtain ⟨E, hEH, hInter⟩ := hPrivate x hxT
    refine ⟨E, hEH, hxT, ?_, ?_⟩
    · have hxInter : x ∈ T ∩ E := by rw [hInter]; simp
      exact (Finset.mem_inter.mp hxInter).2
    · intro y hyT hyE
      have hyInter : y ∈ T ∩ E := Finset.mem_inter.mpr ⟨hyT, hyE⟩
      rw [hInter] at hyInter
      simpa using hyInter
  · intro hT
    have hMinimal := mem_blocker.mp hT
    simp only [supportPrivateBlockerCertificate, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · intro E hEH hDisjoint
      obtain ⟨x, hxT, hxE⟩ := hMinimal.prop E hEH
      exact Finset.disjoint_left.mp hDisjoint hxT hxE
    intro x hxT
    obtain ⟨E, hEPrivate⟩ := hMinimal.exists_privateRow hxT
    refine ⟨E, hEPrivate.1, ?_⟩
    ext y
    constructor
    · intro hy
      have hyx := hEPrivate.2.2.2
        (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      simp [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact Finset.mem_inter.mpr ⟨hxT, hEPrivate.2.2.1⟩

theorem blocker_row_subset_biUnion {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {T : G413.Row alpha}
    (hT : T ∈ blocker H) : T ⊆ H.biUnion id := by
  intro x hxT
  obtain ⟨E, hEPrivate⟩ := (mem_blocker.mp hT).exists_privateRow hxT
  exact Finset.mem_biUnion.mpr ⟨E, hEPrivate.1, hEPrivate.2.2.1⟩

theorem supportBlocker_eq_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) : supportBlocker H = blocker H := by
  ext T
  simp only [supportBlocker, Finset.mem_filter, Finset.mem_powerset,
    supportPrivateBlockerCertificate_eq_true_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨blocker_row_subset_biUnion h, h⟩

def fastMinimize {alpha : Type*} [DecidableEq alpha]
    (rows : G413.Hypergraph alpha) : G413.Hypergraph alpha :=
  rows.filter fun row =>
    decide (∀ other ∈ rows, other ⊆ row → row ⊆ other)

def fastBlockerExpand {alpha : Type*} [DecidableEq alpha]
    (candidates : G413.Hypergraph alpha) (row : G413.Row alpha) :
    G413.Hypergraph alpha :=
  candidates.biUnion fun candidate =>
    if Disjoint candidate row then
      row.image fun point => insert point candidate
    else
      {candidate}

def fastBlockerStep {alpha : Type*} [DecidableEq alpha]
    (candidates : G413.Hypergraph alpha) (row : G413.Row alpha) :
    G413.Hypergraph alpha :=
  fastMinimize (fastBlockerExpand candidates row)

def fastBlocker {alpha : Type*} [DecidableEq alpha] :
    List (G413.Row alpha) → G413.Hypergraph alpha
  | [] => {∅}
  | row :: rows => fastBlockerStep (fastBlocker rows) row

@[simp]
theorem mem_fastMinimize {alpha : Type*} [DecidableEq alpha]
    {rows : G413.Hypergraph alpha} {row : G413.Row alpha} :
    row ∈ fastMinimize rows ↔
      row ∈ rows ∧ ∀ other ∈ rows, other ⊆ row → row ⊆ other := by
  simp [fastMinimize]

theorem fastBlockerExpand_transversal {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H candidates : G413.Hypergraph alpha} {row candidate : G413.Row alpha}
    (hCandidates : candidates = blocker H)
    (hCandidate : candidate ∈ fastBlockerExpand candidates row) :
    IsTransversal (insert row H) candidate := by
  subst candidates
  rw [fastBlockerExpand, Finset.mem_biUnion] at hCandidate
  obtain ⟨base, hBase, hCandidate⟩ := hCandidate
  by_cases hDisjoint : Disjoint base row
  · rw [if_pos hDisjoint] at hCandidate
    obtain ⟨point, hPointRow, rfl⟩ := Finset.mem_image.mp hCandidate
    intro edge hEdge
    simp only [Finset.mem_insert] at hEdge
    rcases hEdge with rfl | hEdge
    · exact ⟨point, by simp, hPointRow⟩
    · obtain ⟨x, hxBase, hxEdge⟩ := (mem_blocker.mp hBase).prop edge hEdge
      exact ⟨x, by simp [hxBase], hxEdge⟩
  · rw [if_neg hDisjoint] at hCandidate
    have hEq : candidate = base := by simpa using hCandidate
    subst candidate
    intro edge hEdge
    simp only [Finset.mem_insert] at hEdge
    rcases hEdge with rfl | hEdge
    · obtain ⟨x, hxBase, hxRow⟩ := Finset.not_disjoint_iff.mp hDisjoint
      exact ⟨x, hxBase, hxRow⟩
    · exact (mem_blocker.mp hBase).prop edge hEdge

theorem fastBlockerExpand_exists_subset {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H candidates : G413.Hypergraph alpha} {row set : G413.Row alpha}
    (hCandidates : candidates = blocker H)
    (hSet : IsTransversal (insert row H) set) :
    ∃ candidate ∈ fastBlockerExpand candidates row, candidate ⊆ set := by
  have hSetH : IsTransversal H set := by
    intro edge hEdge
    exact hSet edge (by simp [hEdge])
  obtain ⟨base, hBaseSet, hBaseMinimal⟩ :=
    exists_minimalTransversal_subset hSetH
  have hBase : base ∈ candidates := by
    rw [hCandidates]
    exact mem_blocker.mpr hBaseMinimal
  by_cases hDisjoint : Disjoint base row
  · obtain ⟨point, hPointSet, hPointRow⟩ := hSet row (by simp)
    refine ⟨insert point base, ?_, ?_⟩
    · rw [fastBlockerExpand, Finset.mem_biUnion]
      refine ⟨base, hBase, ?_⟩
      rw [if_pos hDisjoint]
      exact Finset.mem_image.mpr ⟨point, hPointRow, rfl⟩
    · exact Finset.insert_subset hPointSet hBaseSet
  · refine ⟨base, ?_, hBaseSet⟩
    rw [fastBlockerExpand, Finset.mem_biUnion]
    refine ⟨base, hBase, ?_⟩
    simp [hDisjoint]

theorem fastBlockerStep_eq_blocker_insert {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H candidates : G413.Hypergraph alpha) (row : G413.Row alpha)
    (hCandidates : candidates = blocker H) :
    fastBlockerStep candidates row = blocker (insert row H) := by
  ext set
  constructor
  · intro hSet
    obtain ⟨hSetExpand, hSetMinimal⟩ :=
      mem_fastMinimize.mp (by simpa [fastBlockerStep] using hSet)
    have hSetTransversal := fastBlockerExpand_transversal
      hCandidates hSetExpand
    apply mem_blocker.mpr
    apply isMinimalTransversal_iff.mpr
    refine ⟨hSetTransversal, ?_⟩
    intro proper hProper hProperTransversal
    obtain ⟨candidate, hCandidateExpand, hCandidateProper⟩ :=
      fastBlockerExpand_exists_subset hCandidates hProperTransversal
    have hSetCandidate := hSetMinimal candidate hCandidateExpand
      (hCandidateProper.trans hProper.1)
    exact hProper.2 (hSetCandidate.trans hCandidateProper)
  · intro hSet
    have hSetMinimal := mem_blocker.mp hSet
    obtain ⟨candidate, hCandidateExpand, hCandidateSet⟩ :=
      fastBlockerExpand_exists_subset hCandidates hSetMinimal.prop
    have hCandidateTransversal := fastBlockerExpand_transversal
      hCandidates hCandidateExpand
    have hSetCandidate : set ⊆ candidate := by
      by_contra hNotSubset
      have hProper : candidate ⊂ set := ⟨hCandidateSet, hNotSubset⟩
      exact (isMinimalTransversal_iff.mp hSetMinimal).2 hProper
        hCandidateTransversal
    have hSetExpand : set ∈ fastBlockerExpand candidates row := by
      have hEq : set = candidate :=
        Finset.Subset.antisymm hSetCandidate hCandidateSet
      simpa [hEq] using hCandidateExpand
    apply mem_fastMinimize.mpr
    refine ⟨hSetExpand, ?_⟩
    intro other hOtherExpand hOtherSet
    have hOtherTransversal := fastBlockerExpand_transversal
      hCandidates hOtherExpand
    by_contra hNotSubset
    have hProper : other ⊂ set := ⟨hOtherSet, hNotSubset⟩
    exact (isMinimalTransversal_iff.mp hSetMinimal).2 hProper
      hOtherTransversal

theorem fastBlocker_eq_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (rows : List (G413.Row alpha)) :
    fastBlocker rows = blocker rows.toFinset := by
  induction rows with
  | nil =>
      ext set
      simp only [fastBlocker, List.toFinset_nil, Finset.mem_singleton]
      constructor
      · intro hSet
        subst set
        rw [mem_blocker]
        apply isMinimalTransversal_iff.mpr
        refine ⟨by simp [IsTransversal], ?_⟩
        intro other hOther
        exact (hOther.2 (by simp)).elim
      · intro hSet
        have hMinimal := mem_blocker.mp hSet
        have hEmptyTransversal : IsTransversal (∅ : G413.Hypergraph alpha) ∅ := by
          simp [IsTransversal]
        by_contra hSetEmpty
        have hProper : (∅ : G413.Row alpha) ⊂ set := by
          refine ⟨by simp, ?_⟩
          intro hSetSubset
          exact hSetEmpty (Finset.Subset.antisymm hSetSubset (by simp))
        exact (isMinimalTransversal_iff.mp hMinimal).2 hProper hEmptyTransversal
  | cons row rows ih =>
      rw [fastBlocker, List.toFinset_cons]
      exact fastBlockerStep_eq_blocker_insert rows.toFinset
        (fastBlocker rows) row ih

abbrev MiddleFourModelPoint := Fin 16

def middleFourListPowerset {alpha : Type*} : List alpha → List (List alpha)
  | [] => [[]]
  | value :: values =>
      let tail := middleFourListPowerset values
      tail ++ tail.map (value :: ·)

def middleFourModelSupports (values : List Nat) : List Nat :=
  (List.range 14).flatMap fun support =>
    List.replicate (values.getD support 0) support

def middleFourModelKernelRows (values : List Nat) :
    List (G413.Row MiddleFourModelPoint) :=
  (List.range 4).map fun row =>
    Finset.univ.filter fun point =>
      point.val < (middleFourModelSupports values).length &&
        fourSupportContains
          ((middleFourModelSupports values).getD point.val 0) row

def middleFourModelKernel (values : List Nat) :
    G413.Hypergraph MiddleFourModelPoint :=
  (middleFourModelKernelRows values).toFinset

def middleFourModelCenter (values : List Nat) : MiddleFourModelPoint :=
  ⟨(middleFourModelSupports values).length % 16, Nat.mod_lt _ (by omega)⟩

def middleFourModelActivePoints (values : List Nat) :
    List MiddleFourModelPoint :=
  (List.finRange 16).filter fun point =>
    point.val < (middleFourModelSupports values).length

def middleFourModelBlockerRows (values : List Nat) :
    List (G413.Row MiddleFourModelPoint) :=
  let blockers := fastBlocker (middleFourModelKernelRows values)
  ((middleFourListPowerset (middleFourModelActivePoints values)).map
    List.toFinset).filter fun row =>
    row ∈ blockers

def middleFourModelBlocker (values : List Nat) :
    G413.Hypergraph MiddleFourModelPoint :=
  (middleFourModelBlockerRows values).toFinset

def middleFourModelPairBlockerRows (values : List Nat) :
    List (G413.Row MiddleFourModelPoint) :=
  (middleFourModelBlockerRows values).filter fun row => row.card = 2

def middleFourModelOtherBlockerRows (values : List Nat) :
    List (G413.Row MiddleFourModelPoint) :=
  (middleFourModelBlockerRows values).filter fun row => row.card ≠ 2

def middleFourModelLiftSelectionRows (values : List Nat) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  (middleFourListPowerset (middleFourModelOtherBlockerRows values)).filter fun selected =>
    selected.length + (middleFourModelPairBlockerRows values).length ≤ 4

def middleFourModelLiftBaseRows (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint)) :
    List (G413.Row MiddleFourModelPoint) :=
  (middleFourModelBlockerRows values).map fun row =>
    if row.card = 2 ∨ row ∈ selected then
      insert (middleFourModelCenter values) row
    else row

def middleFourModelEligibleOldPointList (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint)) :
    List MiddleFourModelPoint :=
  (List.finRange 16).filter fun point =>
    point.val ≤ (middleFourModelSupports values).length &&
      decide (degree base.toFinset point < 4)

def middleFourModelFreshPointList (values : List Nat) (count : Nat) :
    List MiddleFourModelPoint :=
  (List.finRange 16).filter fun point =>
    (middleFourModelSupports values).length < point.val &&
      point.val ≤ (middleFourModelSupports values).length + count

def middleFourModelExtraRowList (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint)) :
    List (G413.Row MiddleFourModelPoint) :=
  (middleFourListPowerset
    (middleFourModelEligibleOldPointList values base)).flatMap fun old =>
    (List.range 9).map fun fresh =>
      old.toFinset ∪ (middleFourModelFreshPointList values fresh).toFinset

def middleFourModelCandidateRowsForSelection (values : List Nat)
    (selected : List (G413.Row MiddleFourModelPoint)) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  let base := middleFourModelLiftBaseRows values selected
  if base.toFinset.card = 8 then
    [base]
  else if base.toFinset.card = 7 then
    (middleFourModelExtraRowList values base).map fun extra => extra :: base
  else
    []

def middleFourModelCandidateRowsValid
    (rows : List (G413.Row MiddleFourModelPoint)) : Bool :=
  let candidate := rows.toFinset
  decide (∀ A, A ∈ candidate → ∀ B, B ∈ candidate → A ⊆ B → A = B) &&
    rows.all fun row => decide (3 ≤ row.card ∧ row.card ≤ 8)

def middleFourModelCandidateRows (values : List Nat) :
    List (List (G413.Row MiddleFourModelPoint)) :=
  (middleFourModelLiftSelectionRows values).flatMap fun selected =>
    middleFourModelCandidateRowsForSelection values selected

def middleFourModelCandidates (values : List Nat) :
    Finset (G413.Hypergraph MiddleFourModelPoint) :=
  ((middleFourModelCandidateRows values).map List.toFinset).toFinset

def middleFourDegreeFourValuesCheck (values : List Nat) : Bool :=
  (middleFourModelCandidateRows values).all fun candidate =>
    decide ((fastBlocker candidate).card ≠ 8)

def middleFourModelRawOldCheck (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint))
    (old : List MiddleFourModelPoint) : Bool :=
  (List.range 9).all fun fresh =>
    let extra := old.toFinset ∪
      (middleFourModelFreshPointList values fresh).toFinset
    decide ((fastBlocker (extra :: base)).card ≠ 8)

def middleFourModelRawChunkCheck (values : List Nat)
    (base : List (G413.Row MiddleFourModelPoint))
    (chunk : List (List MiddleFourModelPoint)) : Bool :=
  chunk.all (middleFourModelRawOldCheck values base)

theorem middleFourModelRawSelectionCheck_of_chunks
    (values : List Nat) (base : List (G413.Row MiddleFourModelPoint))
    (oldSubsets : List (List MiddleFourModelPoint))
    (chunks : List (List (List MiddleFourModelPoint)))
    (hFlatten : chunks.flatMap id = oldSubsets)
    (hChunks : chunks.all
      (middleFourModelRawChunkCheck values base) = true) :
    oldSubsets.all (middleFourModelRawOldCheck values base) = true := by
  subst oldSubsets
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      change (middleFourModelRawChunkCheck values base chunk &&
        chunks.all (middleFourModelRawChunkCheck values base)) = true at hChunks
      have hBoth := Bool.and_eq_true_iff.mp hChunks
      rw [List.flatMap_cons, List.all_append]
      apply Bool.and_eq_true_iff.mpr
      constructor
      · change chunk.all (middleFourModelRawOldCheck values base) = true
        simpa only [middleFourModelRawChunkCheck] using hBoth.1
      · exact ih hBoth.2

theorem middleFourModelCandidateRowsForSelection_check_of_raw
    (values : List Nat) (selected : List (G413.Row MiddleFourModelPoint))
    (base : List (G413.Row MiddleFourModelPoint))
    (eligible : List MiddleFourModelPoint)
    (hBase : middleFourModelLiftBaseRows values selected = base)
    (hBaseCard : base.toFinset.card = 7)
    (hEligible : middleFourModelEligibleOldPointList values base = eligible)
    (hRaw : (middleFourListPowerset eligible).all
      (middleFourModelRawOldCheck values base) = true) :
    (middleFourModelCandidateRowsForSelection values selected).all
      (fun candidate => decide ((fastBlocker candidate).card ≠ 8)) = true := by
  unfold middleFourModelCandidateRowsForSelection
  rw [hBase, if_neg (by omega), if_pos hBaseCard]
  unfold middleFourModelExtraRowList
  rw [hEligible]
  simpa [middleFourModelRawOldCheck] using hRaw

end AiMathLab.P0054.G420
