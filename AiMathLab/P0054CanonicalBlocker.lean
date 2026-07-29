import AiMathLab.P0054G413.BlockerInvolution
import AiMathLab.SaturatedSperner.HomogeneousLayers

/-!
# The canonical-layer blocker interface

For a saturated antichain carrying a common all-or-none block, its small
members and the complements of its large members are mutual blockers.  The
proof works on the original finite ground type; minimal transversals cannot
use inactive atom points.
-/

universe u

namespace AiMathLab.P0054.CanonicalBlocker

open AiMathLab.SaturatedSperner
open AiMathLab.P0054.G413

variable {α : Type u} [Fintype α] [DecidableEq α]

def traceGround (H : Finset α) : Finset α := Finset.univ \ H

def smallTrace (A : AiMathLab.SaturatedSperner.Family α)
    (H : Finset α) : AiMathLab.P0054.G413.Hypergraph α :=
  SmallPart A H

def largeComplementTrace (A : AiMathLab.SaturatedSperner.Family α)
    (H : Finset α) : AiMathLab.P0054.G413.Hypergraph α :=
  (LargePart A H).image fun L => Finset.univ \ L

@[simp] theorem mem_smallTrace_iff
    {A : AiMathLab.SaturatedSperner.Family α} {H S : Finset α} :
    S ∈ smallTrace A H ↔ S ∈ A ∧ Disjoint S H := by
  simp [smallTrace]

theorem mem_largeComplementTrace_iff
    {A : AiMathLab.SaturatedSperner.Family α} {H C : Finset α} :
    C ∈ largeComplementTrace A H ↔
      ∃ L ∈ A, H ⊆ L ∧ C = Finset.univ \ L := by
  constructor
  · intro hC
    rcases Finset.mem_image.mp hC with ⟨L, hL, rfl⟩
    exact ⟨L, (mem_largePart.mp hL).1, (mem_largePart.mp hL).2, rfl⟩
  · rintro ⟨L, hLA, hHL, rfl⟩
    exact Finset.mem_image.mpr ⟨L, mem_largePart.mpr ⟨hLA, hHL⟩, rfl⟩

theorem smallTrace_isClutter
    {A : AiMathLab.SaturatedSperner.Family α} {H : Finset α}
    (hanti : IsAntichain A) :
    AiMathLab.P0054.G413.IsClutter (smallTrace A H) := by
  intro S hS T hT hST
  by_contra hne
  exact hanti.not_ssubset
    (mem_smallTrace_iff.mp hS).1 (mem_smallTrace_iff.mp hT).1
    (Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩)

theorem largeComplementTrace_isClutter
    {A : AiMathLab.SaturatedSperner.Family α} {H : Finset α}
    (hanti : IsAntichain A) :
    AiMathLab.P0054.G413.IsClutter (largeComplementTrace A H) := by
  intro C hC D hD hCD
  rcases mem_largeComplementTrace_iff.mp hC with ⟨L, hLA, hHL, rfl⟩
  rcases mem_largeComplementTrace_iff.mp hD with ⟨M, hMA, hHM, rfl⟩
  have hML : M ⊆ L := by
    intro x hxM
    by_contra hxL
    have hxC : x ∈ (Finset.univ \ L : Finset α) := by simp [hxL]
    have hxD := hCD hxC
    simpa [hxM] using hxD
  have hEq : M = L := by
    by_contra hne
    exact hanti.not_ssubset hMA hLA
      (Finset.ssubset_iff_subset_ne.mpr ⟨hML, hne⟩)
  simp [hEq]

theorem trace_cover
    {A : AiMathLab.SaturatedSperner.Family α} {H R : Finset α}
    (hsat : IsSaturatedAntichain A)
    (hblock : IsAtomBlock A H)
    (hHcard : 1 < H.card)
    (hRU : R ⊆ traceGround H) :
    (∃ S ∈ smallTrace A H, S ⊆ R) ∨
      (∃ C ∈ largeComplementTrace A H,
        C ⊆ traceGround H \ R) := by
  rcases Finset.one_lt_card.mp hHcard with ⟨q, hqH, r, hrH, hqr⟩
  let T := R ∪ {q}
  have hTnot : T ∉ A := by
    intro hTA
    rcases hblock T hTA with hdisj | hHT
    · exact Finset.disjoint_left.mp hdisj (by simp [T]) hqH
    · have hrT := hHT hrH
      simp only [T, Finset.mem_union] at hrT
      rcases hrT with hrR | hrq
      · have hrU := hRU hrR
        exact (Finset.mem_sdiff.mp hrU).2 hrH
      · exact hqr (Eq.symm (by simpa using hrq))
  rcases exists_comparable_of_isSaturatedAntichain hsat hTnot with
    ⟨B, hBA, hBT | hTB⟩
  · rcases hblock B hBA with hBH | hHB
    · left
      refine ⟨B, mem_smallTrace_iff.mpr ⟨hBA, hBH⟩, ?_⟩
      intro x hxB
      have hxT := hBT.1 hxB
      simp only [T, Finset.mem_union] at hxT
      rcases hxT with hxR | hxq
      · exact hxR
      · have hxEq : x = q := by simpa using hxq
        subst x
        exact False.elim (Finset.disjoint_left.mp hBH hxB hqH)
    · have hrB := hHB hrH
      have hrT := hBT.1 hrB
      simp only [T, Finset.mem_union] at hrT
      rcases hrT with hrR | hrq
      · exact False.elim ((Finset.mem_sdiff.mp (hRU hrR)).2 hrH)
      · exact False.elim (hqr (Eq.symm (by simpa using hrq)))
  · rcases hblock B hBA with hBH | hHB
    · have hqB : q ∈ B := hTB.1 (by simp [T])
      exact False.elim (Finset.disjoint_left.mp hBH hqB hqH)
    · right
      let C : Finset α := Finset.univ \ B
      refine ⟨C, mem_largeComplementTrace_iff.mpr ⟨B, hBA, hHB, rfl⟩, ?_⟩
      intro x hxC
      have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hxC).2
      have hxnotH : x ∉ H := by
        intro hxH
        exact hxnotB (hHB hxH)
      have hxnotR : x ∉ R := by
        intro hxR
        exact hxnotB (hTB.1 (Finset.mem_union_left _ hxR))
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnotH⟩, hxnotR⟩

theorem small_meets_largeComplement
    {A : AiMathLab.SaturatedSperner.Family α} {H S C : Finset α}
    (hanti : IsAntichain A) (hHne : H.Nonempty)
    (hS : S ∈ smallTrace A H)
    (hC : C ∈ largeComplementTrace A H) :
    ∃ x ∈ S, x ∈ C := by
  rcases mem_largeComplementTrace_iff.mp hC with ⟨L, hLA, hHL, hCL⟩
  have hSA := (mem_smallTrace_iff.mp hS).1
  have hSH := (mem_smallTrace_iff.mp hS).2
  by_contra hnone
  push_neg at hnone
  have hSL : S ⊆ L := by
    intro x hxS
    by_contra hxL
    have hxC : x ∈ C := by simp [hCL, hxL]
    exact hnone x hxS hxC
  have hne : S ≠ L := by
    intro hEq
    rcases hHne with ⟨h, hhH⟩
    have hhL := hHL hhH
    have hhS : h ∈ S := by simpa [hEq] using hhL
    exact Finset.disjoint_left.mp hSH hhS hhH
  exact hanti.not_ssubset hSA hLA
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSL, hne⟩)

theorem smallTrace_eq_blocker_largeComplement
    {A : AiMathLab.SaturatedSperner.Family α} {H : Finset α}
    (hsat : IsSaturatedAntichain A)
    (hblock : IsAtomBlock A H)
    (hHcard : 1 < H.card)
    (hsmallRows : AiMathLab.P0054.G413.RowsNonempty (smallTrace A H))
    (hlargeRows : AiMathLab.P0054.G413.RowsNonempty (largeComplementTrace A H)) :
    smallTrace A H = AiMathLab.P0054.G413.blocker
      (largeComplementTrace A H) := by
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hsmallClutter := smallTrace_isClutter (H := H) hsat.1
  have hlargeClutter := largeComplementTrace_isClutter (H := H) hsat.1
  apply Finset.Subset.antisymm
  · intro S hS
    apply mem_blocker.mpr
    rw [isMinimalTransversal_iff]
    constructor
    · intro C hC
      exact small_meets_largeComplement hsat.1 hHne hS hC
    · intro T hTS hTtrans
      have hTU : T ⊆ traceGround H := by
        intro x hxT
        have hxS := hTS.1 hxT
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, fun hxH =>
            Finset.disjoint_left.mp (mem_smallTrace_iff.mp hS).2 hxS hxH⟩
      rcases trace_cover hsat hblock hHcard hTU with
        ⟨S', hS', hS'T⟩ | ⟨C, hC, hCcomp⟩
      · have hS'S : S' ⊆ S := hS'T.trans hTS.1
        have hEq := hsmallClutter hS' hS hS'S
        subst S'
        exact hTS.2 hS'T
      · rcases hTtrans C hC with ⟨x, hxT, hxC⟩
        have hxComp := hCcomp hxC
        exact (Finset.mem_sdiff.mp hxComp).2 hxT
  · intro T hT
    have hTmin := mem_blocker.mp hT
    have hTU : T ⊆ traceGround H := by
      intro x hxT
      by_contra hxU
      have hxH : x ∈ H := by
        simpa [traceGround] using hxU
      let T' := T.erase x
      have hT'sub : T' ⊂ T := by
        simpa [T'] using Finset.erase_ssubset hxT
      have hT'trans : AiMathLab.P0054.G413.IsTransversal
          (largeComplementTrace A H) T' := by
        intro C hC
        rcases hTmin.prop C hC with ⟨y, hyT, hyC⟩
        have hyNotH : y ∉ H := by
          rcases mem_largeComplementTrace_iff.mp hC with ⟨L, hLA, hHL, rfl⟩
          intro hyH
          exact (Finset.mem_sdiff.mp hyC).2 (hHL hyH)
        have hyx : y ≠ x := fun h => hyNotH (h ▸ hxH)
        exact ⟨y, by simpa [T'] using Finset.mem_erase.mpr ⟨hyx, hyT⟩, hyC⟩
      exact (isMinimalTransversal_iff.mp hTmin).2 hT'sub hT'trans
    rcases trace_cover hsat hblock hHcard hTU with
      ⟨S, hS, hST⟩ | ⟨C, hC, hCcomp⟩
    · have hStrans : IsTransversal (largeComplementTrace A H) S := by
        intro D hD
        exact small_meets_largeComplement hsat.1 hHne hS hD
      have hTS : T ⊆ S := hTmin.le_of_le hStrans hST
      have hEq : T = S := Finset.Subset.antisymm hTS hST
      simpa [hEq] using hS
    · rcases hTmin.prop C hC with ⟨x, hxT, hxC⟩
      exact False.elim ((Finset.mem_sdiff.mp (hCcomp hxC)).2 hxT)

theorem mutual_blockers
    {A : AiMathLab.SaturatedSperner.Family α} {H : Finset α}
    (hsat : IsSaturatedAntichain A)
    (hblock : IsAtomBlock A H)
    (hHcard : 1 < H.card)
    (hsmallRows : AiMathLab.P0054.G413.RowsNonempty (smallTrace A H))
    (hlargeRows : AiMathLab.P0054.G413.RowsNonempty (largeComplementTrace A H)) :
    smallTrace A H = AiMathLab.P0054.G413.blocker (largeComplementTrace A H) ∧
      largeComplementTrace A H = AiMathLab.P0054.G413.blocker
        (smallTrace A H) := by
  have hfirst := smallTrace_eq_blocker_largeComplement
    hsat hblock hHcard hsmallRows hlargeRows
  refine ⟨hfirst, ?_⟩
  rw [hfirst, blocker_involution
    (largeComplementTrace_isClutter (H := H) hsat.1)]

end AiMathLab.P0054.CanonicalBlocker
