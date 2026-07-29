import AiMathLab.P0054MiddleSevenNineK4FiniteCore
import AiMathLab.P0054G420.MiddleFourDegreeFourExclusion

/-!
# Arbitrary-finite soundness core for the 7+9 `K₄` branch

The seven-row kernel blocker lifts to seven rows of the nine-row family.
Consequently the complement consists of exactly two rows.  Those two rows
are split into old, first-private, second-private, and shared fresh points;
the four pieces correspond to the fixed intervals in the finite model.
-/

namespace AiMathLab.P0054.MiddleSevenNineK4Sound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineK4Finite

theorem liftFamily_two_extra_partition {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (hLiftCard : (blocker (avoidPoint H x)).card = 7)
    (hBlockerCard : (blocker H).card = 9) :
    let lifted := middleFourSemanticLiftFamily H x
    (blocker H \ lifted).card = 2 ∧
      blocker H = (blocker H \ lifted) ∪ lifted := by
  dsimp only
  have hSubset : middleFourSemanticLiftFamily H x ⊆ blocker H :=
    middleFourSemanticLiftFamily_subset_blocker H x
  have hLiftedCard : (middleFourSemanticLiftFamily H x).card = 7 := by
    rw [middleFourSemanticLiftFamily_card, hLiftCard]
  constructor
  · rw [Finset.card_sdiff_of_subset hSubset,
      hBlockerCard, hLiftedCard]
  · exact (Finset.sdiff_union_of_subset hSubset).symm

theorem liftFamily_exists_two_extras {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (hLiftCard : (blocker (avoidPoint H x)).card = 7)
    (hBlockerCard : (blocker H).card = 9) :
    ∃ first second,
      first ≠ second ∧
      first ∈ blocker H ∧ second ∈ blocker H ∧
      first ∉ middleFourSemanticLiftFamily H x ∧
      second ∉ middleFourSemanticLiftFamily H x ∧
      blocker H = insert first
        (insert second (middleFourSemanticLiftFamily H x)) := by
  obtain ⟨hDifferenceCard, hUnion⟩ :=
    liftFamily_two_extra_partition H x hLiftCard hBlockerCard
  obtain ⟨first, second, hNe, hDifference⟩ :=
    Finset.card_eq_two.mp hDifferenceCard
  have hFirstDifference :
      first ∈ blocker H \ middleFourSemanticLiftFamily H x := by
    simp [hDifference]
  have hSecondDifference :
      second ∈ blocker H \ middleFourSemanticLiftFamily H x := by
    simp [hDifference]
  have hFirst := Finset.mem_sdiff.mp hFirstDifference
  have hSecond := Finset.mem_sdiff.mp hSecondDifference
  refine ⟨first, second, hNe, hFirst.1,
    hSecond.1, hFirst.2, hSecond.2, ?_⟩
  calc
    blocker H =
        (blocker H \ middleFourSemanticLiftFamily H x) ∪
          middleFourSemanticLiftFamily H x := hUnion
    _ = {first, second} ∪ middleFourSemanticLiftFamily H x := by
      rw [hDifference]
    _ = insert first
        (insert second (middleFourSemanticLiftFamily H x)) := by
      ext row
      simp

def sevenNineK4ActiveDomain {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) : Finset alpha :=
  insert x (fourActiveUniverse (avoidPoint H x))

def sevenNineK4OldPart {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha) (row : G413.Row alpha) :
    G413.Row alpha :=
  row ∩ sevenNineK4ActiveDomain H x

def sevenNineK4FirstPrivateFresh {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) : G413.Row alpha :=
  first \ (sevenNineK4ActiveDomain H x ∪ second)

def sevenNineK4SecondPrivateFresh {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) : G413.Row alpha :=
  second \ (sevenNineK4ActiveDomain H x ∪ first)

def sevenNineK4SharedFresh {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) : G413.Row alpha :=
  (first ∩ second) \ sevenNineK4ActiveDomain H x

theorem sevenNineK4_first_decompose {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    first =
      (sevenNineK4OldPart H x first ∪
        sevenNineK4FirstPrivateFresh H x first second) ∪
          sevenNineK4SharedFresh H x first second := by
  ext point
  constructor
  · intro hPointFirst
    by_cases hPointActive : point ∈ sevenNineK4ActiveDomain H x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hPointFirst, hPointActive⟩))
    · by_cases hPointSecond : point ∈ second
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointFirst, hPointSecond⟩,
            hPointActive⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hPointFirst, by
            simp [hPointActive, hPointSecond]⟩))
  · intro hPoint
    rcases Finset.mem_union.mp hPoint with hOldOrPrivate | hShared
    · rcases Finset.mem_union.mp hOldOrPrivate with hOld | hPrivate
      · exact (Finset.mem_inter.mp hOld).1
      · exact (Finset.mem_sdiff.mp hPrivate).1
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hShared).1).1

theorem sevenNineK4_second_decompose {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    second =
      (sevenNineK4OldPart H x second ∪
        sevenNineK4SecondPrivateFresh H x first second) ∪
          sevenNineK4SharedFresh H x first second := by
  ext point
  constructor
  · intro hPointSecond
    by_cases hPointActive : point ∈ sevenNineK4ActiveDomain H x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hPointSecond, hPointActive⟩))
    · by_cases hPointFirst : point ∈ first
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hPointFirst, hPointSecond⟩,
            hPointActive⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hPointSecond, by
            simp [hPointActive, hPointFirst]⟩))
  · intro hPoint
    rcases Finset.mem_union.mp hPoint with hOldOrPrivate | hShared
    · rcases Finset.mem_union.mp hOldOrPrivate with hOld | hPrivate
      · exact (Finset.mem_inter.mp hOld).1
      · exact (Finset.mem_sdiff.mp hPrivate).1
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hShared).1).2

theorem sevenNineK4_firstPrivate_card_le {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    (sevenNineK4FirstPrivateFresh H x first second).card ≤ first.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem sevenNineK4_secondPrivate_card_le {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    (sevenNineK4SecondPrivateFresh H x first second).card ≤ second.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem sevenNineK4_shared_card_le_first {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    (sevenNineK4SharedFresh H x first second).card ≤ first.card :=
  Finset.card_le_card
    (Finset.sdiff_subset.trans Finset.inter_subset_left)

theorem sevenNineK4_shared_card_le_second {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) :
    (sevenNineK4SharedFresh H x first second).card ≤ second.card :=
  Finset.card_le_card
    (Finset.sdiff_subset.trans Finset.inter_subset_right)

theorem sevenNineK4_activePoints_length_eq_six {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20) :
    (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length = 6 := by
  have hModel :
      (middleFourModelSupports
        (fourActualSupportMultiplicity rowOrder).toList).length = 6 := by
    rw [hValues]
    decide
  rw [middleFourModelSupports_length_eq_activePoints] at hModel
  exact hModel

noncomputable def sevenNineK4TwoExtraPoint {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (point : alpha) : SevenNineK4Point :=
  if hActive : point ∈ sevenNineK4ActiveDomain H x then
    sevenNineK4WidenPoint (middleFourBasePoint rowOrder x point)
  else if hFirst : point ∈
      sevenNineK4FirstPrivateFresh H x first second then
    ⟨7 + (Finset.equivFin
      (sevenNineK4FirstPrivateFresh H x first second)
        ⟨point, hFirst⟩).val, by
      have hIndex := (Finset.equivFin
        (sevenNineK4FirstPrivateFresh H x first second)
          ⟨point, hFirst⟩).isLt
      omega⟩
  else if hSecond : point ∈
      sevenNineK4SecondPrivateFresh H x first second then
    ⟨14 + (Finset.equivFin
      (sevenNineK4SecondPrivateFresh H x first second)
        ⟨point, hSecond⟩).val, by
      have hIndex := (Finset.equivFin
        (sevenNineK4SecondPrivateFresh H x first second)
          ⟨point, hSecond⟩).isLt
      omega⟩
  else if hCommon : point ∈
      sevenNineK4SharedFresh H x first second then
    ⟨21 + (Finset.equivFin
      (sevenNineK4SharedFresh H x first second)
        ⟨point, hCommon⟩).val, by
      have hIndex := (Finset.equivFin
        (sevenNineK4SharedFresh H x first second)
          ⟨point, hCommon⟩).isLt
      omega⟩
  else
    sevenNineK4Center

theorem sevenNineK4TwoExtraPoint_active {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈ sevenNineK4ActiveDomain H x) :
    sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point =
        sevenNineK4WidenPoint (middleFourBasePoint rowOrder x point) := by
  simp [sevenNineK4TwoExtraPoint, hPoint]

theorem sevenNineK4TwoExtraPoint_active_val_le_six {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    {point : alpha} (hPoint : point ∈ sevenNineK4ActiveDomain H x) :
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val ≤ 6 := by
  rw [sevenNineK4TwoExtraPoint_active H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hPoint]
  change (middleFourBasePoint rowOrder x point).val ≤ 6
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  have hBound := middleFourBasePoint_val_le_activePoints_length
    H x rowOrder hLength (by
      simpa [sevenNineK4ActiveDomain, middleFourExtraActiveDomain]
        using hPoint)
  omega

theorem sevenNineK4TwoExtraPoint_firstPrivate_val {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4FirstPrivateFresh H x first second) :
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val =
        7 + (Finset.equivFin
          (sevenNineK4FirstPrivateFresh H x first second)
            ⟨point, hPoint⟩).val := by
  have hNotActive : point ∉ sevenNineK4ActiveDomain H x := by
    exact fun hActive => (Finset.mem_sdiff.mp hPoint).2
      (Finset.mem_union_left _ hActive)
  simp [sevenNineK4TwoExtraPoint, hNotActive, hPoint]

theorem sevenNineK4TwoExtraPoint_secondPrivate_val {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4SecondPrivateFresh H x first second) :
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val =
        14 + (Finset.equivFin
          (sevenNineK4SecondPrivateFresh H x first second)
            ⟨point, hPoint⟩).val := by
  have hExcluded := (Finset.mem_sdiff.mp hPoint).2
  have hNotActive : point ∉ sevenNineK4ActiveDomain H x := by
    exact fun hActive => hExcluded (Finset.mem_union_left _ hActive)
  have hNotFirst : point ∉ first := by
    exact fun hFirst => hExcluded (Finset.mem_union_right _ hFirst)
  have hNotFirstPrivate : point ∉
      sevenNineK4FirstPrivateFresh H x first second := by
    exact fun hFirst => hNotFirst (Finset.mem_sdiff.mp hFirst).1
  simp [sevenNineK4TwoExtraPoint, hNotActive,
    hNotFirstPrivate, hPoint]

theorem sevenNineK4TwoExtraPoint_shared_val {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4SharedFresh H x first second) :
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val =
        21 + (Finset.equivFin
          (sevenNineK4SharedFresh H x first second)
            ⟨point, hPoint⟩).val := by
  have hIntersection := Finset.mem_inter.mp (Finset.mem_sdiff.mp hPoint).1
  have hNotActive := (Finset.mem_sdiff.mp hPoint).2
  have hNotFirstPrivate : point ∉
      sevenNineK4FirstPrivateFresh H x first second := by
    intro hFirst
    exact (Finset.mem_sdiff.mp hFirst).2
      (Finset.mem_union_right _ hIntersection.2)
  have hNotSecondPrivate : point ∉
      sevenNineK4SecondPrivateFresh H x first second := by
    intro hSecond
    exact (Finset.mem_sdiff.mp hSecond).2
      (Finset.mem_union_right _ hIntersection.1)
  simp [sevenNineK4TwoExtraPoint, hNotActive,
    hNotFirstPrivate, hNotSecondPrivate, hPoint]

theorem sevenNineK4WidenPoint_injective :
    Function.Injective sevenNineK4WidenPoint := by
  intro left right hEq
  apply Fin.ext
  exact congrArg (fun point : SevenNineK4Point => point.val) hEq

theorem sevenNineK4TwoExtraPoint_firstPrivate_bounds {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4FirstPrivateFresh H x first second) :
    7 ≤ (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val ∧
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val < 14 := by
  rw [sevenNineK4TwoExtraPoint_firstPrivate_val H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hPoint]
  have hIndex := (Finset.equivFin
    (sevenNineK4FirstPrivateFresh H x first second)
      ⟨point, hPoint⟩).isLt
  omega

theorem sevenNineK4TwoExtraPoint_secondPrivate_bounds {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4SecondPrivateFresh H x first second) :
    14 ≤ (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val ∧
    (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val < 21 := by
  rw [sevenNineK4TwoExtraPoint_secondPrivate_val H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hPoint]
  have hIndex := (Finset.equivFin
    (sevenNineK4SecondPrivateFresh H x first second)
      ⟨point, hPoint⟩).isLt
  omega

theorem sevenNineK4TwoExtraPoint_shared_bounds {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    {point : alpha} (hPoint : point ∈
      sevenNineK4SharedFresh H x first second) :
    21 ≤ (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared point).val := by
  rw [sevenNineK4TwoExtraPoint_shared_val H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hPoint]
  omega

theorem sevenNineK4TwoExtraPoint_firstPrivate_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    Set.InjOn (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared)
      (sevenNineK4FirstPrivateFresh H x first second) := by
  intro left hLeft right hRight hEq
  have hVal := congrArg Fin.val hEq
  rw [sevenNineK4TwoExtraPoint_firstPrivate_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hLeft,
    sevenNineK4TwoExtraPoint_firstPrivate_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hRight] at hVal
  have hIndexEq :
      Finset.equivFin (sevenNineK4FirstPrivateFresh H x first second)
          ⟨left, hLeft⟩ =
        Finset.equivFin (sevenNineK4FirstPrivateFresh H x first second)
          ⟨right, hRight⟩ := by
    apply Fin.ext
    omega
  exact congrArg Subtype.val
    ((Finset.equivFin
      (sevenNineK4FirstPrivateFresh H x first second)).injective hIndexEq)

theorem sevenNineK4TwoExtraPoint_secondPrivate_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    Set.InjOn (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared)
      (sevenNineK4SecondPrivateFresh H x first second) := by
  intro left hLeft right hRight hEq
  have hVal := congrArg Fin.val hEq
  rw [sevenNineK4TwoExtraPoint_secondPrivate_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hLeft,
    sevenNineK4TwoExtraPoint_secondPrivate_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hRight] at hVal
  have hIndexEq :
      Finset.equivFin (sevenNineK4SecondPrivateFresh H x first second)
          ⟨left, hLeft⟩ =
        Finset.equivFin (sevenNineK4SecondPrivateFresh H x first second)
          ⟨right, hRight⟩ := by
    apply Fin.ext
    omega
  exact congrArg Subtype.val
    ((Finset.equivFin
      (sevenNineK4SecondPrivateFresh H x first second)).injective hIndexEq)

theorem sevenNineK4TwoExtraPoint_shared_injective {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    Set.InjOn (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared)
      (sevenNineK4SharedFresh H x first second) := by
  intro left hLeft right hRight hEq
  have hVal := congrArg Fin.val hEq
  rw [sevenNineK4TwoExtraPoint_shared_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hLeft,
    sevenNineK4TwoExtraPoint_shared_val H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared hRight] at hVal
  have hIndexEq :
      Finset.equivFin (sevenNineK4SharedFresh H x first second)
          ⟨left, hLeft⟩ =
        Finset.equivFin (sevenNineK4SharedFresh H x first second)
          ⟨right, hRight⟩ := by
    apply Fin.ext
    omega
  exact congrArg Subtype.val
    ((Finset.equivFin
      (sevenNineK4SharedFresh H x first second)).injective hIndexEq)

def sevenNineK4TwoExtraDomain {alpha : Type*} [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha) : Finset alpha :=
  ((sevenNineK4ActiveDomain H x ∪
      sevenNineK4FirstPrivateFresh H x first second) ∪
    sevenNineK4SecondPrivateFresh H x first second) ∪
      sevenNineK4SharedFresh H x first second

theorem sevenNineK4TwoExtraPoint_injOn {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20) :
    Set.InjOn (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared)
        (sevenNineK4TwoExtraDomain H x first second) := by
  intro left hLeft right hRight hEq
  have hLeftCases :
      left ∈ sevenNineK4ActiveDomain H x ∨
      left ∈ sevenNineK4FirstPrivateFresh H x first second ∨
      left ∈ sevenNineK4SecondPrivateFresh H x first second ∨
      left ∈ sevenNineK4SharedFresh H x first second := by
    simpa [sevenNineK4TwoExtraDomain, or_assoc] using hLeft
  have hRightCases :
      right ∈ sevenNineK4ActiveDomain H x ∨
      right ∈ sevenNineK4FirstPrivateFresh H x first second ∨
      right ∈ sevenNineK4SecondPrivateFresh H x first second ∨
      right ∈ sevenNineK4SharedFresh H x first second := by
    simpa [sevenNineK4TwoExtraDomain, or_assoc] using hRight
  have hVal := congrArg Fin.val hEq
  rcases hLeftCases with hLeftActive | hLeftFirst |
      hLeftSecond | hLeftShared
  · rcases hRightCases with hRightActive | hRightFirst |
        hRightSecond | hRightShared
    · have hEq' := hEq
      rw [sevenNineK4TwoExtraPoint_active H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared hLeftActive,
        sevenNineK4TwoExtraPoint_active H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared hRightActive] at hEq'
      have hLength : (fourActivePoints
          (fourActualSupportMultiplicity rowOrder)).length < 16 := by
        rw [sevenNineK4_activePoints_length_eq_six rowOrder hValues]
        omega
      exact middleFourBasePoint_injOn_active_insert H x rowOrder hLength
        (by simpa [sevenNineK4ActiveDomain] using hLeftActive)
        (by simpa [sevenNineK4ActiveDomain] using hRightActive)
        (sevenNineK4WidenPoint_injective hEq')
    · have hLeftBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hLeftActive
      have hRightBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightFirst
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hLeftActive
      have hRightBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightSecond
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hLeftActive
      have hRightBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightShared
      omega
  · rcases hRightCases with hRightActive | hRightFirst |
        hRightSecond | hRightShared
    · have hLeftBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftFirst
      have hRightBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hRightActive
      omega
    · exact sevenNineK4TwoExtraPoint_firstPrivate_injective
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftFirst hRightFirst hEq
    · have hLeftBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftFirst
      have hRightBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightSecond
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftFirst
      have hRightBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightShared
      omega
  · rcases hRightCases with hRightActive | hRightFirst |
        hRightSecond | hRightShared
    · have hLeftBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftSecond
      have hRightBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hRightActive
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftSecond
      have hRightBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightFirst
      omega
    · exact sevenNineK4TwoExtraPoint_secondPrivate_injective
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftSecond hRightSecond hEq
    · have hLeftBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftSecond
      have hRightBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightShared
      omega
  · rcases hRightCases with hRightActive | hRightFirst |
        hRightSecond | hRightShared
    · have hLeftBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftShared
      have hRightBound := sevenNineK4TwoExtraPoint_active_val_le_six
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hRightActive
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftShared
      have hRightBound := sevenNineK4TwoExtraPoint_firstPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightFirst
      omega
    · have hLeftBound := sevenNineK4TwoExtraPoint_shared_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftShared
      have hRightBound := sevenNineK4TwoExtraPoint_secondPrivate_bounds
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hRightSecond
      omega
    · exact sevenNineK4TwoExtraPoint_shared_injective
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hLeftShared hRightShared hEq

theorem sevenNineK4_blocker_biUnion_subset_domain {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (first second : G413.Row alpha)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x))) :
    (blocker H).biUnion id ⊆
      sevenNineK4TwoExtraDomain H x first second := by
  intro point hPoint
  obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
  rw [hBlocker] at hRow
  rcases Finset.mem_insert.mp hRow with hRow | hRow
  · subst row
    rw [sevenNineK4_first_decompose H x first second] at hPointRow
    rcases Finset.mem_union.mp hPointRow with hOldOrPrivate | hShared
    · rcases Finset.mem_union.mp hOldOrPrivate with hOld | hPrivate
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_union_left _ (Finset.mem_inter.mp hOld).2
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_union_right _ hPrivate
    · exact Finset.mem_union_right _ hShared
  · rcases Finset.mem_insert.mp hRow with hRow | hRow
    · subst row
      rw [sevenNineK4_second_decompose H x first second] at hPointRow
      rcases Finset.mem_union.mp hPointRow with hOldOrPrivate | hShared
      · rcases Finset.mem_union.mp hOldOrPrivate with hOld | hPrivate
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact Finset.mem_union_left _ (Finset.mem_inter.mp hOld).2
        · apply Finset.mem_union_left
          exact Finset.mem_union_right _ hPrivate
      · exact Finset.mem_union_right _ hShared
    · obtain ⟨source, hSource, hRowEq⟩ := Finset.mem_image.mp hRow
      rw [← hRowEq] at hPointRow
      have hActive := middleFourAvoidBlockerLift_subset_active_insert
        H x hSource hPointRow
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_union_left _ hActive

theorem sevenNineK4TwoExtraPoint_injOn_blocker {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x))) :
    Set.InjOn (sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared) ((blocker H).biUnion id) :=
  (sevenNineK4TwoExtraPoint_injOn H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hValues).mono
      (sevenNineK4_blocker_biUnion_subset_domain
        H x first second hBlocker)

theorem finset_image_eq_sevenNineK4FreshBlock {alpha : Type*}
    [DecidableEq alpha] (source : Finset alpha)
    (pointMap : alpha → SevenNineK4Point) (start : Nat)
    (hValue : ∀ {point : alpha} (hPoint : point ∈ source),
      (pointMap point).val = start +
        (Finset.equivFin source ⟨point, hPoint⟩).val) :
    source.image pointMap =
      sevenNineK4FreshBlock start source.card := by
  ext modelPoint
  constructor
  · intro hModelPoint
    obtain ⟨point, hPoint, rfl⟩ := Finset.mem_image.mp hModelPoint
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hValue hPoint]
    have hIndex := (Finset.equivFin source ⟨point, hPoint⟩).isLt
    omega
  · intro hModelPoint
    obtain ⟨_hUniv, hBounds⟩ := Finset.mem_filter.mp hModelPoint
    let index : Fin source.card := ⟨modelPoint.val - start, by omega⟩
    let point := (Finset.equivFin source).symm index
    apply Finset.mem_image.mpr
    refine ⟨point.1, point.2, ?_⟩
    apply Fin.ext
    rw [hValue point.2]
    have hIndexEq : Finset.equivFin source ⟨point.1, point.2⟩ = index := by
      change (Finset.equivFin source) ((Finset.equivFin source).symm index) = index
      exact Equiv.apply_symm_apply _ _
    rw [hIndexEq]
    dsimp [index]
    omega

theorem sevenNineK4_firstPrivate_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    (sevenNineK4FirstPrivateFresh H x first second).image
        (sevenNineK4TwoExtraPoint H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared) =
      sevenNineK4PrivateFirst
        (sevenNineK4FirstPrivateFresh H x first second).card := by
  apply finset_image_eq_sevenNineK4FreshBlock
  intro point hPoint
  exact sevenNineK4TwoExtraPoint_firstPrivate_val
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared hPoint

theorem sevenNineK4_secondPrivate_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    (sevenNineK4SecondPrivateFresh H x first second).image
        (sevenNineK4TwoExtraPoint H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared) =
      sevenNineK4PrivateSecond
        (sevenNineK4SecondPrivateFresh H x first second).card := by
  apply finset_image_eq_sevenNineK4FreshBlock
  intro point hPoint
  exact sevenNineK4TwoExtraPoint_secondPrivate_val
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared hPoint

theorem sevenNineK4_shared_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    (sevenNineK4SharedFresh H x first second).image
        (sevenNineK4TwoExtraPoint H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared) =
      sevenNineK4Shared
        (sevenNineK4SharedFresh H x first second).card := by
  apply finset_image_eq_sevenNineK4FreshBlock
  intro point hPoint
  exact sevenNineK4TwoExtraPoint_shared_val
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared hPoint

noncomputable def sevenNineK4ActualOldModel {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (row : G413.Row alpha) :
    G413.Row SevenNineK4Point :=
  (sevenNineK4OldPart H x row).image fun point =>
    sevenNineK4WidenPoint (middleFourBasePoint rowOrder x point)

noncomputable def sevenNineK4ActualExtraKey {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (row other : G413.Row alpha) : Nat :=
  sevenNineK4ExtraKey (sevenNineK4ActualOldModel H x rowOrder row)
    (row \ (sevenNineK4ActiveDomain H x ∪ other)).card

theorem liftFamily_exists_ordered_two_extras {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hLiftCard : (blocker (avoidPoint H x)).card = 7)
    (hBlockerCard : (blocker H).card = 9) :
    ∃ first second,
      first ≠ second ∧
      first ∈ blocker H ∧ second ∈ blocker H ∧
      first ∉ middleFourSemanticLiftFamily H x ∧
      second ∉ middleFourSemanticLiftFamily H x ∧
      blocker H = insert first
        (insert second (middleFourSemanticLiftFamily H x)) ∧
      sevenNineK4ActualExtraKey H x rowOrder first second ≤
        sevenNineK4ActualExtraKey H x rowOrder second first := by
  obtain ⟨first, second, hNe, hFirst, hSecond,
      hFirstNotLifted, hSecondNotLifted, hBlocker⟩ :=
    liftFamily_exists_two_extras H x hLiftCard hBlockerCard
  by_cases hKey : sevenNineK4ActualExtraKey H x rowOrder first second ≤
      sevenNineK4ActualExtraKey H x rowOrder second first
  · exact ⟨first, second, hNe, hFirst, hSecond,
      hFirstNotLifted, hSecondNotLifted, hBlocker, hKey⟩
  · refine ⟨second, first, hNe.symm, hSecond, hFirst,
      hSecondNotLifted, hFirstNotLifted, ?_, by omega⟩
    exact hBlocker.trans (Finset.insert_comm first second _)

theorem sevenNineK4_oldPart_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second row : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    (sevenNineK4OldPart H x row).image
        (sevenNineK4TwoExtraPoint H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared) =
      sevenNineK4ActualOldModel H x rowOrder row := by
  apply Finset.image_congr
  intro point hPoint
  exact sevenNineK4TwoExtraPoint_active H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared (Finset.mem_inter.mp hPoint).2

theorem sevenNineK4_first_image_decompose {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    first.image (sevenNineK4TwoExtraPoint H x rowOrder first second
        hFirstPrivate hSecondPrivate hShared) =
      (sevenNineK4ActualOldModel H x rowOrder first ∪
        sevenNineK4PrivateFirst
          (sevenNineK4FirstPrivateFresh H x first second).card) ∪
        sevenNineK4Shared
          (sevenNineK4SharedFresh H x first second).card := by
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  change first.image pointMap = _
  calc
    first.image pointMap =
        ((sevenNineK4OldPart H x first ∪
          sevenNineK4FirstPrivateFresh H x first second) ∪
            sevenNineK4SharedFresh H x first second).image pointMap :=
      congrArg (fun row => row.image pointMap)
        (sevenNineK4_first_decompose H x first second)
    _ = _ := by
      rw [Finset.image_union, Finset.image_union,
        sevenNineK4_oldPart_image H x rowOrder first second first
          hFirstPrivate hSecondPrivate hShared,
        sevenNineK4_firstPrivate_image H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared,
        sevenNineK4_shared_image H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared]

theorem sevenNineK4_second_image_decompose {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7) :
    second.image (sevenNineK4TwoExtraPoint H x rowOrder first second
        hFirstPrivate hSecondPrivate hShared) =
      (sevenNineK4ActualOldModel H x rowOrder second ∪
        sevenNineK4PrivateSecond
          (sevenNineK4SecondPrivateFresh H x first second).card) ∪
        sevenNineK4Shared
          (sevenNineK4SharedFresh H x first second).card := by
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  change second.image pointMap = _
  calc
    second.image pointMap =
        ((sevenNineK4OldPart H x second ∪
          sevenNineK4SecondPrivateFresh H x first second) ∪
            sevenNineK4SharedFresh H x first second).image pointMap :=
      congrArg (fun row => row.image pointMap)
        (sevenNineK4_second_decompose H x first second)
    _ = _ := by
      rw [Finset.image_union, Finset.image_union,
        sevenNineK4_oldPart_image H x rowOrder first second second
          hFirstPrivate hSecondPrivate hShared,
        sevenNineK4_secondPrivate_image H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared,
        sevenNineK4_shared_image H x rowOrder first second
          hFirstPrivate hSecondPrivate hShared]

theorem sevenNineK4_actualOldModel_subset_oldPoints {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (row : G413.Row alpha)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20) :
    sevenNineK4ActualOldModel H x rowOrder row ⊆
      sevenNineK4OldPoints.toFinset := by
  intro modelPoint hModelPoint
  obtain ⟨point, hPointOld, rfl⟩ := Finset.mem_image.mp hModelPoint
  have hPointActive := (Finset.mem_inter.mp hPointOld).2
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  have hVal := middleFourBasePoint_val_le_activePoints_length
    H x rowOrder hLength (by
      simpa [sevenNineK4ActiveDomain, middleFourExtraActiveDomain]
        using hPointActive)
  apply List.mem_toFinset.mpr
  apply List.mem_filter.mpr
  refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
  change (middleFourBasePoint rowOrder x point).val < 7
  omega

theorem sevenNineK4_actualOldModel_exists_list {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x) (row : G413.Row alpha)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20) :
    ∃ old ∈ middleFourListPowerset sevenNineK4OldPoints,
      old.toFinset = sevenNineK4ActualOldModel H x rowOrder row := by
  let model := sevenNineK4ActualOldModel H x rowOrder row
  let old := sevenNineK4OldPoints.filter fun point => point ∈ model
  have hSubset : model ⊆ sevenNineK4OldPoints.toFinset := by
    simpa [model] using sevenNineK4_actualOldModel_subset_oldPoints
      H x rowOrder row hValues
  refine ⟨old, ?_, ?_⟩
  · simpa [old] using middleFourListPowerset_filter_mem
      (fun point => point ∈ model) sevenNineK4OldPoints
  · ext modelPoint
    constructor
    · intro hPoint
      have hPointList := List.mem_toFinset.mp hPoint
      exact of_decide_eq_true (List.mem_filter.mp hPointList).2
    · intro hPoint
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      exact ⟨List.mem_toFinset.mp (hSubset hPoint), decide_eq_true hPoint⟩

theorem sevenNineK4_actualOldModels_mem_oldPairs {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (base : List (G413.Row SevenNineK4Point))
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hAdmissible : sevenNineK4OldPairAdmissible base
      (sevenNineK4ActualOldModel H x rowOrder first)
      (sevenNineK4ActualOldModel H x rowOrder second) = true) :
    (sevenNineK4ActualOldModel H x rowOrder first,
      sevenNineK4ActualOldModel H x rowOrder second) ∈
        sevenNineK4OldPairs base := by
  obtain ⟨oldFirst, hOldFirst, hOldFirstSet⟩ :=
    sevenNineK4_actualOldModel_exists_list
      H x rowOrder first hValues
  obtain ⟨oldSecond, hOldSecond, hOldSecondSet⟩ :=
    sevenNineK4_actualOldModel_exists_list
      H x rowOrder second hValues
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨oldFirst, hOldFirst, ?_⟩
    apply List.mem_map.mpr
    refine ⟨oldSecond, hOldSecond, ?_⟩
    rw [hOldFirstSet, hOldSecondSet]
  · exact hAdmissible

theorem sevenNineK4WidenRows_toFinset
    (rows : List (G413.Row MiddleFourModelPoint)) :
    (sevenNineK4WidenRows rows).toFinset =
      rows.toFinset.image sevenNineK4WidenRow := by
  induction rows with
  | nil => simp [sevenNineK4WidenRows]
  | cons row rows ih =>
      simp only [sevenNineK4WidenRows, List.map_cons, List.toFinset_cons,
        Finset.image_insert]
      change insert (sevenNineK4WidenRow row)
          (sevenNineK4WidenRows rows).toFinset = _
      rw [ih]

theorem sevenNineK4_semanticBase_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2) :
    (sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))).toFinset =
        (middleFourSemanticLiftFamily H x).image fun row =>
          row.image (sevenNineK4TwoExtraPoint H x rowOrder first second
            hFirstPrivate hSecondPrivate hShared) := by
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  rw [sevenNineK4WidenRows_toFinset,
    middleFourSemanticLiftBaseRows_toFinset H x rowOrder
      hHBlockerRows hAvoidBlockerRows hLength,
    Finset.image_image, middleFourSemanticLiftFamily,
    Finset.image_image]
  apply Finset.image_congr
  intro source hSource
  unfold sevenNineK4WidenRow
  simp only [Function.comp_apply]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro point hPoint
  exact (sevenNineK4TwoExtraPoint_active H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
      (middleFourAvoidBlockerLift_subset_active_insert
        H x hSource hPoint)).symm

theorem sevenNineK4_widenedBase_mem_bases
    (selected : List (G413.Row MiddleFourModelPoint))
    (hSelection : selected ∈
      middleFourModelLiftSelectionRows middleFourDegreeFourVector20) :
    sevenNineK4WidenRows
      (middleFourModelLiftBaseRows middleFourDegreeFourVector20 selected) ∈
        sevenNineK4Bases := by
  rw [middleFourDegreeFourVector20_selections] at hSelection
  have hSelection' :
      selected = middleFourDegreeFourVector20Selected0 ∨
      selected = middleFourDegreeFourVector20Selected1 ∨
      selected = middleFourDegreeFourVector20Selected2 ∨
      selected = middleFourDegreeFourVector20Selected3 ∨
      selected = middleFourDegreeFourVector20Selected4 := by
    simpa [middleFourDegreeFourVector20Selections,
      middleFourDegreeFourVector20Selected0,
      middleFourDegreeFourVector20Selected1,
      middleFourDegreeFourVector20Selected2,
      middleFourDegreeFourVector20Selected3,
      middleFourDegreeFourVector20Selected4] using hSelection
  rcases hSelection' with hSelection | hSelection | hSelection |
      hSelection | hSelection
  · subst selected
    rw [middleFourDegreeFourVector20_base0]
    simp [sevenNineK4Bases]
  · subst selected
    rw [middleFourDegreeFourVector20_base1]
    simp [sevenNineK4Bases]
  · subst selected
    rw [middleFourDegreeFourVector20_base2]
    simp [sevenNineK4Bases]
  · subst selected
    rw [middleFourDegreeFourVector20_base3]
    simp [sevenNineK4Bases]
  · subst selected
    rw [middleFourDegreeFourVector20_base4]
    simp [sevenNineK4Bases]

theorem sevenNineK4_semanticBase_mem_bases {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList) :
    sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder)) ∈ sevenNineK4Bases := by
  rw [hValues] at hSelection ⊢
  exact sevenNineK4_widenedBase_mem_bases
    (middleFourSemanticSelected H x rowOrder) hSelection

theorem sevenNineK4_candidateSet_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x))) :
    let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
    let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
    let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
    let privateFirst :=
      (sevenNineK4FirstPrivateFresh H x first second).card
    let privateSecond :=
      (sevenNineK4SecondPrivateFresh H x first second).card
    let shared := (sevenNineK4SharedFresh H x first second).card
    (sevenNineK4TwoExtraRows base oldFirst oldSecond
      privateFirst privateSecond shared).toFinset =
        (blocker H).image fun row =>
          row.image (sevenNineK4TwoExtraPoint H x rowOrder first second
            hFirstPrivate hSecondPrivate hShared) := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  have hBaseImage := sevenNineK4_semanticBase_image
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
      hValues hHBlockerRows hAvoidBlockerRows
  have hFirstImage := sevenNineK4_first_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  have hSecondImage := sevenNineK4_second_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  change (sevenNineK4SecondExtra
      (sevenNineK4ActualOldModel H x rowOrder second)
      (sevenNineK4SecondPrivateFresh H x first second).card
      (sevenNineK4SharedFresh H x first second).card ::
    sevenNineK4FirstExtra
      (sevenNineK4ActualOldModel H x rowOrder first)
      (sevenNineK4FirstPrivateFresh H x first second).card
      (sevenNineK4SharedFresh H x first second).card ::
    sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))).toFinset = _
  simp only [sevenNineK4SecondExtra, sevenNineK4FirstExtra]
  rw [List.toFinset_cons, List.toFinset_cons,
    ← hSecondImage, ← hFirstImage, hBaseImage]
  rw [← Finset.image_insert, ← Finset.image_insert,
    Finset.insert_comm second first, ← hBlocker]

theorem isClutter_image_of_injOn_biUnion {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    {family : G413.Hypergraph alpha} (pointMap : alpha → beta)
    (hClutter : IsClutter family)
    (hPointMap : Set.InjOn pointMap (family.biUnion id)) :
    IsClutter (family.image fun row => row.image pointMap) := by
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

theorem sevenNineK4_extraImages_not_base {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hFirstBlocker : first ∈ blocker H)
    (hSecondBlocker : second ∈ blocker H)
    (hFirstNotLifted : first ∉ middleFourSemanticLiftFamily H x)
    (hSecondNotLifted : second ∉ middleFourSemanticLiftFamily H x)
    (hNe : first ≠ second)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x))) :
    let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared
    let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
    first.image pointMap ∉ base.toFinset ∧
      second.image pointMap ∉ insert (first.image pointMap) base.toFinset := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder))
  have hBaseImage : base.toFinset =
      (middleFourSemanticLiftFamily H x).image fun row =>
        row.image pointMap := by
    simpa [base, pointMap] using sevenNineK4_semanticBase_image
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hHBlockerRows hAvoidBlockerRows
  have hPointMap : Set.InjOn pointMap ((blocker H).biUnion id) := by
    simpa [pointMap] using sevenNineK4TwoExtraPoint_injOn_blocker
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hBlocker
  have hRowMap : Set.InjOn
      (fun row : G413.Row alpha => row.image pointMap) (blocker H) :=
    row_image_injOn_of_injOn (fun _ hPoint => hPoint) hPointMap
  constructor
  · intro hFirstBase
    rw [hBaseImage] at hFirstBase
    obtain ⟨source, hSource, hSourceImage⟩ :=
      Finset.mem_image.mp hFirstBase
    have hSourceBlocker :=
      middleFourSemanticLiftFamily_subset_blocker H x hSource
    have hEq : first = source :=
      hRowMap hFirstBlocker hSourceBlocker hSourceImage.symm
    exact hFirstNotLifted (hEq.symm ▸ hSource)
  · intro hSecondRest
    rcases Finset.mem_insert.mp hSecondRest with hSecondFirst | hSecondBase
    · have hEq : second = first :=
        hRowMap hSecondBlocker hFirstBlocker hSecondFirst
      exact hNe hEq.symm
    · rw [hBaseImage] at hSecondBase
      obtain ⟨source, hSource, hSourceImage⟩ :=
        Finset.mem_image.mp hSecondBase
      have hSourceBlocker :=
        middleFourSemanticLiftFamily_subset_blocker H x hSource
      have hEq : second = source :=
        hRowMap hSecondBlocker hSourceBlocker hSourceImage.symm
      exact hSecondNotLifted (hEq.symm ▸ hSource)

theorem sevenNineK4RowsMaxDegreeAtMost_of_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (rows : List (G413.Row SevenNineK4Point))
    {family : G413.Hypergraph alpha} {domain : Finset alpha}
    (pointMap : alpha → SevenNineK4Point)
    (hRows : rows.toFinset =
      family.image fun row => row.image pointMap)
    (hFamilyDomain : family.biUnion id ⊆ domain)
    (hPointMap : Set.InjOn pointMap domain)
    {bound : Nat} (hMaxDegree : MaxDegreeAtMost family bound) :
    sevenNineK4RowsMaxDegreeAtMost rows bound = true := by
  rw [sevenNineK4RowsMaxDegreeAtMost, List.all_eq_true]
  intro modelPoint _hModelPoint
  apply decide_eq_true
  by_cases hActive : modelPoint ∈ rows.toFinset.biUnion id
  · rw [hRows] at hActive
    obtain ⟨imageRow, hImageRow, hModelImage⟩ :=
      Finset.mem_biUnion.mp hActive
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
    obtain ⟨point, hPointSource, hPointEq⟩ :=
      Finset.mem_image.mp hModelImage
    have hPointDomain : point ∈ domain :=
      hFamilyDomain (Finset.mem_biUnion.mpr
        ⟨source, hSource, hPointSource⟩)
    rw [← hPointEq, hRows,
      degree_image_eq_of_injOn hPointDomain hFamilyDomain hPointMap]
    exact hMaxDegree point
  · have hFilter : rows.toFinset.filter
        (fun row => modelPoint ∈ row) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro row hRow
      apply hActive
      exact Finset.mem_biUnion.mpr
        ⟨row, (Finset.mem_filter.mp hRow).1,
          (Finset.mem_filter.mp hRow).2⟩
    simp [degree, hFilter]

theorem sevenNineK4_actualOldPair_admissible {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hFirstBlocker : first ∈ blocker H)
    (hSecondBlocker : second ∈ blocker H)
    (hFirstNotLifted : first ∉ middleFourSemanticLiftFamily H x)
    (hSecondNotLifted : second ∉ middleFourSemanticLiftFamily H x)
    (hNe : first ≠ second)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x)))
    (hBlockerMax : MaxDegreeAtMost (blocker H) 4) :
    let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
    sevenNineK4OldPairAdmissible base
      (sevenNineK4ActualOldModel H x rowOrder first)
      (sevenNineK4ActualOldModel H x rowOrder second) = true := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder))
  let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
  let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
  let privateFirst :=
    (sevenNineK4FirstPrivateFresh H x first second).card
  let privateSecond :=
    (sevenNineK4SecondPrivateFresh H x first second).card
  let shared := (sevenNineK4SharedFresh H x first second).card
  let rows := sevenNineK4TwoExtraRows base oldFirst oldSecond
    privateFirst privateSecond shared
  have hCandidateSet : rows.toFinset =
      (blocker H).image fun row => row.image pointMap := by
    simpa [rows, base, oldFirst, oldSecond, privateFirst,
      privateSecond, shared, pointMap] using sevenNineK4_candidateSet_image
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHBlockerRows hAvoidBlockerRows hBlocker
  have hPointMap : Set.InjOn pointMap ((blocker H).biUnion id) := by
    simpa [pointMap] using sevenNineK4TwoExtraPoint_injOn_blocker
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hBlocker
  have hMax : sevenNineK4RowsMaxDegreeAtMost rows 4 = true :=
    sevenNineK4RowsMaxDegreeAtMost_of_image rows pointMap hCandidateSet
      (fun _ hPoint => hPoint) hPointMap hBlockerMax
  have hNot := sevenNineK4_extraImages_not_base
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
      hValues hHBlockerRows hAvoidBlockerRows hFirstBlocker hSecondBlocker
        hFirstNotLifted hSecondNotLifted hNe hBlocker
  have hFirstImage := sevenNineK4_first_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  have hSecondImage := sevenNineK4_second_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  apply sevenNineK4OldPairAdmissible_of_candidate_max base oldFirst oldSecond
    privateFirst privateSecond shared
  · simpa [base, oldFirst, privateFirst, shared, pointMap,
      hFirstImage, sevenNineK4FirstExtra, Finset.union_assoc] using hNot.1
  · simpa [base, oldFirst, oldSecond, privateFirst, privateSecond,
      shared, pointMap, hFirstImage, hSecondImage,
      sevenNineK4FirstExtra, sevenNineK4SecondExtra,
      Finset.union_assoc] using hNot.2
  · simpa [rows] using hMax

theorem sevenNineK4_actualCandidateStructure {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHCard : H.card = 7)
    (hBlockerCard : (blocker H).card = 9)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hFirstBlocker : first ∈ blocker H)
    (hSecondBlocker : second ∈ blocker H)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x)))
    (hKey : sevenNineK4ActualExtraKey H x rowOrder first second ≤
      sevenNineK4ActualExtraKey H x rowOrder second first) :
    let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
    let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
    let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
    let privateFirst :=
      (sevenNineK4FirstPrivateFresh H x first second).card
    let privateSecond :=
      (sevenNineK4SecondPrivateFresh H x first second).card
    let shared := (sevenNineK4SharedFresh H x first second).card
    sevenNineK4CandidateStructure base oldFirst oldSecond
      privateFirst privateSecond shared = true := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder))
  let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
  let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
  let privateFirst :=
    (sevenNineK4FirstPrivateFresh H x first second).card
  let privateSecond :=
    (sevenNineK4SecondPrivateFresh H x first second).card
  let shared := (sevenNineK4SharedFresh H x first second).card
  let firstModel :=
    sevenNineK4FirstExtra oldFirst privateFirst shared
  let secondModel :=
    sevenNineK4SecondExtra oldSecond privateSecond shared
  let rows := sevenNineK4TwoExtraRows base oldFirst oldSecond
    privateFirst privateSecond shared
  have hCandidateSet : rows.toFinset =
      (blocker H).image fun row => row.image pointMap := by
    simpa [rows, base, oldFirst, oldSecond, privateFirst,
      privateSecond, shared, pointMap] using sevenNineK4_candidateSet_image
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHBlockerRows hAvoidBlockerRows hBlocker
  have hPointMap : Set.InjOn pointMap ((blocker H).biUnion id) := by
    simpa [pointMap] using sevenNineK4TwoExtraPoint_injOn_blocker
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hBlocker
  have hRowMap : Set.InjOn
      (fun row : G413.Row alpha => row.image pointMap) (blocker H) :=
    row_image_injOn_of_injOn (fun _ hPoint => hPoint) hPointMap
  have hFirstPointMap : Set.InjOn pointMap first := by
    intro left hLeft right hRight hEqual
    apply hPointMap
    · exact Finset.mem_biUnion.mpr
        ⟨first, hFirstBlocker, hLeft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨first, hFirstBlocker, hRight⟩
    · exact hEqual
  have hSecondPointMap : Set.InjOn pointMap second := by
    intro left hLeft right hRight hEqual
    apply hPointMap
    · exact Finset.mem_biUnion.mpr
        ⟨second, hSecondBlocker, hLeft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨second, hSecondBlocker, hRight⟩
    · exact hEqual
  have hFirstImage := sevenNineK4_first_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  have hSecondImage := sevenNineK4_second_image_decompose
    H x rowOrder first second hFirstPrivate hSecondPrivate hShared
  have hFirstModelCard : firstModel.card = first.card := by
    dsimp [firstModel, oldFirst, privateFirst, shared]
    rw [sevenNineK4FirstExtra, ← hFirstImage]
    exact Finset.card_image_iff.mpr hFirstPointMap
  have hSecondModelCard : secondModel.card = second.card := by
    dsimp [secondModel, oldSecond, privateSecond, shared]
    rw [sevenNineK4SecondExtra, ← hSecondImage]
    exact Finset.card_image_iff.mpr hSecondPointMap
  have hFirstUpper : first.card ≤ 7 :=
    (minimalTransversal_card_le_rows
      (mem_blocker.mp hFirstBlocker)).trans_eq hHCard
  have hSecondUpper : second.card ≤ 7 :=
    (minimalTransversal_card_le_rows
      (mem_blocker.mp hSecondBlocker)).trans_eq hHCard
  have hRowsCard : rows.toFinset.card = 9 := by
    rw [hCandidateSet, Finset.card_image_iff.mpr hRowMap,
      hBlockerCard]
  have hRowsClutter : IsClutter rows.toFinset := by
    rw [hCandidateSet]
    exact isClutter_image_of_injOn_biUnion pointMap
      (blocker_isClutter H) hPointMap
  apply sevenNineK4CandidateStructure_of base oldFirst oldSecond
    privateFirst privateSecond shared
  · simpa [sevenNineK4ActualExtraKey, oldFirst, oldSecond,
      privateFirst, privateSecond, sevenNineK4FirstPrivateFresh,
      sevenNineK4SecondPrivateFresh] using hKey
  · simpa [firstModel] using
      (show 3 ≤ first.card from hHBlockerRows first hFirstBlocker).trans_eq
        hFirstModelCard.symm
  · simpa [firstModel] using hFirstModelCard.trans_le hFirstUpper
  · simpa [secondModel] using
      (show 3 ≤ second.card from
        hHBlockerRows second hSecondBlocker).trans_eq
          hSecondModelCard.symm
  · simpa [secondModel] using hSecondModelCard.trans_le hSecondUpper
  · simpa [rows] using hRowsCard
  · simpa [rows] using hRowsClutter

theorem sevenNineK4_semanticKernel_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2) :
    let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared
    sevenNineK4KernelRows.toFinset =
      (avoidPoint H x).image fun row => row.image pointMap := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  rw [sevenNineK4KernelRows, sevenNineK4WidenRows_toFinset]
  change (middleFourModelKernel middleFourDegreeFourVector20).image
      sevenNineK4WidenRow = _
  rw [← hValues]
  calc
    (middleFourModelKernel
        (fourActualSupportMultiplicity rowOrder).toList).image
        sevenNineK4WidenRow =
      ((middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow => activeRow.image
          (middleFourActualModelPoint rowOrder))).image
        sevenNineK4WidenRow := by
          exact congrArg (fun family =>
            family.image sevenNineK4WidenRow)
              (middleFourActiveKernel_image_eq_modelKernel
                rowOrder hAvoidBlockerRows hLength).symm
    _ = (middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow => sevenNineK4WidenRow
          (activeRow.image (middleFourActualModelPoint rowOrder))) := by
          rw [Finset.image_image]
          rfl
    _ = (middleFourActiveKernelRows rowOrder).toFinset.image
        (fun activeRow =>
          (activeRow.image Subtype.val).image pointMap) := by
          apply Finset.image_congr
          intro activeRow _hActiveRow
          change (activeRow.image (middleFourActualModelPoint rowOrder)).image
              sevenNineK4WidenPoint =
            (activeRow.image Subtype.val).image pointMap
          rw [Finset.image_image, Finset.image_image]
          apply Finset.image_congr
          intro point _hPoint
          change sevenNineK4WidenPoint
              (middleFourActualModelPoint rowOrder point) =
            pointMap point.1
          symm
          have hActive : point.1 ∈ sevenNineK4ActiveDomain H x := by
            simpa [sevenNineK4ActiveDomain] using
              Finset.mem_insert_of_mem point.2
          calc
            pointMap point.1 = sevenNineK4WidenPoint
                (middleFourBasePoint rowOrder x point.1) := by
              simpa [pointMap] using sevenNineK4TwoExtraPoint_active
                H x rowOrder first second hFirstPrivate hSecondPrivate
                  hShared hActive
            _ = sevenNineK4WidenPoint
                (middleFourActualModelPoint rowOrder point) :=
              congrArg sevenNineK4WidenPoint
                (middleFourBasePoint_active rowOrder x point)
    _ = ((middleFourActiveKernelRows rowOrder).toFinset.image
          (fun activeRow => activeRow.image Subtype.val)).image
        (fun row => row.image pointMap) := by
          rw [Finset.image_image]
          rfl
    _ = (avoidPoint H x).image
        (fun row => row.image pointMap) := by
          exact congrArg
            (fun family => family.image
              (fun row => row.image pointMap))
            (middleFourActiveKernel_image_subtypeVal rowOrder)

theorem sevenNineK4TwoExtraPoint_center {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20) :
    sevenNineK4TwoExtraPoint H x rowOrder first second
      hFirstPrivate hSecondPrivate hShared x = sevenNineK4Center := by
  have hActive : x ∈ sevenNineK4ActiveDomain H x := by
    simp [sevenNineK4ActiveDomain]
  rw [sevenNineK4TwoExtraPoint_active H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared hActive,
    middleFourBasePoint_center H x rowOrder]
  apply Fin.ext
  change (middleFourModelCenter
    (fourActualSupportMultiplicity rowOrder).toList).val = 6
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  rw [middleFourModelCenter_val_eq_activePoints_length _ hLength,
    hLengthEq]

theorem sevenNineK4DualRowsValid_of_actual_image {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rows : List (G413.Row SevenNineK4Point))
    (pointMap : alpha → SevenNineK4Point)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hBlockerCard : (blocker H).card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hDegree : degree H x = 3)
    (hRowsImage : rows.toFinset =
      (blocker H).image fun row => row.image pointMap)
    (hPointMap : Set.InjOn pointMap ((blocker H).biUnion id))
    (hCenterMap : pointMap x = sevenNineK4Center)
    (hKernel : ∀ row ∈ sevenNineK4KernelRows,
      row ∈ H.image fun source => source.image pointMap) :
    sevenNineK4DualRowsValid (fastBlocker rows) = true := by
  have hDualImage : fastBlocker rows =
      H.image fun row => row.image pointMap := by
    calc
      fastBlocker rows = blocker rows.toFinset :=
        fastBlocker_eq_blocker rows
      _ = blocker ((blocker H).image fun row =>
          row.image pointMap) := congrArg blocker hRowsImage
      _ = (blocker (blocker H)).image fun row =>
          row.image pointMap :=
        blocker_image_eq_of_injOn_active hPointMap
      _ = H.image fun row => row.image pointMap := by
        rw [blocker_involution hHClutter]
  have hHDomain : H.biUnion id ⊆ (blocker H).biUnion id := by
    intro point hPoint
    obtain ⟨row, hRow, hPointRow⟩ := Finset.mem_biUnion.mp hPoint
    have hRowDouble : row ∈ blocker (blocker H) := by
      rw [blocker_involution hHClutter]
      exact hRow
    exact blocker_row_subset_biUnion hRowDouble hPointRow
  have hRowMap : Set.InjOn
      (fun row : G413.Row alpha => row.image pointMap) H :=
    row_image_injOn_of_injOn hHDomain hPointMap
  have hDualCard : (fastBlocker rows).card = 7 := by
    rw [hDualImage, Finset.card_image_iff.mpr hRowMap, hHCard]
  have hDualRows : ∀ row ∈ fastBlocker rows,
      3 ≤ row.card ∧ row.card ≤ 9 := by
    intro imageRow hImageRow
    rw [hDualImage] at hImageRow
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
    have hSourcePointMap : Set.InjOn pointMap source :=
      hPointMap.mono (fun point hPoint =>
        hHDomain (Finset.mem_biUnion.mpr
          ⟨source, hSource, hPoint⟩))
    have hImageCard : (source.image pointMap).card = source.card :=
      Finset.card_image_iff.mpr hSourcePointMap
    have hSourceDouble : source ∈ blocker (blocker H) := by
      rw [blocker_involution hHClutter]
      exact hSource
    rw [hImageCard]
    exact ⟨hHRows source hSource,
      (minimalTransversal_card_le_rows
        (mem_blocker.mp hSourceDouble)).trans_eq hBlockerCard⟩
  have hDualMaxDegree : ∀ modelPoint,
      degree (fastBlocker rows) modelPoint ≤ 3 := by
    intro modelPoint
    rw [hDualImage]
    by_cases hActive : modelPoint ∈
        (H.image fun row => row.image pointMap).biUnion id
    · obtain ⟨imageRow, hImageRow, hModelImage⟩ :=
        Finset.mem_biUnion.mp hActive
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hImageRow
      obtain ⟨point, hPointSource, hPointEq⟩ :=
        Finset.mem_image.mp hModelImage
      have hPointDomain : point ∈ (blocker H).biUnion id :=
        hHDomain (Finset.mem_biUnion.mpr
          ⟨source, hSource, hPointSource⟩)
      rw [← hPointEq,
        degree_image_eq_of_injOn hPointDomain hHDomain hPointMap]
      exact hHMaxDegree point
    · have hFilter : (H.image fun row =>
          row.image pointMap).filter
            (fun row => modelPoint ∈ row) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro row hRow
        apply hActive
        exact Finset.mem_biUnion.mpr
          ⟨row, (Finset.mem_filter.mp hRow).1,
            (Finset.mem_filter.mp hRow).2⟩
      simp [degree, hFilter]
  have hXInH : x ∈ H.biUnion id := by
    have hPositive : 0 < degree H x := by omega
    change 0 < (H.filter fun row => x ∈ row).card at hPositive
    obtain ⟨row, hRow⟩ := Finset.card_pos.mp hPositive
    exact Finset.mem_biUnion.mpr
      ⟨row, (Finset.mem_filter.mp hRow).1,
        (Finset.mem_filter.mp hRow).2⟩
  have hXDomain : x ∈ (blocker H).biUnion id := hHDomain hXInH
  have hCenterDegree :
      degree (fastBlocker rows) sevenNineK4Center = 3 := by
    rw [hDualImage, ← hCenterMap,
      degree_image_eq_of_injOn hXDomain hHDomain hPointMap,
      hDegree]
  apply sevenNineK4DualRowsValid_of
  · exact hDualCard
  · intro row hRow
    rw [hDualImage]
    exact hKernel row hRow
  · exact hDualRows
  · exact hDualMaxDegree
  · exact hCenterDegree

theorem sevenNineK4_actualDualRowsValid {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (first second : G413.Row alpha)
    (hFirstPrivate :
      (sevenNineK4FirstPrivateFresh H x first second).card ≤ 7)
    (hSecondPrivate :
      (sevenNineK4SecondPrivateFresh H x first second).card ≤ 7)
    (hShared :
      (sevenNineK4SharedFresh H x first second).card ≤ 7)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hBlockerCard : (blocker H).card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hDegree : degree H x = 3)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hBlocker : blocker H = insert first
      (insert second (middleFourSemanticLiftFamily H x))) :
    let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
      (fourActualSupportMultiplicity rowOrder).toList
      (middleFourSemanticSelected H x rowOrder))
    let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
    let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
    let privateFirst :=
      (sevenNineK4FirstPrivateFresh H x first second).card
    let privateSecond :=
      (sevenNineK4SecondPrivateFresh H x first second).card
    let shared := (sevenNineK4SharedFresh H x first second).card
    sevenNineK4DualRowsValid (fastBlocker
      (sevenNineK4TwoExtraRows base oldFirst oldSecond
        privateFirst privateSecond shared)) = true := by
  dsimp only
  let pointMap := sevenNineK4TwoExtraPoint H x rowOrder first second
    hFirstPrivate hSecondPrivate hShared
  let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder))
  let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
  let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
  let privateFirst :=
    (sevenNineK4FirstPrivateFresh H x first second).card
  let privateSecond :=
    (sevenNineK4SecondPrivateFresh H x first second).card
  let shared := (sevenNineK4SharedFresh H x first second).card
  let rows := sevenNineK4TwoExtraRows base oldFirst oldSecond
    privateFirst privateSecond shared
  have hRowsImage : rows.toFinset =
      (blocker H).image fun row => row.image pointMap := by
    simpa [rows, base, oldFirst, oldSecond, privateFirst,
      privateSecond, shared, pointMap] using sevenNineK4_candidateSet_image
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHBlockerRows hAvoidBlockerRows hBlocker
  have hPointMap : Set.InjOn pointMap ((blocker H).biUnion id) := by
    simpa [pointMap] using sevenNineK4TwoExtraPoint_injOn_blocker
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hBlocker
  have hCenterMap : pointMap x = sevenNineK4Center := by
    simpa [pointMap] using sevenNineK4TwoExtraPoint_center
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues
  have hKernelImage : sevenNineK4KernelRows.toFinset =
      (avoidPoint H x).image fun row => row.image pointMap := by
    simpa [pointMap] using sevenNineK4_semanticKernel_image
      H x rowOrder first second hFirstPrivate hSecondPrivate hShared
        hValues hAvoidBlockerRows
  have hKernel : ∀ row ∈ sevenNineK4KernelRows,
      row ∈ H.image fun source => source.image pointMap := by
    intro row hRow
    have hKernelMember : row ∈
        (avoidPoint H x).image fun source => source.image pointMap := by
      rw [← hKernelImage]
      exact List.mem_toFinset.mpr hRow
    obtain ⟨source, hSource, hSourceImage⟩ :=
      Finset.mem_image.mp hKernelMember
    exact Finset.mem_image.mpr
      ⟨source, (mem_avoidPoint.mp hSource).1, hSourceImage⟩
  simpa [rows] using sevenNineK4DualRowsValid_of_actual_image
    H x rows pointMap hHClutter hHCard hBlockerCard hHRows
      hHMaxDegree hDegree hRowsImage hPointMap hCenterMap hKernel

theorem sevenNineK4_contradicts_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    (H : G413.Hypergraph alpha) (x : alpha)
    (rowOrder : Fin 4 ≃ avoidPoint H x)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBlockerCard : (blocker H).card = 9)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBlockerMaxDegree : MaxDegreeAtMost (blocker H) 4)
    (hDegree : degree H x = 3)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 7)
    (hAvoidBlockerRows :
      RowsCardAtLeast (blocker (avoidPoint H x)) 2)
    (hValues : (fourActualSupportMultiplicity rowOrder).toList =
      middleFourDegreeFourVector20)
    (hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList)
    (hCheck : sevenNineK4ExtensionCheck = true) : False := by
  obtain ⟨first, second, hNe, hFirstBlocker, hSecondBlocker,
      hFirstNotLifted, hSecondNotLifted, hBlocker, hKey⟩ :=
    liftFamily_exists_ordered_two_extras H x rowOrder
      hAvoidBlockerCard hBlockerCard
  have hFirstUpper : first.card ≤ 7 :=
    (minimalTransversal_card_le_rows
      (mem_blocker.mp hFirstBlocker)).trans_eq hHCard
  have hSecondUpper : second.card ≤ 7 :=
    (minimalTransversal_card_le_rows
      (mem_blocker.mp hSecondBlocker)).trans_eq hHCard
  have hFirstPrivate :=
    (sevenNineK4_firstPrivate_card_le H x first second).trans
      hFirstUpper
  have hSecondPrivate :=
    (sevenNineK4_secondPrivate_card_le H x first second).trans
      hSecondUpper
  have hShared :=
    (sevenNineK4_shared_card_le_first H x first second).trans
      hFirstUpper
  let base := sevenNineK4WidenRows (middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder))
  let oldFirst := sevenNineK4ActualOldModel H x rowOrder first
  let oldSecond := sevenNineK4ActualOldModel H x rowOrder second
  let privateFirst :=
    (sevenNineK4FirstPrivateFresh H x first second).card
  let privateSecond :=
    (sevenNineK4SecondPrivateFresh H x first second).card
  let shared := (sevenNineK4SharedFresh H x first second).card
  let rows := sevenNineK4TwoExtraRows base oldFirst oldSecond
    privateFirst privateSecond shared
  have hBase : base ∈ sevenNineK4Bases := by
    simpa [base] using sevenNineK4_semanticBase_mem_bases
      H x rowOrder hValues hSelection
  have hAdmissible : sevenNineK4OldPairAdmissible base
      oldFirst oldSecond = true := by
    simpa [base, oldFirst, oldSecond] using
      sevenNineK4_actualOldPair_admissible
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHBlockerRows hAvoidBlockerRows hFirstBlocker
            hSecondBlocker hFirstNotLifted hSecondNotLifted hNe hBlocker
              hBlockerMaxDegree
  have hOldPair : (oldFirst, oldSecond) ∈
      sevenNineK4OldPairs base := by
    simpa [oldFirst, oldSecond] using
      sevenNineK4_actualOldModels_mem_oldPairs
        H x rowOrder first second base hValues hAdmissible
  have hStructure : sevenNineK4CandidateStructure base
      oldFirst oldSecond privateFirst privateSecond shared = true := by
    simpa [base, oldFirst, oldSecond, privateFirst, privateSecond,
      shared] using sevenNineK4_actualCandidateStructure
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHCard hBlockerCard hHBlockerRows hAvoidBlockerRows
            hFirstBlocker hSecondBlocker hBlocker hKey
  have hOldPairCheck : sevenNineK4OldPairCheck base
      (oldFirst, oldSecond) = true :=
    sevenNineK4OldPairCheck_of_extensionCheck
      base (oldFirst, oldSecond) hCheck hBase hOldPair
  have hInvalid : sevenNineK4DualRowsValid (fastBlocker rows) = false := by
    simpa [rows, sevenNineK4TwoExtraRows] using
      sevenNineK4DualRows_invalid_of_oldPairCheck
        base oldFirst oldSecond privateFirst privateSecond shared
          hOldPairCheck (by omega) (by omega) (by omega) hStructure
  have hValid : sevenNineK4DualRowsValid (fastBlocker rows) = true := by
    simpa [rows, base, oldFirst, oldSecond, privateFirst,
      privateSecond, shared] using sevenNineK4_actualDualRowsValid
        H x rowOrder first second hFirstPrivate hSecondPrivate hShared
          hValues hHClutter hHCard hBlockerCard hHRows hHMaxDegree
            hDegree hHBlockerRows hAvoidBlockerRows hBlocker
  simpa [hValid] using hInvalid

end AiMathLab.P0054.MiddleSevenNineK4Sound
