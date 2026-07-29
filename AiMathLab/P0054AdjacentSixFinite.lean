import AiMathLab.P0054G417.SupportMultigraphLift

/-!
# The finite low-degree kernel for the adjacent six-row bound

The existing `G417` certificate lists all 562 minimal covers of the six-vertex
loop multigraph.  Here every low vertex has degree exactly two (rather than
three), every other vertex has degree at least three, and a positive support
must touch a low vertex.  The additional predicate excludes a positive
three-support cover.  A small pruned kernel check then proves that the weighted
number of minimal support covers is at least six.
-/

namespace AiMathLab.P0054.AdjacentSixFinite

open AiMathLab.P0054.G417

def AdjacentSixMultiplicityValid (lowCount : Nat) (m : SixMultiplicity) : Prop :=
  (∀ v : SixVertex, if v.val < lowCount then sixSupportDegree m v = 2
    else 3 ≤ sixSupportDegree m v) ∧
  ∀ s : SixSupportIndex, 0 < sixMultiplicityDigit m s.val →
    sixSupportTouchesLow lowCount s

instance (lowCount : Nat) (m : SixMultiplicity) :
    Decidable (AdjacentSixMultiplicityValid lowCount m) := by
  unfold AdjacentSixMultiplicityValid
  infer_instance

def AdjacentSixNoThreeCover (m : SixMultiplicity) : Prop :=
  ∀ C ∈ sixMinimalSupportCovers, C.length = 3 →
    ∃ s ∈ C, sixMultiplicityDigit m s.val = 0

instance (m : SixMultiplicity) : Decidable (AdjacentSixNoThreeCover m) := by
  unfold AdjacentSixNoThreeCover
  infer_instance

def adjacentSixDegreeStateValidBool
    (lowCount : Nat) (degrees : SixDegreeState) : Bool :=
  (List.range 6).all fun v ↦
    if v < lowCount then decide (degrees.getD v 0 = 2)
    else decide (3 ≤ degrees.getD v 0)

def adjacentSixMultiplicityChoices
    (lowCount : Nat) (degrees : SixDegreeState) (s : Nat) : List Nat :=
  (List.range 3).filter fun k ↦
    (decide (k = 0) || sixSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !sixSupportContains s v || decide (degrees.getD v 0 + k ≤ 2)

def adjacentSixCheckAux
    (lowCount minimum : Nat) : List Nat → SixMultiplicity → SixDegreeState → Bool
  | [], m, degrees =>
      if adjacentSixDegreeStateValidBool lowCount degrees then
        if decide (AdjacentSixNoThreeCover m) then
          decide (minimum ≤ sixWeightedCoverCount m)
        else true
      else true
  | s :: supports, m, degrees =>
      (adjacentSixMultiplicityChoices lowCount degrees s).all fun k ↦
        adjacentSixCheckAux lowCount minimum supports (m.set! s k)
          (addSixSupportDegree degrees s k)

def adjacentSixSubcheck (lowCount a b c d : Nat) : Bool :=
  adjacentSixCheckAux lowCount 6 ((List.range 21).drop 4)
    (sixMultiplicityAfterFour a b c d) (sixDegreeStateAfterFour a b c d)

def adjacentSixCheckA (lowCount a : Nat) : Bool :=
  (List.range 3).all fun b ↦
    (List.range 3).all fun c ↦
      (List.range 3).all fun d ↦ adjacentSixSubcheck lowCount a b c d

def adjacentSixCheck (lowCount : Nat) : Bool :=
  (List.range 3).all fun a ↦ adjacentSixCheckA lowCount a

def adjacentSixCompactMultiplicityDigit (m s : Nat) : Nat :=
  m / 3 ^ s % 3

def adjacentSixCompactDegreeDigit (degrees v : Nat) : Nat :=
  degrees / 32 ^ v % 32

def adjacentSixCompactSupportWeight (s : Nat) : Nat :=
  (List.range 6).foldl (fun weight v ↦
    if sixSupportContains s v then weight + 32 ^ v else weight) 0

def adjacentSixCompactAddDegree (degrees s k : Nat) : Nat :=
  degrees + k * adjacentSixCompactSupportWeight s

def adjacentSixCompactWeightedCoverCount (m : Nat) : Nat :=
  (sixMinimalSupportCovers.map fun C ↦
    (C.map fun s ↦ adjacentSixCompactMultiplicityDigit m s.val).prod).sum

def adjacentSixCompactCoverWeight (m : Nat) (C : List SixSupportIndex) : Nat :=
  (C.map fun s ↦ adjacentSixCompactMultiplicityDigit m s.val).prod

def adjacentSixCompactWeightedCoverAtLeastAux
    (minimum m : Nat) : Nat → List (List SixSupportIndex) → Bool
  | total, [] => decide (minimum ≤ total)
  | total, C :: covers =>
      if decide (minimum ≤ total) then true
      else adjacentSixCompactWeightedCoverAtLeastAux minimum m
        (total + adjacentSixCompactCoverWeight m C) covers

def adjacentSixCompactWeightedCoverAtLeast (minimum m : Nat) : Bool :=
  adjacentSixCompactWeightedCoverAtLeastAux minimum m 0 sixMinimalSupportCovers

def AdjacentSixCompactNoThreeCover (m : Nat) : Prop :=
  ∀ C ∈ sixMinimalSupportCovers, C.length = 3 →
    ∃ s ∈ C, adjacentSixCompactMultiplicityDigit m s.val = 0

instance (m : Nat) : Decidable (AdjacentSixCompactNoThreeCover m) := by
  unfold AdjacentSixCompactNoThreeCover
  infer_instance

def adjacentSixCompactDegreeValidBool (lowCount degrees : Nat) : Bool :=
  (List.range 6).all fun v ↦
    if v < lowCount then decide (adjacentSixCompactDegreeDigit degrees v = 2)
    else decide (3 ≤ adjacentSixCompactDegreeDigit degrees v)

def adjacentSixCompactChoices (lowCount degrees s : Nat) : List Nat :=
  (List.range 3).filter fun k ↦
    (decide (k = 0) || sixSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !sixSupportContains s v ||
          decide (adjacentSixCompactDegreeDigit degrees v + k ≤ 2)

def adjacentSixCompactSupportOrder : List Nat :=
  [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 4, 20, 5]

def adjacentSixCompactSealedValidBool
    (lowCount degrees : Nat) (supports : List Nat) : Bool :=
  (List.range lowCount).all fun v ↦
    if supports.any (fun s ↦ sixSupportContains s v) then true
    else decide (adjacentSixCompactDegreeDigit degrees v = 2)

def adjacentSixCompactNoThreePossibleBool
    (lowCount m : Nat) (supports : List Nat) : Bool :=
  if lowCount < 5 || 8 < supports.length then true
  else
    (sixMinimalSupportCovers.take 15).all fun C ↦
      C.any (fun s ↦ supports.contains s.val) ||
        C.any (fun s ↦ decide (adjacentSixCompactMultiplicityDigit m s.val = 0))

def adjacentSixCompactCheckAux
    (lowCount minimum : Nat) : List Nat → Nat → Nat → Bool
  | [], m, degrees =>
      if adjacentSixCompactDegreeValidBool lowCount degrees then
        if decide (AdjacentSixCompactNoThreeCover m) then
          adjacentSixCompactWeightedCoverAtLeast minimum m
        else true
      else true
  | s :: supports, m, degrees =>
      if adjacentSixCompactSealedValidBool lowCount degrees (s :: supports) &&
          adjacentSixCompactNoThreePossibleBool lowCount m (s :: supports) then
        (adjacentSixCompactChoices lowCount degrees s).all fun k ↦
          adjacentSixCompactCheckAux lowCount minimum supports (m + k * 3 ^ s)
            (adjacentSixCompactAddDegree degrees s k)
      else true

def adjacentSixCompactSubcheck (lowCount a b c d : Nat) : Bool :=
  adjacentSixCompactCheckAux lowCount 6 adjacentSixCompactSupportOrder
    (a + 3 * b + 9 * c + 27 * d)
    (a + 32 * b + 32 ^ 2 * c + 32 ^ 3 * d)

def adjacentSixCompactCheckAB (lowCount a b : Nat) : Bool :=
  (List.range 3).all fun c ↦
    (List.range 3).all fun d ↦ adjacentSixCompactSubcheck lowCount a b c d

def adjacentSixCompactCheckA (lowCount a : Nat) : Bool :=
  (List.range 3).all fun b ↦ adjacentSixCompactCheckAB lowCount a b

def adjacentSixCompactCheck (lowCount : Nat) : Bool :=
  (List.range 3).all fun a ↦ adjacentSixCompactCheckA lowCount a

inductive AdjacentSixGenerated (lowCount : Nat) :
    List Nat → SixMultiplicity → SixDegreeState →
      SixMultiplicity → SixDegreeState → Prop
  | nil (m degrees) : AdjacentSixGenerated lowCount [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : SixMultiplicity}
      {degrees finalDegrees : SixDegreeState} {k : Nat}
      (hChoice : k ∈ adjacentSixMultiplicityChoices lowCount degrees s)
      (hGenerated : AdjacentSixGenerated lowCount supports (m.set! s k)
        (addSixSupportDegree degrees s k) finalM finalDegrees) :
      AdjacentSixGenerated lowCount (s :: supports) m degrees finalM finalDegrees

theorem AdjacentSixGenerated.append {lowCount : Nat}
    {left right : List Nat}
    {m middleM finalM : SixMultiplicity}
    {degrees middleDegrees finalDegrees : SixDegreeState}
    (hLeft : AdjacentSixGenerated lowCount left m degrees middleM middleDegrees)
    (hRight : AdjacentSixGenerated lowCount right middleM middleDegrees finalM finalDegrees) :
    AdjacentSixGenerated lowCount (left ++ right) m degrees finalM finalDegrees := by
  induction hLeft with
  | nil => simpa using hRight
  | cons hChoice hGenerated ih =>
      exact AdjacentSixGenerated.cons hChoice (ih hRight)

theorem adjacentSixCheckAux_sound
    {lowCount minimum : Nat} {supports : List Nat}
    {m finalM : SixMultiplicity} {degrees finalDegrees : SixDegreeState}
    (hGenerated : AdjacentSixGenerated lowCount supports m degrees finalM finalDegrees)
    (hCheck : adjacentSixCheckAux lowCount minimum supports m degrees = true)
    (hValid : adjacentSixDegreeStateValidBool lowCount finalDegrees = true)
    (hNoThree : AdjacentSixNoThreeCover finalM) :
    minimum ≤ sixWeightedCoverCount finalM := by
  induction hGenerated with
  | nil =>
      simpa [adjacentSixCheckAux, hValid, hNoThree, decide_eq_true_eq] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll :
          (adjacentSixMultiplicityChoices lowCount degrees s).all (fun choice ↦
            adjacentSixCheckAux lowCount minimum supports
              (m.set! s choice) (addSixSupportDegree degrees s choice)) = true := by
        simpa [adjacentSixCheckAux] using hCheck
      have hBranch :
          adjacentSixCheckAux lowCount minimum supports
            (m.set! s k) (addSixSupportDegree degrees s k) = true :=
        (List.all_eq_true.mp hAll) k hChoice
      exact ih hBranch hValid hNoThree

end AiMathLab.P0054.AdjacentSixFinite
