import AiMathLab.P0054G420.FourKernelPair

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G413 G419 G420

def middleFourMultiplicityCertificate : List (List Nat) :=
  [
    [1, 1, 0, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0],
    [1, 1, 0, 1, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0],
    [1, 1, 0, 1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0],
    [0, 0, 1, 1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0],
    [1, 0, 0, 0, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0],
    [1, 1, 0, 1, 1, 0, 1, 2, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 1, 1, 0, 1, 2, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 1, 1, 1, 2, 0, 1, 0, 0, 0, 0],
    [0, 1, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0],
    [0, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0],
    [1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0],
    [0, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0],
    [1, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 1, 0, 0, 2, 1, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0, 0, 0],
    [0, 0, 0, 1, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 0, 1, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 1, 0, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    [0, 0, 1, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0],
    [0, 1, 0, 2, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 0, 0, 2, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0],
    [0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0, 0],
    [1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0],
    [1, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0],
    [0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0],
    [1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0],
    [0, 1, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0],
    [1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0],
    [0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0],
    [1, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0],
    [0, 1, 1, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 0, 2, 0, 0],
    [0, 0, 2, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0],
    [0, 0, 2, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0, 1, 0, 1, 2, 0, 0, 2, 0, 0],
    [0, 1, 2, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0],
    [0, 0, 2, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0],
    [0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0],
    [1, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [1, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0],
    [0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [0, 0, 2, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [1, 0, 1, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [0, 1, 2, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0],
    [0, 0, 2, 0, 1, 1, 0, 0, 0, 2, 0, 1, 0, 0],
    [0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 0],
    [1, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    [0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    [0, 0, 2, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0],
    [1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 0, 2, 0, 0],
    [0, 0, 2, 0, 2, 0, 0, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0],
    [0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 1, 0, 0],
    [0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0],
    [0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0],
    [0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    [0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    [1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    [1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0],
    [1, 2, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 2, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0],
    [1, 2, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0],
    [0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0],
    [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0],
    [0, 2, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0],
    [0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0],
    [1, 2, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0],
    [0, 2, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0],
    [1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0],
    [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    [1, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    [1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0],
    [2, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1],
    [2, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1],
    [2, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    [1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    [0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    [2, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1],
    [2, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    [2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    [2, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1],
    [2, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1],
    [2, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
  ]

def middleFourMultiplicityInCertificate (m : FourMultiplicity) : Bool :=
  middleFourMultiplicityCertificate.any fun values ↦ decide (m.toList = values)

def middleFourMaskPairCoverCount (mask : Nat) : Nat :=
  ((fourMinimalSupportCoverMasks.take 25).filter fun coverMask ↦
    decide (Nat.land mask coverMask = coverMask)).length

def middleFourMultiplicityLeafValid (m : FourMultiplicity) : Bool :=
  ((List.range 4).map (fourRowDegree m)).all fun degree ↦
    decide (3 ≤ degree ∧ degree ≤ 9)

def middleFourMaskValid (mask : Nat) : Bool :=
  let supportDegrees := (List.range 4).map (fourMaskSupportDegree mask)
  decide (mask ≠ 0) &&
    supportDegrees.all (fun degree ↦ decide (0 < degree ∧ degree ≤ 9)) &&
      fourMaskRowsClutter mask &&
        decide (0 < fourMaskCoverCount mask ∧ fourMaskCoverCount mask ≤ 9) &&
          decide (middleFourMaskPairCoverCount mask ≤ 4) &&
            decide (fourMaskCoveredUnion mask = mask)

def middleFourMultiplicityChoices
    (m : FourMultiplicity) (degrees : FourDegreeState) (s : Nat) : List Nat :=
  ((List.range 9).map (· + 1)).filter fun k ↦
    ((List.range 4).all fun row ↦
      !fourSupportContains s row || decide (degrees.getD row 0 + k ≤ 9)) &&
      decide (fourWeightedCoverCount (m.set! s k) ≤ 9) &&
        decide (fourPairCoverCount (m.set! s k) ≤ 4)

def middleFourClassificationAux :
    List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], m, _ =>
      !middleFourMultiplicityLeafValid m || middleFourMultiplicityInCertificate m
  | s :: supports, m, degrees =>
      (middleFourMultiplicityChoices m degrees s).all fun k ↦
        middleFourClassificationAux supports (m.set! s k)
          (addFourSupportDegree degrees s k)

def middleFourClassificationMaskCheck (mask : Nat) : Bool :=
  !middleFourMaskValid mask ||
    middleFourClassificationAux (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero

def middleFourClassificationValuesCheckAux :
    List Nat → List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], supports, m, degrees => middleFourClassificationAux supports m degrees
  | _, [], _, _ => true
  | k :: values, s :: supports, m, degrees =>
      if k ∈ middleFourMultiplicityChoices m degrees s then
        middleFourClassificationValuesCheckAux values supports (m.set! s k)
          (addFourSupportDegree degrees s k)
      else true

def middleFourClassificationValuesCheck
    (mask : Nat) (values : List Nat) : Bool :=
  middleFourClassificationValuesCheckAux values (fourMaskSupports mask)
    (fourMultiplicityForMask mask) fourDegreeStateZero

def middleFourTwoPrefixAdmissible (mask k l : Nat) : Bool :=
  match fourMaskSupports mask with
  | s :: t :: _ =>
      decide (k ∈ middleFourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s) &&
      decide (l ∈ middleFourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t)
  | _ => false

theorem middleFourClassificationMaskCheck_of_list
    {masks : List Nat}
    (hCheck : masks.all middleFourClassificationMaskCheck = true)
    {mask : Nat} (hMask : mask ∈ masks) :
    middleFourClassificationMaskCheck mask = true :=
  List.all_eq_true.mp hCheck mask hMask

theorem middleFourClassificationValuesCheck_of_list
    {mask : Nat} {valuesList : List (List Nat)}
    (hCheck : valuesList.all (middleFourClassificationValuesCheck mask) = true)
    {values : List Nat} (hValues : values ∈ valuesList) :
    middleFourClassificationValuesCheck mask values = true :=
  List.all_eq_true.mp hCheck values hValues

theorem middleFourClassificationMaskCheck_of_two_prefixes
    (mask s t : Nat) (supports : List Nat)
    (hSupports : fourMaskSupports mask = s :: t :: supports)
    (hValid : middleFourMaskValid mask = true)
    (hPrefixes : ∀ k ∈ middleFourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s,
      ∀ l ∈ middleFourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t,
        middleFourClassificationValuesCheck mask [k, l] = true) :
    middleFourClassificationMaskCheck mask = true := by
  simp only [middleFourClassificationMaskCheck, hValid,
    Bool.not_true, Bool.false_or]
  rw [hSupports]
  simp only [middleFourClassificationAux, List.all_eq_true]
  intro k hk l hl
  have hPrefix := hPrefixes k hk l hl
  unfold middleFourClassificationValuesCheck at hPrefix
  rw [hSupports] at hPrefix
  simp only [middleFourClassificationValuesCheckAux] at hPrefix
  rw [if_pos hk, if_pos hl] at hPrefix
  exact hPrefix

inductive MiddleFourGenerated :
    List Nat → FourMultiplicity → FourDegreeState →
      FourMultiplicity → FourDegreeState → Prop
  | nil (m degrees) : MiddleFourGenerated [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : FourMultiplicity}
      {degrees finalDegrees : FourDegreeState} {k : Nat}
      (hChoice : k ∈ middleFourMultiplicityChoices m degrees s)
      (hGenerated : MiddleFourGenerated supports (m.set! s k)
        (addFourSupportDegree degrees s k) finalM finalDegrees) :
      MiddleFourGenerated (s :: supports) m degrees finalM finalDegrees

theorem middleFourClassificationAux_sound
    {supports : List Nat} {m finalM : FourMultiplicity}
    {degrees finalDegrees : FourDegreeState}
    (hGenerated : MiddleFourGenerated supports m degrees finalM finalDegrees)
    (hCheck : middleFourClassificationAux supports m degrees = true)
    (hLeaf : middleFourMultiplicityLeafValid finalM = true) :
    middleFourMultiplicityInCertificate finalM = true := by
  induction hGenerated with
  | nil => simpa [middleFourClassificationAux, hLeaf] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll :
          (middleFourMultiplicityChoices m degrees s).all (fun choice ↦
            middleFourClassificationAux supports (m.set! s choice)
              (addFourSupportDegree degrees s choice)) = true := by
        simpa [middleFourClassificationAux] using hCheck
      exact ih (List.all_eq_true.mp hAll k hChoice) hLeaf

theorem middleFourClassificationMaskCheck_sound
    {mask : Nat} {m : FourMultiplicity} {degrees : FourDegreeState}
    (hMask : middleFourMaskValid mask = true)
    (hGenerated : MiddleFourGenerated (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero m degrees)
    (hLeaf : middleFourMultiplicityLeafValid m = true)
    (hCheck : middleFourClassificationMaskCheck mask = true) :
    middleFourMultiplicityInCertificate m = true := by
  apply middleFourClassificationAux_sound hGenerated (hLeaf := hLeaf)
  simpa [middleFourClassificationMaskCheck, hMask] using hCheck

theorem fourPairCoverCount_mono
    {left right : FourMultiplicity}
    (hDigits : ∀ s < 14,
      fourMultiplicityDigit left s ≤ fourMultiplicityDigit right s) :
    fourPairCoverCount left ≤ fourPairCoverCount right := by
  rw [← four_pair_cover_count_eq_index_covers,
    ← four_pair_cover_count_eq_index_covers]
  induction fourMinimalSupportIndexCovers.take 25 with
  | nil => simp
  | cons cover covers ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · simpa only [List.map_map, Function.comp_def] using
          fourProductDigits_mono (left := left) (right := right)
            (cover.map fun s ↦ s.val) (by
              intro s hs
              obtain ⟨index, hIndex, rfl⟩ := List.mem_map.mp hs
              exact index.isLt) hDigits
      · exact ih

theorem middleFourGenerated_suffix
    (actual current : FourMultiplicity) (remaining : List Nat)
    (degrees : FourDegreeState)
    (hActualSize : actual.size = 14)
    (hCurrentSize : current.size = 14)
    (hRemainingRange : ∀ s ∈ remaining, s < 14)
    (hRemainingPositive : ∀ s ∈ remaining,
      0 < fourMultiplicityDigit actual s)
    (hCurrentLe : ∀ s < 14,
      fourMultiplicityDigit current s ≤ fourMultiplicityDigit actual s)
    (hCurrentDone : ∀ s < 14, s ∉ remaining →
      fourMultiplicityDigit current s = fourMultiplicityDigit actual s)
    (hDegreeInvariant : ∀ row < 4,
      degrees.getD row 0 + fourRemainingRowDegree actual remaining row =
        fourRowDegree actual row)
    (hRowUpper : ∀ row < 4, fourRowDegree actual row ≤ 9)
    (hWeighted : fourWeightedCoverCount actual ≤ 9)
    (hPair : fourPairCoverCount actual ≤ 4) :
    ∃ finalDegrees,
      MiddleFourGenerated remaining current degrees actual finalDegrees := by
  induction remaining generalizing current degrees with
  | nil =>
      have hCurrent : current = actual := by
        apply Array.ext
        · omega
        · intro i hiCurrent hiActual
          have hi : i < 14 := by omega
          have hDigit := hCurrentDone i hi (by simp)
          simpa [fourMultiplicityDigit, hCurrentSize, hActualSize, hi] using hDigit
      subst current
      exact ⟨degrees, MiddleFourGenerated.nil _ _⟩
  | cons s remaining ih =>
      let k := fourMultiplicityDigit actual s
      have hsRange : s < 14 := hRemainingRange s (by simp)
      have hkPositive : 0 < k := hRemainingPositive s (by simp)
      have hkUpper : k ≤ 9 := by
        obtain ⟨row, hrow, hContains⟩ := exists_fourSupportContains hsRange
        exact (fourMultiplicityDigit_le_rowDegree actual hsRange hContains).trans
          (hRowUpper row hrow)
      have hkRange : k ∈ (List.range 9).map (· + 1) := by
        apply List.mem_map.mpr
        exact ⟨k - 1, List.mem_range.mpr (by omega), by omega⟩
      have hDegreeCaps :
          ((List.range 4).all fun row ↦
            !fourSupportContains s row ||
              decide (degrees.getD row 0 + k ≤ 9)) = true := by
        rw [List.all_eq_true]
        intro row hrow
        have hrowLt := List.mem_range.mp hrow
        by_cases hContains : fourSupportContains s row = true
        · have hInvariant := hDegreeInvariant row hrowLt
          rw [fourRemainingRowDegree_cons, hContains] at hInvariant
          simp only [if_true] at hInvariant
          exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by
            have hUpper := hRowUpper row hrowLt
            omega)))
        · exact Bool.or_eq_true_iff.mpr (Or.inl (by
            simp [Bool.eq_false_of_not_eq_true hContains]))
      let next := current.set! s k
      have hNextSize : next.size = 14 := by simp [next, hCurrentSize]
      have hNextLe : ∀ t < 14,
          fourMultiplicityDigit next t ≤ fourMultiplicityDigit actual t := by
        intro t ht
        rw [fourMultiplicityDigit_set! current hCurrentSize hsRange ht]
        by_cases hts : t = s
        · simp [hts, k]
        · simp [hts, hCurrentLe t ht]
      have hNextWeighted : fourWeightedCoverCount next ≤ 9 :=
        (fourWeightedCoverCount_mono hNextLe).trans hWeighted
      have hNextPair : fourPairCoverCount next ≤ 4 :=
        (fourPairCoverCount_mono hNextLe).trans hPair
      have hChoice : k ∈ middleFourMultiplicityChoices current degrees s := by
        apply List.mem_filter.mpr
        refine ⟨hkRange, Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hNextPair⟩⟩
        exact Bool.and_eq_true_iff.mpr
          ⟨hDegreeCaps, decide_eq_true hNextWeighted⟩
      have hTailRange : ∀ t ∈ remaining, t < 14 := by
        intro t ht
        exact hRemainingRange t (by simp [ht])
      have hTailPositive : ∀ t ∈ remaining,
          0 < fourMultiplicityDigit actual t := by
        intro t ht
        exact hRemainingPositive t (by simp [ht])
      have hNextDone : ∀ t < 14, t ∉ remaining →
          fourMultiplicityDigit next t = fourMultiplicityDigit actual t := by
        intro t ht hNotTail
        rw [fourMultiplicityDigit_set! current hCurrentSize hsRange ht]
        by_cases hts : t = s
        · simp [hts, k]
        · simp only [if_neg hts]
          exact hCurrentDone t ht (by simp [hts, hNotTail])
      have hNextDegreeInvariant : ∀ row < 4,
          (addFourSupportDegree degrees s k).getD row 0 +
              fourRemainingRowDegree actual remaining row =
            fourRowDegree actual row := by
        intro row hrow
        rw [addFourSupportDegree_getD degrees s k hrow]
        have hInvariant := hDegreeInvariant row hrow
        rw [fourRemainingRowDegree_cons] at hInvariant
        simpa [k, Nat.add_assoc] using hInvariant
      obtain ⟨finalDegrees, hGenerated⟩ := ih next
        (addFourSupportDegree degrees s k) hNextSize hTailRange hTailPositive
        hNextLe hNextDone hNextDegreeInvariant
      exact ⟨finalDegrees, MiddleFourGenerated.cons hChoice hGenerated⟩

theorem middleFourGenerated_multiplicityMask
    (m : FourMultiplicity) (hSize : m.size = 14)
    (hRowUpper : ∀ row < 4, fourRowDegree m row ≤ 9)
    (hWeighted : fourWeightedCoverCount m ≤ 9)
    (hPair : fourPairCoverCount m ≤ 4) :
    ∃ finalDegrees,
      MiddleFourGenerated (fourMaskSupports (fourMultiplicityMask m))
        (fourMultiplicityForMask (fourMultiplicityMask m))
        fourDegreeStateZero m finalDegrees := by
  apply middleFourGenerated_suffix m
  · exact hSize
  · simp [fourMultiplicityForMask]
  · intro s hs
    exact List.mem_range.mp (List.mem_of_mem_filter hs)
  · intro s hs
    rw [fourMaskSupports_multiplicityMask] at hs
    exact of_decide_eq_true (List.mem_filter.mp hs).2
  · intro s hs
    rw [fourMultiplicityForMask_multiplicityMask_digit m hs]
    split <;> omega
  · intro s hs hNotSupport
    have hsZero : fourMultiplicityDigit m s = 0 := by
      by_contra hsNonzero
      apply hNotSupport
      rw [fourMaskSupports_multiplicityMask]
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr hs, decide_eq_true (Nat.pos_of_ne_zero hsNonzero)⟩
    rw [fourMultiplicityForMask_multiplicityMask_digit m hs]
    simp [hsZero]
  · intro row hrow
    rw [fourRemainingRowDegree_maskSupports]
    simp [fourDegreeStateZero, hrow]
  · exact hRowUpper
  · exact hWeighted
  · exact hPair

def middleFourPositivePairCovers (m : FourMultiplicity) : List (List Nat) :=
  (fourMinimalSupportCovers.take 25).filter fun cover ↦
    cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)

theorem middleFourMaskPairCoverCount_multiplicityMask (m : FourMultiplicity) :
    middleFourMaskPairCoverCount (fourMultiplicityMask m) =
      (middleFourPositivePairCovers m).length := by
  unfold middleFourMaskPairCoverCount middleFourPositivePairCovers
  have hMasks := congrArg (List.take 25) four_minimal_support_cover_masks_eq
  rw [hMasks]
  rw [← List.map_take]
  let left : Nat → Bool := fun coverMask ↦
    decide (Nat.land (fourMultiplicityMask m) coverMask = coverMask)
  let right : List Nat → Bool := fun cover ↦
    cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)
  have hPredicate : ∀ cover ∈ fourMinimalSupportCovers.take 25,
      left (fourSupportListMask cover) = right cover := by
    intro cover hCover
    apply Bool.eq_iff_iff.mpr
    unfold left right
    rw [decide_eq_true_eq]
    have hCoverAll := List.mem_of_mem_take hCover
    rw [fourSupportListMask_subset_iff _
      (four_minimal_support_covers_sorted cover hCoverAll)]
    rw [List.all_eq_true]
    constructor
    · intro hAll s hs
      exact decide_eq_true ((fourMultiplicityMask_testBit_true_iff m
        (four_minimal_support_covers_range cover hCoverAll s hs)).mp (hAll s hs))
    · intro hAll s hs
      exact (fourMultiplicityMask_testBit_true_iff m
        (four_minimal_support_covers_range cover hCoverAll s hs)).mpr
          (of_decide_eq_true (hAll s hs))
  rw [filter_map_eq_map_filter_of_predicate
    (fourMinimalSupportCovers.take 25) fourSupportListMask left right hPredicate]
  simp [right]

theorem four_pair_cover_count_eq_support_covers (m : FourMultiplicity) :
    ((fourMinimalSupportCovers.take 25).map fun cover ↦
      (cover.map (fourMultiplicityDigit m)).prod).sum = fourPairCoverCount m := by
  rw [← four_minimal_support_pair_covers_values]
  simpa only [List.map_map, Function.comp_def] using
    four_pair_cover_count_eq_index_covers m

theorem middleFourMaskPairCoverCount_le_pairCoverCount (m : FourMultiplicity) :
    middleFourMaskPairCoverCount (fourMultiplicityMask m) ≤
      fourPairCoverCount m := by
  rw [middleFourMaskPairCoverCount_multiplicityMask,
    ← four_pair_cover_count_eq_support_covers]
  exact length_filter_all_positive_le_sum_products
    (fourMinimalSupportCovers.take 25) m

theorem middleFourMaskValid_multiplicityMask
    (m : FourMultiplicity)
    (hLeaf : middleFourMultiplicityLeafValid m = true)
    (hClutter : fourRowsClutter m = true)
    (hCovered : fourActiveSupportsCovered m = true)
    (hWeighted : fourWeightedCoverCount m ≤ 9)
    (hPair : fourPairCoverCount m ≤ 4) :
    middleFourMaskValid (fourMultiplicityMask m) = true := by
  unfold middleFourMultiplicityLeafValid at hLeaf
  have hRowBounds : ∀ row < 4,
      3 ≤ fourRowDegree m row ∧ fourRowDegree m row ≤ 9 := by
    intro row hrow
    exact of_decide_eq_true (List.all_eq_true.mp hLeaf (fourRowDegree m row)
      (List.mem_map.mpr ⟨row, List.mem_range.mpr hrow, rfl⟩))
  have hMaskDegreeAll :
      ((List.range 4).map
        (fourMaskSupportDegree (fourMultiplicityMask m))).all
          (fun degree ↦ decide (0 < degree ∧ degree ≤ 9)) = true := by
    rw [List.all_eq_true]
    intro degree hDegree
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hDegree
    have hrowLt := List.mem_range.mp hrow
    exact decide_eq_true
      ⟨fourMaskSupportDegree_pos_of_rowDegree_pos m hrowLt
        (by have := (hRowBounds row hrowLt).1; omega),
      (fourMaskSupportDegree_le_rowDegree m hrowLt).trans
        (hRowBounds row hrowLt).2⟩
  have hMaskNonzero : fourMultiplicityMask m ≠ 0 := by
    have hPositive := fourMaskSupportDegree_pos_of_rowDegree_pos m
      (row := 0) (by omega) (by have := (hRowBounds 0 (by omega)).1; omega)
    intro hZero
    unfold fourMaskSupportDegree at hPositive
    simp [hZero] at hPositive
  have hActive : ∃ s < 14, 0 < fourMultiplicityDigit m s := by
    by_contra hExists
    have hActiveEmpty : fourActiveSupportFinset m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hsRange, hsPositive⟩ := Finset.mem_filter.mp hs
      exact hExists ⟨s, Finset.mem_range.mp hsRange, hsPositive⟩
    apply hMaskNonzero
    simp [fourMultiplicityMask, hActiveEmpty]
  have hCoverPositive :=
    fourMaskCoverCount_pos_of_activeSupportsCovered m hActive hCovered
  have hCoverUpper := (fourMaskCoverCount_le_weightedCoverCount m).trans hWeighted
  have hPairUpper :=
    (middleFourMaskPairCoverCount_le_pairCoverCount m).trans hPair
  have hMaskClutter :=
    fourMaskRowsClutter_multiplicityMask_of_rowsClutter m hClutter
  have hCoveredUnion :=
    fourMaskCoveredUnion_multiplicityMask_of_activeSupportsCovered m hCovered
  unfold middleFourMaskValid
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true hCoveredUnion⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true hPairUpper⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true ⟨hCoverPositive, hCoverUpper⟩⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hMaskClutter⟩
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true hMaskNonzero, hMaskDegreeAll⟩

set_option maxHeartbeats 2000000 in
-- Expands actual support degrees through the finite blocker representation.
theorem middleFourActualSupportMultiplicity_leaf_valid {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9) :
    middleFourMultiplicityLeafValid
      (fourActualSupportMultiplicity rowOrder) = true := by
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  unfold middleFourMultiplicityLeafValid
  rw [List.all_eq_true]
  intro degree hDegree
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hDegree
  let row : FourVertex := ⟨n, List.mem_range.mp hn⟩
  have hDegree := fourRowDegree_actualSupportMultiplicity rowOrder hProper row
  have hLower := hTRows (rowOrder row : Row alpha) (rowOrder row).property
  have hUpper := hTUpper (rowOrder row : Row alpha) (rowOrder row).property
  apply decide_eq_true
  change 3 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val ∧
    fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val ≤ 9
  rw [hDegree]
  exact ⟨hLower, hUpper⟩

theorem middleFourActualSupportMultiplicity_row_upper {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9) :
    ∀ row < 4,
      fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 9 := by
  intro row hrow
  let vertex : FourVertex := ⟨row, hrow⟩
  rw [fourRowDegree_actualSupportMultiplicity rowOrder
    (fourRows_actual_support_proper rowOrder hBRows) vertex]
  exact hTUpper (rowOrder vertex : Row alpha) (rowOrder vertex).property

theorem middleFourActualSupportMultiplicity_enumeration_data {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    middleFourMaskValid (fourMultiplicityMask actual) = true ∧
      ∃ finalDegrees,
        MiddleFourGenerated (fourMaskSupports (fourMultiplicityMask actual))
          (fourMultiplicityForMask (fourMultiplicityMask actual))
          fourDegreeStateZero actual finalDegrees := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hLeaf := middleFourActualSupportMultiplicity_leaf_valid rowOrder
    hBRows hTRows hTUpper
  have hClutter :=
    fourActualSupportMultiplicity_rows_clutter rowOrder hTClutter hBRows
  have hCovered :=
    fourActualSupportMultiplicity_active_supports_covered_of_complete
      rowOrder hTClutter hBRows four_minimal_support_index_covers_complete
  have hWeighted :=
    (fourWeightedCoverCount_le_blocker_card rowOrder hBRows).trans hBCard
  have hPair := (fourPairCoverCount_le_pairRows_card rowOrder hBRows).trans hPairCard
  have hMask := middleFourMaskValid_multiplicityMask actual
    hLeaf hClutter hCovered hWeighted hPair
  have hGenerated := middleFourGenerated_multiplicityMask actual
    (fourActualSupportMultiplicity_size rowOrder)
    (middleFourActualSupportMultiplicity_row_upper rowOrder hBRows hTUpper)
    hWeighted hPair
  exact ⟨hMask, hGenerated⟩

end AiMathLab.P0054.MiddleSevenNineFinite
