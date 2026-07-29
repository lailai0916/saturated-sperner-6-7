import AiMathLab.P0054G419.KernelAData

namespace AiMathLab.P0054.G419

abbrev FourMultiplicity := Array Nat
abbrev FourDegreeState := Array Nat

def fourMinimalSupportCovers : List (List Nat) :=
  [[0, 13], [1, 12], [2, 11], [2, 12], [2, 13], [3, 10], [4, 9],
    [4, 10], [4, 13], [5, 8], [5, 10], [5, 12], [6, 7], [6, 8],
    [6, 9], [6, 10], [6, 11], [6, 12], [6, 13], [8, 13], [9, 12],
    [10, 11], [10, 12], [10, 13], [12, 13], [0, 1, 11], [0, 3, 9],
    [0, 5, 7], [0, 5, 9], [0, 5, 11], [0, 9, 11], [1, 3, 8],
    [1, 4, 7], [1, 4, 8], [1, 4, 11], [1, 8, 11], [2, 3, 7],
    [2, 3, 8], [2, 3, 9], [2, 4, 7], [2, 4, 8], [2, 5, 7],
    [2, 5, 9], [3, 8, 9], [4, 5, 7], [4, 5, 11], [8, 9, 11],
    [0, 1, 3, 7]]

def fourMinimalSupportCoverMasks : List Nat :=
  [8193, 4098, 2052, 4100, 8196, 1032, 528, 1040, 8208, 288, 1056,
    4128, 192, 320, 576, 1088, 2112, 4160, 8256, 8448, 4608, 3072,
    5120, 9216, 12288, 2051, 521, 161, 545, 2081, 2561, 266, 146,
    274, 2066, 2306, 140, 268, 524, 148, 276, 164, 548, 776, 176,
    2096, 2816, 139]

def fourMinimalSupportCoverCodes : List Nat :=
  [225, 210, 195, 211, 227, 180, 165, 181, 229, 150, 182, 214, 135,
    151, 167, 183, 199, 215, 231, 233, 218, 203, 219, 235, 237, 3105,
    2625, 2145, 2657, 3169, 3233, 2370, 2130, 2386, 3154, 3218,
    2115, 2371, 2627, 2131, 2387, 2147, 2659, 2708, 2149, 3173,
    3241, 33825]

def fourMultiplicityDigit (m : FourMultiplicity) (s : Nat) : Nat :=
  m.getD s 0

def fourSupportMask (s : Nat) : Nat := s + 1

def fourSupportContains (s row : Nat) : Bool :=
  (fourSupportMask s).testBit row

def fourCoverSlotValue (m : FourMultiplicity) (slot : Nat) : Nat :=
  if slot = 0 then 1 else fourMultiplicityDigit m (slot - 1)

def fourCoverCodeValue (m : FourMultiplicity) (code : Nat) : Nat :=
  fourCoverSlotValue m (Nat.land code 15) *
    fourCoverSlotValue m (Nat.land (Nat.shiftRight code 4) 15) *
      fourCoverSlotValue m (Nat.land (Nat.shiftRight code 8) 15) *
        fourCoverSlotValue m (Nat.land (Nat.shiftRight code 12) 15)

def fourWeightedCoverCount (m : FourMultiplicity) : Nat :=
  (fourMinimalSupportCoverCodes.map (fourCoverCodeValue m)).sum

def fourPairCoverCount (m : FourMultiplicity) : Nat :=
  ((fourMinimalSupportCoverCodes.take 25).map (fourCoverCodeValue m)).sum

def fourRowDegree (m : FourMultiplicity) (row : Nat) : Nat :=
  ((List.range 14).map fun s =>
    if fourSupportContains s row then fourMultiplicityDigit m s else 0).sum

def fourRowsClutter (m : FourMultiplicity) : Bool :=
  (List.range 4).all fun left =>
    (List.range 4).all fun right =>
      decide (left = right) ||
        (List.range 14).any fun s =>
          decide (0 < fourMultiplicityDigit m s) &&
            fourSupportContains s left && !fourSupportContains s right

def fourActiveSupportsCovered (m : FourMultiplicity) : Bool :=
  (List.range 14).all fun s =>
    decide (fourMultiplicityDigit m s = 0) ||
      fourMinimalSupportCovers.any fun cover =>
        decide (s ∈ cover) &&
          cover.all fun t => decide (0 < fourMultiplicityDigit m t)

def fourMaskContains (mask s : Nat) : Bool := mask.testBit s

def fourMaskSupports (mask : Nat) : List Nat :=
  (List.range 14).filter (fourMaskContains mask)

def fourMaskCovers (mask : Nat) : List (List Nat) :=
  fourMinimalSupportCovers.filter fun cover =>
    cover.all (fourMaskContains mask)

def fourMaskCoverCount (mask : Nat) : Nat :=
  (fourMinimalSupportCoverMasks.filter fun coverMask =>
    decide (Nat.land mask coverMask = coverMask)).length

def fourMaskCoveredUnion (mask : Nat) : Nat :=
  fourMinimalSupportCoverMasks.foldl (fun covered coverMask =>
    if Nat.land mask coverMask = coverMask then Nat.lor covered coverMask else covered) 0

def fourRowSupportMask : Nat → Nat
  | 0 => 5461
  | 1 => 9830
  | 2 => 14456
  | 3 => 16256
  | _ => 0

def fourDirectionalSupportMask : Nat → Nat → Nat
  | 0, 1 => 4369
  | 0, 2 => 1285
  | 0, 3 => 85
  | 1, 0 => 8738
  | 1, 2 => 1542
  | 1, 3 => 102
  | 2, 0 => 10280
  | 2, 1 => 6168
  | 2, 3 => 120
  | 3, 0 => 10880
  | 3, 1 => 6528
  | 3, 2 => 1920
  | _, _ => 0

def fourMaskSupportDegree (mask row : Nat) : Nat :=
  ((List.range 14).filter fun s =>
    (Nat.land mask (fourRowSupportMask row)).testBit s).length

def fourMaskRowsClutter (mask : Nat) : Bool :=
  (List.range 4).all fun left =>
    (List.range 4).all fun right =>
      decide (left = right) || decide (Nat.land mask (fourDirectionalSupportMask left right) ≠ 0)

def fourMaskValid (mask : Nat) : Bool :=
  let supportDegrees := (List.range 4).map (fourMaskSupportDegree mask)
  decide (mask ≠ 0) &&
    supportDegrees.all (fun degree => decide (0 < degree ∧ degree ≤ 6)) &&
      fourMaskRowsClutter mask &&
        decide (0 < fourMaskCoverCount mask ∧ fourMaskCoverCount mask ≤ 6) &&
          decide (fourMaskCoveredUnion mask = mask)

def fourMultiplicityLeafValid (m : FourMultiplicity) : Bool :=
  let degrees := (List.range 4).map (fourRowDegree m)
  degrees.all (fun degree => decide (3 ≤ degree ∧ degree ≤ 6)) &&
    degrees.any fun degree => decide (degree = 3)

def fourMultiplicityInCertificate (m : FourMultiplicity) : Bool :=
  fourMultiplicityCertificate.any fun values => decide (m.toList = values)

def fourMultiplicityValid (m : FourMultiplicity) : Bool :=
  let degrees := (List.range 4).map (fourRowDegree m)
  degrees.all fun degree => decide (3 ≤ degree ∧ degree ≤ 6) &&
    degrees.any fun degree => decide (degree = 3) &&
      fourRowsClutter m && fourActiveSupportsCovered m &&
        decide (fourWeightedCoverCount m ≤ 6)

abbrev FourPoint := Nat × Nat

def fourActivePoints (m : FourMultiplicity) : List FourPoint :=
  (List.range 14).flatMap fun s =>
    (List.range (fourMultiplicityDigit m s)).map fun copy => (s, copy)

def fourPointCover (points : List FourPoint) : Bool :=
  let unionMask := points.foldl (fun mask point => Nat.lor mask (fourSupportMask point.1)) 0
  decide (unionMask = 15) &&
    points.all fun point =>
      decide ((points.erase point).foldl
        (fun mask other => Nat.lor mask (fourSupportMask other.1)) 0 ≠ 15)

def fourTriplePointCover (a b c : FourPoint) : Bool :=
  let ma := fourSupportMask a.1
  let mb := fourSupportMask b.1
  let mc := fourSupportMask c.1
  decide (Nat.lor ma (Nat.lor mb mc) = 15) &&
    decide (Nat.lor mb mc ≠ 15) && decide (Nat.lor ma mc ≠ 15) &&
      decide (Nat.lor ma mb ≠ 15)

def fourKernelOrderedCompatible
    (outside : List FourPoint) (a b c : FourPoint) : Bool :=
  outside.any fun u =>
    outside.any fun v =>
      decide (v ≠ u) &&
        outside.any fun w =>
          decide (w ≠ u ∧ w ≠ v) &&
            fourTriplePointCover a u v &&
              fourTriplePointCover b u w && fourTriplePointCover c v w

def fourKernelCompatible (m : FourMultiplicity) : Bool :=
  let points := fourActivePoints m
  (List.range 4).any fun row =>
    let rowPoints := points.filter fun point => fourSupportContains point.1 row
    decide (rowPoints.length = 3) &&
      match rowPoints with
      | [p, q, r] =>
          let outside := points.filter fun point => !fourSupportContains point.1 row
          fourKernelOrderedCompatible outside p q r ||
            fourKernelOrderedCompatible outside p r q ||
              fourKernelOrderedCompatible outside q p r ||
                fourKernelOrderedCompatible outside q r p ||
                  fourKernelOrderedCompatible outside r p q ||
                    fourKernelOrderedCompatible outside r q p
      | _ => false

def fourMultiplicityZero : FourMultiplicity := Array.replicate 14 0

def fourMultiplicityForMask (mask : Nat) : FourMultiplicity :=
  Array.ofFn fun support : Fin 14 => if mask.testBit support.val then 1 else 0

def fourDegreeStateZero : FourDegreeState := Array.replicate 4 0

def addFourSupportDegree
    (degrees : FourDegreeState) (s k : Nat) : FourDegreeState :=
  Array.ofFn fun row : Fin 4 =>
    degrees.getD row.val 0 + if fourSupportContains s row.val then k else 0

def fourMultiplicityChoices
    (m : FourMultiplicity) (degrees : FourDegreeState) (s : Nat) : List Nat :=
  ((List.range 6).map (· + 1)).filter fun k =>
    ((List.range 4).all fun row =>
      !fourSupportContains s row || decide (degrees.getD row 0 + k ≤ 6)) &&
      decide (fourWeightedCoverCount (m.set! s k) ≤ 6)

def fourKernelACheckAux :
    List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], m, _ => !fourMultiplicityLeafValid m || !fourKernelCompatible m
  | s :: supports, m, degrees =>
      (fourMultiplicityChoices m degrees s).all fun k =>
        fourKernelACheckAux supports (m.set! s k)
          (addFourSupportDegree degrees s k)

def fourKernelAClassificationAux :
    List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], m, _ => !fourMultiplicityLeafValid m || fourMultiplicityInCertificate m
  | s :: supports, m, degrees =>
      (fourMultiplicityChoices m degrees s).all fun k =>
        fourKernelAClassificationAux supports (m.set! s k)
          (addFourSupportDegree degrees s k)

def fourKernelAClassificationMaskCheck (mask : Nat) : Bool :=
  !fourMaskValid mask ||
    fourKernelAClassificationAux (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero

def fourKernelAClassificationValuesCheckAux :
    List Nat → List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], supports, m, degrees => fourKernelAClassificationAux supports m degrees
  | _, [], _, _ => true
  | k :: values, s :: supports, m, degrees =>
      if k ∈ fourMultiplicityChoices m degrees s then
        fourKernelAClassificationValuesCheckAux values supports (m.set! s k)
          (addFourSupportDegree degrees s k)
      else true

def fourKernelAClassificationValuesCheck
    (mask : Nat) (values : List Nat) : Bool :=
  fourKernelAClassificationValuesCheckAux values (fourMaskSupports mask)
    (fourMultiplicityForMask mask) fourDegreeStateZero

def fourKernelATwoPrefixAdmissible (mask k l : Nat) : Bool :=
  match fourMaskSupports mask with
  | s :: t :: _ =>
      decide (k ∈ fourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s) &&
      decide (l ∈ fourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t)
  | _ => false

theorem fourKernelAClassificationMaskCheck_of_list
    {masks : List Nat}
    (hCheck : masks.all fourKernelAClassificationMaskCheck = true)
    {mask : Nat} (hMask : mask ∈ masks) :
    fourKernelAClassificationMaskCheck mask = true :=
  List.all_eq_true.mp hCheck mask hMask

theorem fourKernelAClassificationMaskCheck_of_two_prefixes
    (mask s t : Nat) (supports : List Nat)
    (hSupports : fourMaskSupports mask = s :: t :: supports)
    (hValid : fourMaskValid mask = true)
    (hPrefixes : ∀ k ∈ fourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s,
      ∀ l ∈ fourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t,
        fourKernelAClassificationValuesCheck mask [k, l] = true) :
    fourKernelAClassificationMaskCheck mask = true := by
  simp only [fourKernelAClassificationMaskCheck, hValid,
    Bool.not_true, Bool.false_or]
  rw [hSupports]
  simp only [fourKernelAClassificationAux, List.all_eq_true]
  intro k hk l hl
  have hPrefix := hPrefixes k hk l hl
  unfold fourKernelAClassificationValuesCheck at hPrefix
  rw [hSupports] at hPrefix
  simp only [fourKernelAClassificationValuesCheckAux] at hPrefix
  rw [if_pos hk, if_pos hl] at hPrefix
  exact hPrefix

theorem fourKernelAClassificationMaskCheck_of_three_prefixes
    (mask s t u : Nat) (supports : List Nat)
    (hSupports : fourMaskSupports mask = s :: t :: u :: supports)
    (hValid : fourMaskValid mask = true)
    (hPrefixes : ∀ k ∈ fourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s,
      ∀ l ∈ fourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t,
      ∀ n ∈ fourMultiplicityChoices
        (((fourMultiplicityForMask mask).set! s k).set! t l)
        (addFourSupportDegree
          (addFourSupportDegree fourDegreeStateZero s k) t l) u,
        fourKernelAClassificationValuesCheck mask [k, l, n] = true) :
    fourKernelAClassificationMaskCheck mask = true := by
  simp only [fourKernelAClassificationMaskCheck, hValid,
    Bool.not_true, Bool.false_or]
  rw [hSupports]
  simp only [fourKernelAClassificationAux, List.all_eq_true]
  intro k hk l hl n hn
  have hPrefix := hPrefixes k hk l hl n hn
  unfold fourKernelAClassificationValuesCheck at hPrefix
  rw [hSupports] at hPrefix
  simp only [fourKernelAClassificationValuesCheckAux] at hPrefix
  rw [if_pos hk, if_pos hl, if_pos hn] at hPrefix
  exact hPrefix

def fourKernelAMaskCheck (mask : Nat) : Bool :=
  !fourMaskValid mask ||
    fourKernelACheckAux (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero

def fourKernelAPrefixCheck (mask k : Nat) : Bool :=
  match fourMaskSupports mask with
  | [] => true
  | s :: supports =>
      if k ∈ fourMultiplicityChoices (fourMultiplicityForMask mask) fourDegreeStateZero s then
        fourKernelACheckAux supports ((fourMultiplicityForMask mask).set! s k)
          (addFourSupportDegree fourDegreeStateZero s k)
      else true

def fourKernelAValuesCheckAux :
    List Nat → List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], supports, m, degrees => fourKernelACheckAux supports m degrees
  | _, [], _, _ => true
  | k :: values, s :: supports, m, degrees =>
      if k ∈ fourMultiplicityChoices m degrees s then
        fourKernelAValuesCheckAux values supports (m.set! s k)
          (addFourSupportDegree degrees s k)
      else true

def fourKernelAValuesCheck (mask : Nat) (values : List Nat) : Bool :=
  fourKernelAValuesCheckAux values (fourMaskSupports mask)
    (fourMultiplicityForMask mask) fourDegreeStateZero

def fourKernelAChunkCheck (chunk : Nat) : Bool :=
  ((List.range 64).map fun offset =>
    ((chunk * 64 + offset) * 14215) % 16384).all
    fourKernelAMaskCheck

def fourKernelACheck : Bool :=
  (List.range 256).all fourKernelAChunkCheck

theorem fourKernelAMaskCheck_of_two_prefixes
    (mask s t : Nat) (supports : List Nat)
    (hSupports : fourMaskSupports mask = s :: t :: supports)
    (hValid : fourMaskValid mask = true)
    (hPrefixes : ∀ k ∈ fourMultiplicityChoices
        (fourMultiplicityForMask mask) fourDegreeStateZero s,
      ∀ l ∈ fourMultiplicityChoices
        ((fourMultiplicityForMask mask).set! s k)
        (addFourSupportDegree fourDegreeStateZero s k) t,
        fourKernelAValuesCheck mask [k, l] = true) :
    fourKernelAMaskCheck mask = true := by
  simp only [fourKernelAMaskCheck, hValid, Bool.not_true, Bool.false_or]
  rw [hSupports]
  simp only [fourKernelACheckAux, List.all_eq_true]
  intro k hk
  intro l hl
  have hPrefix := hPrefixes k hk l hl
  unfold fourKernelAValuesCheck at hPrefix
  rw [hSupports] at hPrefix
  simp only [fourKernelAValuesCheckAux] at hPrefix
  rw [if_pos hk, if_pos hl] at hPrefix
  exact hPrefix

end AiMathLab.P0054.G419
