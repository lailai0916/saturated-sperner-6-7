import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

inductive FourGenerated :
    List Nat → FourMultiplicity → FourDegreeState →
      FourMultiplicity → FourDegreeState → Prop
  | nil (m degrees) : FourGenerated [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : FourMultiplicity}
      {degrees finalDegrees : FourDegreeState} {k : Nat}
      (hChoice : k ∈ fourMultiplicityChoices m degrees s)
      (hGenerated : FourGenerated supports (m.set! s k)
        (addFourSupportDegree degrees s k) finalM finalDegrees) :
      FourGenerated (s :: supports) m degrees finalM finalDegrees

theorem fourKernelAClassificationAux_sound
    {supports : List Nat} {m finalM : FourMultiplicity}
    {degrees finalDegrees : FourDegreeState}
    (hGenerated : FourGenerated supports m degrees finalM finalDegrees)
    (hCheck : fourKernelAClassificationAux supports m degrees = true)
    (hLeaf : fourMultiplicityLeafValid finalM = true) :
    fourMultiplicityInCertificate finalM = true := by
  induction hGenerated with
  | nil =>
      simpa [fourKernelAClassificationAux, hLeaf] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll :
          (fourMultiplicityChoices m degrees s).all (fun choice ↦
            fourKernelAClassificationAux supports (m.set! s choice)
              (addFourSupportDegree degrees s choice)) = true := by
        simpa [fourKernelAClassificationAux] using hCheck
      have hBranch :
          fourKernelAClassificationAux supports (m.set! s k)
            (addFourSupportDegree degrees s k) = true :=
        List.all_eq_true.mp hAll k hChoice
      exact ih hBranch hLeaf

theorem fourKernelAClassificationMaskCheck_sound
    {mask : Nat} {m : FourMultiplicity} {degrees : FourDegreeState}
    (hMask : fourMaskValid mask = true)
    (hGenerated : FourGenerated (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero m degrees)
    (hLeaf : fourMultiplicityLeafValid m = true)
    (hCheck : fourKernelAClassificationMaskCheck mask = true) :
    fourMultiplicityInCertificate m = true := by
  apply fourKernelAClassificationAux_sound hGenerated (hLeaf := hLeaf)
  simpa [fourKernelAClassificationMaskCheck, hMask] using hCheck

end AiMathLab.P0054.G419
