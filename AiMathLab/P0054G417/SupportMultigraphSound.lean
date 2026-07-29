import AiMathLab.P0054G417.SixSupportMultigraphFinite

namespace AiMathLab.P0054.G417

inductive SixGenerated (lowCount : Nat) :
    List Nat → SixMultiplicity → SixDegreeState →
      SixMultiplicity → SixDegreeState → Prop
  | nil (m degrees) : SixGenerated lowCount [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : SixMultiplicity}
      {degrees finalDegrees : SixDegreeState} {k : Nat}
      (hChoice : k ∈ sixMultiplicityChoices lowCount degrees s)
      (hGenerated : SixGenerated lowCount supports (m.set! s k)
        (addSixSupportDegree degrees s k) finalM finalDegrees) :
      SixGenerated lowCount (s :: supports) m degrees finalM finalDegrees

theorem sixSupportMultigraphCheckAux_sound
    {lowCount minimum : Nat} {supports : List Nat}
    {m finalM : SixMultiplicity} {degrees finalDegrees : SixDegreeState}
    (hGenerated : SixGenerated lowCount supports m degrees finalM finalDegrees)
    (hCheck : sixSupportMultigraphCheckAux lowCount minimum supports m degrees = true)
    (hValid : sixDegreeStateValidBool lowCount finalDegrees = true) :
    minimum ≤ sixWeightedCoverCount finalM := by
  induction hGenerated with
  | nil =>
      simpa [sixSupportMultigraphCheckAux, hValid, decide_eq_true_eq] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll :
          (sixMultiplicityChoices lowCount degrees s).all (fun choice ↦
            sixSupportMultigraphCheckAux lowCount minimum supports
              (m.set! s choice) (addSixSupportDegree degrees s choice)) = true := by
        simpa [sixSupportMultigraphCheckAux] using hCheck
      have hBranch :
          sixSupportMultigraphCheckAux lowCount minimum supports
            (m.set! s k) (addSixSupportDegree degrees s k) = true := by
        exact (List.all_eq_true.mp hAll) k hChoice
      exact ih hBranch hValid

end AiMathLab.P0054.G417
