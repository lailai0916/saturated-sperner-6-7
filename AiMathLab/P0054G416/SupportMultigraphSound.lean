import AiMathLab.P0054G416.SupportMultigraphLowThree
import AiMathLab.P0054G416.SupportMultigraphLowFour
import AiMathLab.P0054G416.SupportMultigraphLowFive

namespace AiMathLab.P0054.G416

inductive FiveGenerated (lowCount : Nat) :
    List Nat → FiveMultiplicity → FiveDegreeState →
      FiveMultiplicity → FiveDegreeState → Prop
  | nil (m degrees) : FiveGenerated lowCount [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : FiveMultiplicity}
      {degrees finalDegrees : FiveDegreeState} {k : Nat}
      (hChoice : k ∈ fiveMultiplicityChoices lowCount degrees s)
      (hGenerated : FiveGenerated lowCount supports (m.set! s k)
        (addFiveSupportDegree degrees s k) finalM finalDegrees) :
      FiveGenerated lowCount (s :: supports) m degrees finalM finalDegrees

theorem fiveSupportMultigraphCheckAux_sound
    {lowCount minimum : Nat} {supports : List Nat}
    {m finalM : FiveMultiplicity} {degrees finalDegrees : FiveDegreeState}
    (hGenerated : FiveGenerated lowCount supports m degrees finalM finalDegrees)
    (hCheck : fiveSupportMultigraphCheckAux lowCount minimum supports m degrees = true)
    (hValid : fiveDegreeStateValidBool lowCount finalDegrees = true) :
    minimum ≤ fiveWeightedCoverCount finalM := by
  induction hGenerated with
  | nil =>
      simpa [fiveSupportMultigraphCheckAux, hValid, decide_eq_true_eq] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll :
          (fiveMultiplicityChoices lowCount degrees s).all (fun choice ↦
            fiveSupportMultigraphCheckAux lowCount minimum supports
              (m.set! s choice) (addFiveSupportDegree degrees s choice)) = true := by
        simpa [fiveSupportMultigraphCheckAux] using hCheck
      have hBranch :
          fiveSupportMultigraphCheckAux lowCount minimum supports
            (m.set! s k) (addFiveSupportDegree degrees s k) = true := by
        exact (List.all_eq_true.mp hAll) k hChoice
      exact ih hBranch hValid

end AiMathLab.P0054.G416
