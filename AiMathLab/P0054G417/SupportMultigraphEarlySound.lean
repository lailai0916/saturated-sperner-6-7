import AiMathLab.P0054G417.SixSupportMultigraphEarly

namespace AiMathLab.P0054.G417

inductive SixEarlyGenerated (lowCount : Nat) :
    List Nat → List (List Nat) → Nat → SixCompactDegrees → Nat →
      Nat → SixCompactDegrees → Nat → Prop
  | nil (m degrees count) :
      SixEarlyGenerated lowCount [] [] m degrees count m degrees count
  | cons {s : Nat} {supports : List Nat} {group : List Nat} {groups : List (List Nat)}
      {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
      {count finalCount k : Nat}
      (hChoice : k ∈ sixCompactMultiplicityChoices lowCount degrees s)
      (hCompletion :
        sixCompactDegreeCompletionPossibleBool lowCount supports
          (sixCompactAddSupportDegree degrees s k) = true)
      (hGenerated : SixEarlyGenerated lowCount supports groups
        (sixCompactSetMultiplicity m s k)
        (sixCompactAddSupportDegree degrees s k)
        (count + sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group)
        finalM finalDegrees finalCount) :
      SixEarlyGenerated lowCount (s :: supports) (group :: groups) m degrees count
        finalM finalDegrees finalCount

theorem SixEarlyGenerated.count_mono {lowCount : Nat}
    {supports : List Nat} {groups : List (List Nat)}
    {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
    {count finalCount : Nat}
    (hGenerated : SixEarlyGenerated lowCount supports groups m degrees count
      finalM finalDegrees finalCount) :
    count ≤ finalCount := by
  induction hGenerated with
  | nil => exact Nat.le_refl _
  | @cons s supports group groups m finalM degrees finalDegrees count finalCount k
      hChoice hCompletion hGenerated ih =>
      exact (Nat.le_add_right count _).trans ih

theorem sixSupportMultigraphEarlyCheckAux_sound
    {lowCount minimum : Nat} {supports : List Nat} {groups : List (List Nat)}
    {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
    {count finalCount : Nat}
    (hGenerated : SixEarlyGenerated lowCount supports groups m degrees count
      finalM finalDegrees finalCount)
    (hCheck : sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups
      m degrees count = true)
    (hFinalValid : sixCompactDegreeStateValidBool lowCount finalDegrees = true) :
    minimum ≤ finalCount := by
  induction hGenerated with
  | nil =>
      simpa [sixSupportMultigraphEarlyCheckAux, hFinalValid, decide_eq_true_eq] using hCheck
  | @cons s supports group groups m finalM degrees finalDegrees count finalCount k
      hChoice hCompletion hGenerated ih =>
      have hAll := hCheck
      simp only [sixSupportMultigraphEarlyCheckAux] at hAll
      have hBranch := (List.all_eq_true.mp hAll) k hChoice
      have hBranch' :
          minimum ≤ count +
              sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group ∨
            sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups
              (sixCompactSetMultiplicity m s k)
              (sixCompactAddSupportDegree degrees s k)
              (count + sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group) =
                true := by
        simpa [hCompletion, decide_eq_true_eq] using hBranch
      cases hBranch' with
      | inl hReached => exact hReached.trans hGenerated.count_mono
      | inr hRecursive => exact ih hRecursive hFinalValid

end AiMathLab.P0054.G417
