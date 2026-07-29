import AiMathLab.P0054G417.SupportMultigraphEarlyBridge
import AiMathLab.P0054G417.SupportMultigraphBounds

namespace AiMathLab.P0054.G417

theorem sixCompactEncodeMultiplicity_eq_sum (m : Fin 21 → Fin 4) :
    sixCompactEncodeMultiplicity m = ∑ s : Fin 21, (m s).val * 4 ^ s.val := by
  rw [sixCompactEncodeMultiplicity, Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  congr

theorem sixCompactMultiplicityWeight_eq_pow (s : Fin 21) :
    sixCompactMultiplicityWeight s.val = 4 ^ s.val := by
  fin_cases s <;> norm_num [sixCompactMultiplicityWeight]

theorem sixCompactEncodeMultiplicity_update
    (m : Fin 21 → Fin 4) (s : Fin 21) (k : Fin 4) (hZero : m s = 0) :
    sixCompactSetMultiplicity (sixCompactEncodeMultiplicity m) s.val k.val =
      sixCompactEncodeMultiplicity (Function.update m s k) := by
  classical
  rw [sixCompactEncodeMultiplicity_eq_sum, sixCompactEncodeMultiplicity_eq_sum,
    sixCompactSetMultiplicity, sixCompactMultiplicityWeight_eq_pow]
  have hUpdate :
      (fun x : Fin 21 ↦ (Function.update m s k x).val * 4 ^ x.val) =
        Function.update (fun x : Fin 21 ↦ (m x).val * 4 ^ x.val) s
          (k.val * 4 ^ s.val) := by
    funext x
    by_cases hxs : x = s
    · subst x
      simp
    · simp [Function.update_of_ne hxs]
  rw [hUpdate, Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  simp [hZero, add_comm]

def sixFunctionDegree (m : Fin 21 → Fin 4) (v : Nat) : Nat :=
  ∑ s : Fin 21, if sixSupportContains s.val v then (m s).val else 0

theorem sixFunctionDegree_update
    (m : Fin 21 → Fin 4) (s : Fin 21) (k : Fin 4) (hZero : m s = 0) (v : Nat) :
    sixFunctionDegree (Function.update m s k) v =
      sixFunctionDegree m v + if sixSupportContains s.val v then k.val else 0 := by
  classical
  unfold sixFunctionDegree
  have hUpdate :
      (fun x : Fin 21 ↦ if sixSupportContains x.val v
        then (Function.update m s k x).val else 0) =
        Function.update (fun x : Fin 21 ↦ if sixSupportContains x.val v
          then (m x).val else 0) s
          (if sixSupportContains s.val v then k.val else 0) := by
    funext x
    by_cases hxs : x = s
    · subst x
      simp
    · simp [Function.update_of_ne hxs]
  rw [hUpdate, Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  simp [hZero, add_comm]

def sixCompactDegreesOfFunction (m : Fin 21 → Fin 4) : SixCompactDegrees :=
  ⟨sixFunctionDegree m 0, sixFunctionDegree m 1, sixFunctionDegree m 2,
    sixFunctionDegree m 3, sixFunctionDegree m 4, sixFunctionDegree m 5⟩

def sixCompactAddSupportDegreeGeneric
    (degrees : SixCompactDegrees) (s k : Nat) : SixCompactDegrees :=
  ⟨degrees.d0 + if sixSupportContains s 0 then k else 0,
    degrees.d1 + if sixSupportContains s 1 then k else 0,
    degrees.d2 + if sixSupportContains s 2 then k else 0,
    degrees.d3 + if sixSupportContains s 3 then k else 0,
    degrees.d4 + if sixSupportContains s 4 then k else 0,
    degrees.d5 + if sixSupportContains s 5 then k else 0⟩

theorem sixCompactAddSupportDegree_eq_generic
    (degrees : SixCompactDegrees) (s : Fin 21) (k : Nat) :
    sixCompactAddSupportDegree degrees s.val k =
      sixCompactAddSupportDegreeGeneric degrees s.val k := by
  fin_cases s <;> rfl

theorem sixCompactDegreesOfFunction_update
    (m : Fin 21 → Fin 4) (s : Fin 21) (k : Fin 4) (hZero : m s = 0) :
    sixCompactAddSupportDegree (sixCompactDegreesOfFunction m) s.val k.val =
      sixCompactDegreesOfFunction (Function.update m s k) := by
  have hUpdated : sixCompactDegreesOfFunction (Function.update m s k) =
      ⟨sixFunctionDegree m 0 + if sixSupportContains s.val 0 then k.val else 0,
        sixFunctionDegree m 1 + if sixSupportContains s.val 1 then k.val else 0,
        sixFunctionDegree m 2 + if sixSupportContains s.val 2 then k.val else 0,
        sixFunctionDegree m 3 + if sixSupportContains s.val 3 then k.val else 0,
        sixFunctionDegree m 4 + if sixSupportContains s.val 4 then k.val else 0,
        sixFunctionDegree m 5 + if sixSupportContains s.val 5 then k.val else 0⟩ := by
    unfold sixCompactDegreesOfFunction
    rw [sixFunctionDegree_update m s k hZero 0, sixFunctionDegree_update m s k hZero 1,
      sixFunctionDegree_update m s k hZero 2, sixFunctionDegree_update m s k hZero 3,
      sixFunctionDegree_update m s k hZero 4, sixFunctionDegree_update m s k hZero 5]
  rw [sixCompactAddSupportDegree_eq_generic, hUpdated]
  rfl

def sixRestrictMultiplicity
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21)) : Fin 21 → Fin 4 :=
  fun s ↦ if s ∈ processed then target s else 0

theorem sixRestrictMultiplicity_zero
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    {s : Fin 21} (hs : s ∉ processed) :
    sixRestrictMultiplicity target processed s = 0 := by
  simp [sixRestrictMultiplicity, hs]

theorem sixRestrictMultiplicity_le
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21)) (s : Fin 21) :
    (sixRestrictMultiplicity target processed s).val ≤ (target s).val := by
  by_cases hs : s ∈ processed
  · simp [sixRestrictMultiplicity, hs]
  · simp [sixRestrictMultiplicity, hs]

theorem sixRestrictMultiplicity_update
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    (s : Fin 21) :
    Function.update (sixRestrictMultiplicity target processed) s (target s) =
      sixRestrictMultiplicity target (insert s processed) := by
  funext t
  by_cases hts : t = s
  · subst t
    simp [sixRestrictMultiplicity]
  · rw [Function.update_of_ne hts]
    simp [sixRestrictMultiplicity, hts]

theorem sixCompactEncodeRestrictMultiplicity_update
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    {s : Fin 21} (hs : s ∉ processed) :
    sixCompactSetMultiplicity
        (sixCompactEncodeMultiplicity (sixRestrictMultiplicity target processed))
        s.val (target s).val =
      sixCompactEncodeMultiplicity (sixRestrictMultiplicity target (insert s processed)) := by
  rw [sixCompactEncodeMultiplicity_update _ s (target s)
    (sixRestrictMultiplicity_zero target processed hs)]
  rw [sixRestrictMultiplicity_update target processed s]

theorem sixCompactDegreesRestrictMultiplicity_update
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    {s : Fin 21} (hs : s ∉ processed) :
    sixCompactAddSupportDegree
        (sixCompactDegreesOfFunction (sixRestrictMultiplicity target processed))
        s.val (target s).val =
      sixCompactDegreesOfFunction (sixRestrictMultiplicity target (insert s processed)) := by
  rw [sixCompactDegreesOfFunction_update _ s (target s)
    (sixRestrictMultiplicity_zero target processed hs)]
  rw [sixRestrictMultiplicity_update target processed s]

theorem sixFunctionDegree_mono
    {left right : Fin 21 → Fin 4}
    (hDigits : ∀ s, (left s).val ≤ (right s).val) (v : Nat) :
    sixFunctionDegree left v ≤ sixFunctionDegree right v := by
  unfold sixFunctionDegree
  apply Finset.sum_le_sum
  intro s hs
  by_cases hContains : sixSupportContains s.val v = true
  · simp [hContains, hDigits s]
  · simp [Bool.eq_false_of_not_eq_true hContains]

theorem sixCompactDegree_ofFunction
    (m : Fin 21 → Fin 4) {v : Nat} (hv : v < 6) :
    sixCompactDegree (sixCompactDegreesOfFunction m) v = sixFunctionDegree m v := by
  interval_cases v <;> rfl

theorem sixCompactDegree_restrict_le
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    {v : Nat} (hv : v < 6) :
    sixCompactDegree (sixCompactDegreesOfFunction
        (sixRestrictMultiplicity target processed)) v ≤
      sixFunctionDegree target v := by
  rw [sixCompactDegree_ofFunction _ hv]
  exact sixFunctionDegree_mono (sixRestrictMultiplicity_le target processed) v

theorem sixCompactMultiplicityDigit_encode_getD
    (m : Fin 21 → Fin 4) (s : Nat) :
    sixCompactMultiplicityDigit (sixCompactEncodeMultiplicity m) s =
      (List.ofFn fun t : Fin 21 ↦ (m t).val).getD s 0 := by
  rw [sixCompactMultiplicityDigit_eq_div_mod]
  unfold sixCompactEncodeMultiplicity
  apply sixOfDigits_digit
  intro digit hDigit
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hDigit
  exact (m i).isLt

theorem sixCompactMultiplicityDigit_encode_mono
    {left right : Fin 21 → Fin 4}
    (hDigits : ∀ s, (left s).val ≤ (right s).val) (s : Nat) :
    sixCompactMultiplicityDigit (sixCompactEncodeMultiplicity left) s ≤
      sixCompactMultiplicityDigit (sixCompactEncodeMultiplicity right) s := by
  rw [sixCompactMultiplicityDigit_encode_getD, sixCompactMultiplicityDigit_encode_getD]
  by_cases hs : s < 21
  · have hLeft : s < (List.ofFn fun t : Fin 21 ↦ (left t).val).length := by
      simpa using hs
    have hRight : s < (List.ofFn fun t : Fin 21 ↦ (right t).val).length := by
      simpa using hs
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hLeft, Option.getD_some,
      List.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hRight, Option.getD_some,
      List.getElem_ofFn]
    simpa using hDigits ⟨s, hs⟩
  · have hLeft : ¬s < (List.ofFn fun t : Fin 21 ↦ (left t).val).length := by
      simpa using hs
    have hRight : ¬s < (List.ofFn fun t : Fin 21 ↦ (right t).val).length := by
      simpa using hs
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hLeft),
      List.getElem?_eq_none (Nat.le_of_not_gt hRight)]

theorem sixCompactCoverSlotValue_mono
    {left right : Nat}
    (hDigits : ∀ s, sixCompactMultiplicityDigit left s ≤
      sixCompactMultiplicityDigit right s) (slot : Nat) :
    sixCompactCoverSlotValue left slot ≤ sixCompactCoverSlotValue right slot := by
  by_cases hSlot : slot = 0
  · simp [sixCompactCoverSlotValue, hSlot]
  · simp [sixCompactCoverSlotValue, hSlot, hDigits]

theorem sixCompactCoverValue_mono
    {left right : Nat}
    (hDigits : ∀ s, sixCompactMultiplicityDigit left s ≤
      sixCompactMultiplicityDigit right s) (code : Nat) :
    sixCompactCoverValue left code ≤ sixCompactCoverValue right code := by
  unfold sixCompactCoverValue
  gcongr <;> exact sixCompactCoverSlotValue_mono hDigits _

theorem sixCompactCoverGroupValue_mono
    {left right : Nat}
    (hDigits : ∀ s, sixCompactMultiplicityDigit left s ≤
      sixCompactMultiplicityDigit right s) (group : List Nat) :
    sixCompactCoverGroupValue left group ≤ sixCompactCoverGroupValue right group := by
  unfold sixCompactCoverGroupValue
  induction group with
  | nil => exact Nat.le_refl 0
  | cons code group ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (sixCompactCoverValue_mono hDigits code) ih

theorem sixCompactCoverGroupValue_restrict_le
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21)) (group : List Nat) :
    sixCompactCoverGroupValue
        (sixCompactEncodeMultiplicity (sixRestrictMultiplicity target processed)) group ≤
      sixCompactCoverGroupValue (sixCompactEncodeMultiplicity target) group := by
  apply sixCompactCoverGroupValue_mono
  exact sixCompactMultiplicityDigit_encode_mono
    (sixRestrictMultiplicity_le target processed)

inductive SixEarlyGeneratedDominated (lowCount targetM : Nat) :
    List Nat → List (List Nat) → Nat → SixCompactDegrees → Nat →
      Nat → SixCompactDegrees → Nat → Prop
  | nil (m degrees count) :
      SixEarlyGeneratedDominated lowCount targetM [] [] m degrees count m degrees count
  | cons {s : Nat} {supports : List Nat} {group : List Nat} {groups : List (List Nat)}
      {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
      {count finalCount k : Nat}
      (hChoice : k ∈ sixCompactMultiplicityChoices lowCount degrees s)
      (hCompletion :
        sixCompactDegreeCompletionPossibleBool lowCount supports
          (sixCompactAddSupportDegree degrees s k) = true)
      (hGroup : sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group ≤
        sixCompactCoverGroupValue targetM group)
      (hGenerated : SixEarlyGeneratedDominated lowCount targetM supports groups
        (sixCompactSetMultiplicity m s k)
        (sixCompactAddSupportDegree degrees s k)
        (count + sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group)
        finalM finalDegrees finalCount) :
      SixEarlyGeneratedDominated lowCount targetM (s :: supports) (group :: groups)
        m degrees count finalM finalDegrees finalCount

theorem SixEarlyGeneratedDominated.generated
    {lowCount targetM : Nat} {supports : List Nat} {groups : List (List Nat)}
    {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
    {count finalCount : Nat}
    (hGenerated : SixEarlyGeneratedDominated lowCount targetM supports groups
      m degrees count finalM finalDegrees finalCount) :
    SixEarlyGenerated lowCount supports groups m degrees count
      finalM finalDegrees finalCount := by
  induction hGenerated with
  | nil => exact SixEarlyGenerated.nil _ _ _
  | cons hChoice hCompletion hGroup hGenerated ih =>
      exact SixEarlyGenerated.cons hChoice hCompletion ih

theorem SixEarlyGeneratedDominated.count_le
    {lowCount targetM : Nat} {supports : List Nat} {groups : List (List Nat)}
    {m finalM : Nat} {degrees finalDegrees : SixCompactDegrees}
    {count finalCount : Nat}
    (hGenerated : SixEarlyGeneratedDominated lowCount targetM supports groups
      m degrees count finalM finalDegrees finalCount) :
    finalCount ≤ count + sixCompletionGroupsValue targetM groups := by
  induction hGenerated with
  | nil => simp [sixCompletionGroupsValue]
  | @cons s supports group groups m finalM degrees finalDegrees count finalCount k
      hChoice hCompletion hGroup hGenerated ih =>
      rw [sixCompletionGroupsValue] at ih
      simp only [sixCompletionGroupsValue, List.map_cons, List.sum_cons]
      omega

theorem sixTypedRemainingCapacity_eq
    (remaining : List (Fin 21)) (v : Nat) :
    3 * (remaining.filter fun s ↦ sixSupportContains s.val v).length =
      sixRemainingCapacity (remaining.map Fin.val) v := by
  simp [sixRemainingCapacity, List.filter_map, Function.comp_def]

theorem sixSumThreeFilter (remaining : List (Fin 21)) (v : Nat) :
    (remaining.map fun s ↦ if sixSupportContains s.val v then 3 else 0).sum =
      3 * (remaining.filter fun s ↦ sixSupportContains s.val v).length := by
  induction remaining with
  | nil => simp
  | cons s remaining ih =>
      by_cases hContains : sixSupportContains s.val v = true
      · simp [hContains, ih]
        omega
      · simp [Bool.eq_false_of_not_eq_true hContains, ih]

theorem sixFunctionDegree_le_restrict_add_remaining
    (target : Fin 21 → Fin 4) (processed : Finset (Fin 21))
    (remaining : List (Fin 21)) (hNodup : remaining.Nodup)
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ remaining)
    (v : Nat) :
    sixFunctionDegree target v ≤
      sixFunctionDegree (sixRestrictMultiplicity target processed) v +
        sixRemainingCapacity (remaining.map Fin.val) v := by
  have hPointwise (s : Fin 21) :
      (if sixSupportContains s.val v then (target s).val else 0) ≤
        (if sixSupportContains s.val v then
            (if s ∈ processed then target s else 0 : Fin 4).val else 0) +
          if s ∈ remaining then
            (if sixSupportContains s.val v then 3 else 0)
          else 0 := by
    by_cases hContains : sixSupportContains s.val v = true
    · simp only [hContains, ↓reduceIte]
      by_cases hProcessed : s ∈ processed
      · simp [hProcessed]
      · by_cases hZero : target s = 0
        · simp [hProcessed, hZero]
        · have hRemaining := hCovered s hZero hProcessed
          have hBound : (target s).val ≤ 3 := Nat.le_pred_of_lt (target s).isLt
          simp only [hProcessed, hRemaining, ↓reduceIte]
          omega
    · have hFalse := Bool.eq_false_of_not_eq_true hContains
      simp [hFalse]
  have hExtra :
      (∑ s : Fin 21, if s ∈ remaining then
          (if sixSupportContains s.val v then 3 else 0) else 0) =
        (remaining.map fun s ↦ if sixSupportContains s.val v then 3 else 0).sum := by
    rw [← List.sum_toFinset _ hNodup]
    rw [← Finset.sum_filter]
    rw [show (Finset.univ.filter fun s : Fin 21 ↦ s ∈ remaining) =
      remaining.toFinset by ext s; simp]
  unfold sixFunctionDegree
  calc
    ∑ s : Fin 21, (if sixSupportContains s.val v then (target s).val else 0) ≤
        ∑ s : Fin 21,
          ((if sixSupportContains s.val v then
              (if s ∈ processed then target s else 0 : Fin 4).val else 0) +
            if s ∈ remaining then
              (if sixSupportContains s.val v then 3 else 0)
            else 0) := Finset.sum_le_sum fun s _ ↦ hPointwise s
    _ = (∑ s : Fin 21, if sixSupportContains s.val v then
            (if s ∈ processed then target s else 0 : Fin 4).val else 0) +
          ∑ s : Fin 21, if s ∈ remaining then
            (if sixSupportContains s.val v then 3 else 0)
          else 0 := Finset.sum_add_distrib
    _ = (∑ s : Fin 21, if sixSupportContains s.val v then
            (if s ∈ processed then target s else 0 : Fin 4).val else 0) +
          (remaining.map fun s ↦ if sixSupportContains s.val v then 3 else 0).sum := by
            rw [hExtra]
    _ = (∑ s : Fin 21, if sixSupportContains s.val v then
            (if s ∈ processed then target s else 0 : Fin 4).val else 0) +
          sixRemainingCapacity (remaining.map Fin.val) v := by
            rw [← sixTypedRemainingCapacity_eq]
            rw [sixSumThreeFilter]

theorem sixCompactDegree_add_support
    (degrees : SixCompactDegrees) (s : Fin 21) (k : Nat)
    {v : Nat} (hv : v < 6) :
    sixCompactDegree (sixCompactAddSupportDegree degrees s.val k) v =
      sixCompactDegree degrees v + if sixSupportContains s.val v then k else 0 := by
  fin_cases s <;> interval_cases v <;> rfl

theorem sixSupportDegree_function (target : Fin 21 → Fin 4) (v : Fin 6) :
    sixSupportDegree (sixMultiplicityOfFunction target) v = sixFunctionDegree target v := by
  unfold sixSupportDegree sixFunctionDegree
  apply Finset.sum_congr rfl
  intro s hs
  rw [sixMultiplicityOfFunction_digit]
  fin_cases s <;> fin_cases v <;>
    simp [sixSupport, sixSupportContains, sixSupportMask, Nat.testBit]

theorem sixCompactChoice_of_valid
    {lowCount : Nat} (hHigh : lowCount ≤ 6) (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid lowCount (sixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (s : Fin 21) (hs : s ∉ processed) :
    (target s).val ∈ sixCompactMultiplicityChoices lowCount
      (sixCompactDegreesOfFunction (sixRestrictMultiplicity target processed)) s.val := by
  simp only [sixCompactMultiplicityChoices, List.mem_filter, List.mem_range]
  refine ⟨(target s).isLt, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · by_cases hZero : target s = 0
    · simp [hZero]
    · have hPositive : 0 < sixMultiplicityDigit
          (sixMultiplicityOfFunction target) s.val := by
        rw [sixMultiplicityOfFunction_digit]
        have hVal : (target s).val ≠ 0 := by simpa using hZero
        exact Nat.pos_of_ne_zero hVal
      have hTouch := sixSupportTouchesLowBool_true (hValid.2 s hPositive)
      simp [hTouch]
  · simp only [List.all_eq_true, List.mem_range]
    intro v hvLow
    by_cases hContains : sixSupportContains s.val v = true
    · simp only [hContains, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      have hvSix : v < 6 := lt_of_lt_of_le hvLow hHigh
      have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
      rw [if_pos hvLow, sixSupportDegree_function] at hTarget
      have hAfter := sixCompactDegree_restrict_le target (insert s processed) hvSix
      have hUpdate := sixCompactDegreesRestrictMultiplicity_update target processed hs
      rw [← hUpdate, sixCompactDegree_add_support _ s (target s).val hvSix,
        hContains, if_pos rfl] at hAfter
      rw [hTarget] at hAfter
      exact hAfter
    · simp [Bool.eq_false_of_not_eq_true hContains]

theorem sixCompactCompletion_of_valid
    {lowCount : Nat} (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid lowCount (sixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (remaining : List (Fin 21))
    (hNodup : remaining.Nodup)
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ remaining) :
    sixCompactDegreeCompletionPossibleBool lowCount (remaining.map Fin.val)
      (sixCompactDegreesOfFunction (sixRestrictMultiplicity target processed)) = true := by
  simp only [sixCompactDegreeCompletionPossibleBool, List.all_eq_true, List.mem_range]
  intro v hvSix
  simp only [decide_eq_true_eq]
  have hCapacity := sixFunctionDegree_le_restrict_add_remaining target processed remaining
    hNodup hCovered v
  rw [sixCompactDegree_ofFunction _ hvSix]
  have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
  rw [sixSupportDegree_function] at hTarget
  change (if v < lowCount then sixFunctionDegree target v = 3
    else 4 ≤ sixFunctionDegree target v) at hTarget
  by_cases hvLow : v < lowCount
  · rw [if_pos hvLow] at hTarget ⊢
    rw [← hTarget]
    exact hCapacity
  · rw [if_neg hvLow] at hTarget ⊢
    exact hTarget.trans hCapacity

theorem sixEarlyGeneratedDominated_cons
    (lowCount targetM s : Nat) (supports group : List Nat)
    (groups : List (List Nat)) (m finalM : Nat)
    (degrees finalDegrees : SixCompactDegrees) (count finalCount k : Nat)
    (hChoice : k ∈ sixCompactMultiplicityChoices lowCount degrees s)
    (hCompletion : sixCompactDegreeCompletionPossibleBool lowCount supports
      (sixCompactAddSupportDegree degrees s k) = true)
    (hGroup : sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group ≤
      sixCompactCoverGroupValue targetM group)
    (hGenerated : SixEarlyGeneratedDominated lowCount targetM supports groups
      (sixCompactSetMultiplicity m s k)
      (sixCompactAddSupportDegree degrees s k)
      (count + sixCompactCoverGroupValue (sixCompactSetMultiplicity m s k) group)
      finalM finalDegrees finalCount) :
    SixEarlyGeneratedDominated lowCount targetM (s :: supports) (group :: groups)
      m degrees count finalM finalDegrees finalCount :=
  SixEarlyGeneratedDominated.cons hChoice hCompletion hGroup hGenerated

set_option maxHeartbeats 2000000 in
-- Recursive path assembly carries dependent compact states through each support.
theorem sixEarlyGeneratedDominated_restrict
    {lowCount : Nat} (hHigh : lowCount ≤ 6) (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid lowCount (sixMultiplicityOfFunction target))
    (processed : Finset (Fin 21)) (order : List (Fin 21))
    (groups : List (List Nat)) (count : Nat)
    (hNodup : order.Nodup)
    (hFresh : ∀ s ∈ order, s ∉ processed)
    (hCovered : ∀ s, target s ≠ 0 → s ∉ processed → s ∈ order)
    (hLength : order.length = groups.length) :
    ∃ finalCount,
      SixEarlyGeneratedDominated lowCount (sixCompactEncodeMultiplicity target)
        (order.map Fin.val) groups
        (sixCompactEncodeMultiplicity (sixRestrictMultiplicity target processed))
        (sixCompactDegreesOfFunction (sixRestrictMultiplicity target processed)) count
        (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target)
        finalCount := by
  induction order generalizing processed groups count with
  | nil =>
      cases groups with
      | cons group groups => simp at hLength
      | nil =>
          have hRestrict : sixRestrictMultiplicity target processed = target := by
            funext s
            by_cases hProcessed : s ∈ processed
            · simp [sixRestrictMultiplicity, hProcessed]
            · have hZero : target s = 0 := by
                by_contra hNonzero
                exact (by simpa using hCovered s hNonzero hProcessed)
              simp [sixRestrictMultiplicity, hProcessed, hZero]
          refine ⟨count, ?_⟩
          simpa [hRestrict] using SixEarlyGeneratedDominated.nil
            (lowCount := lowCount) (targetM := sixCompactEncodeMultiplicity target)
            (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target) count
  | cons s order ih =>
      cases groups with
      | nil => simp at hLength
      | cons group groups =>
          have hParts := List.nodup_cons.mp hNodup
          have hs : s ∉ processed := hFresh s (by simp)
          have hFreshTail : ∀ t ∈ order, t ∉ insert s processed := by
            intro t ht
            simp only [Finset.mem_insert, not_or]
            refine ⟨?_, hFresh t (by simp [ht])⟩
            intro hts
            subst t
            exact hParts.1 ht
          have hCoveredTail :
              ∀ t, target t ≠ 0 → t ∉ insert s processed → t ∈ order := by
            intro t hNonzero hNot
            have hNotProcessed : t ∉ processed := by
              intro ht
              exact hNot (Finset.mem_insert_of_mem ht)
            have ht := hCovered t hNonzero hNotProcessed
            rcases List.mem_cons.mp ht with hts | ht
            · subst t
              exact False.elim (hNot (Finset.mem_insert_self s processed))
            · exact ht
          have hChoice := sixCompactChoice_of_valid hHigh target hValid processed s hs
          have hCompletion := sixCompactCompletion_of_valid target hValid
            (insert s processed) order hParts.2 hCoveredTail
          have hGroup := sixCompactCoverGroupValue_restrict_le target
            (insert s processed) group
          let nextCount := count + sixCompactCoverGroupValue
            (sixCompactEncodeMultiplicity
              (sixRestrictMultiplicity target (insert s processed))) group
          obtain ⟨finalCount, hGenerated⟩ := ih (insert s processed) groups nextCount
            hParts.2 hFreshTail hCoveredTail (by simpa using hLength)
          have hEncoded := sixCompactEncodeRestrictMultiplicity_update target processed hs
          have hDegrees := sixCompactDegreesRestrictMultiplicity_update target processed hs
          have hCompletion' :
              sixCompactDegreeCompletionPossibleBool lowCount (order.map Fin.val)
                (sixCompactAddSupportDegree
                  (sixCompactDegreesOfFunction
                    (sixRestrictMultiplicity target processed)) s.val (target s).val) = true := by
            rw [hDegrees]
            exact hCompletion
          have hGroup' :
              sixCompactCoverGroupValue
                  (sixCompactSetMultiplicity
                    (sixCompactEncodeMultiplicity
                      (sixRestrictMultiplicity target processed)) s.val (target s).val) group ≤
                sixCompactCoverGroupValue (sixCompactEncodeMultiplicity target) group := by
            rw [hEncoded]
            exact hGroup
          have hGenerated' :
              SixEarlyGeneratedDominated lowCount (sixCompactEncodeMultiplicity target)
                (order.map Fin.val) groups
                (sixCompactSetMultiplicity
                  (sixCompactEncodeMultiplicity
                    (sixRestrictMultiplicity target processed)) s.val (target s).val)
                (sixCompactAddSupportDegree
                  (sixCompactDegreesOfFunction
                    (sixRestrictMultiplicity target processed)) s.val (target s).val)
                (count + sixCompactCoverGroupValue
                  (sixCompactSetMultiplicity
                    (sixCompactEncodeMultiplicity
                      (sixRestrictMultiplicity target processed)) s.val (target s).val) group)
                (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target)
                finalCount := by
            rw [hEncoded, hDegrees]
            simpa only [nextCount] using hGenerated
          refine ⟨finalCount, ?_⟩
          exact sixEarlyGeneratedDominated_cons lowCount
            (sixCompactEncodeMultiplicity target) s.val (order.map Fin.val) group groups
            (sixCompactEncodeMultiplicity (sixRestrictMultiplicity target processed))
            (sixCompactEncodeMultiplicity target)
            (sixCompactDegreesOfFunction (sixRestrictMultiplicity target processed))
            (sixCompactDegreesOfFunction target) count finalCount (target s).val
            hChoice hCompletion' hGroup' hGenerated'

theorem sixCompactStateValid_of_valid
    {lowCount : Nat} (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid lowCount (sixMultiplicityOfFunction target)) :
    sixCompactDegreeStateValidBool lowCount (sixCompactDegreesOfFunction target) = true := by
  simp only [sixCompactDegreeStateValidBool, List.all_eq_true, List.mem_range]
  intro v hvSix
  have hTarget := hValid.1 (⟨v, hvSix⟩ : SixVertex)
  rw [sixSupportDegree_function] at hTarget
  change (if v < lowCount then sixFunctionDegree target v = 3
    else 4 ≤ sixFunctionDegree target v) at hTarget
  rw [sixCompactDegree_ofFunction _ hvSix]
  simpa [decide_eq_true_eq] using hTarget

def sixTypedSupportOrder4 : List (Fin 21) :=
  [9, 10, 13, 14, 16, 17, 18, 19, 6, 7, 8, 11, 12, 15, 0, 1, 2, 3]

def sixTypedSupportOrder5 : List (Fin 21) :=
  [10, 14, 17, 19, 20, 6, 7, 8, 9, 11, 12, 13, 15, 16, 18, 0, 1, 2, 3, 4]

def sixTypedSupportOrder6 : List (Fin 21) :=
  [0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 15, 16, 17, 2, 18, 19, 3, 20, 4, 5]

theorem sixTargetCovered_four (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid 4 (sixMultiplicityOfFunction target)) :
    ∀ s, target s ≠ 0 → s ∈ sixTypedSupportOrder4 := by
  intro s hNonzero
  have hPositive : 0 < sixMultiplicityDigit (sixMultiplicityOfFunction target) s.val := by
    rw [sixMultiplicityOfFunction_digit]
    exact Nat.pos_of_ne_zero (by simpa using hNonzero)
  have hTouch := hValid.2 s hPositive
  fin_cases s <;> simp_all [sixTypedSupportOrder4, sixSupportTouchesLow, sixSupport]

theorem sixTargetCovered_five (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid 5 (sixMultiplicityOfFunction target)) :
    ∀ s, target s ≠ 0 → s ∈ sixTypedSupportOrder5 := by
  intro s hNonzero
  have hPositive : 0 < sixMultiplicityDigit (sixMultiplicityOfFunction target) s.val := by
    rw [sixMultiplicityOfFunction_digit]
    exact Nat.pos_of_ne_zero (by simpa using hNonzero)
  have hTouch := hValid.2 s hPositive
  fin_cases s <;> simp_all [sixTypedSupportOrder5, sixSupportTouchesLow, sixSupport]

theorem sixTargetCovered_six (target : Fin 21 → Fin 4) :
    ∀ s, target s ≠ 0 → s ∈ sixTypedSupportOrder6 := by
  intro s hNonzero
  fin_cases s <;> simp [sixTypedSupportOrder6]

@[simp] theorem sixCompactEncode_zero_function :
    sixCompactEncodeMultiplicity (fun _ : Fin 21 ↦ 0) = 0 := by
  rfl

@[simp] theorem sixCompactDegrees_zero_function :
    sixCompactDegreesOfFunction (fun _ : Fin 21 ↦ 0) = sixCompactDegreesZero := by
  simp [sixCompactDegreesOfFunction, sixFunctionDegree, sixCompactDegreesZero]

theorem sixEarlyGeneratedDominated_four (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid 4 (sixMultiplicityOfFunction target)) :
    ∃ finalCount,
      SixEarlyGeneratedDominated 4 (sixCompactEncodeMultiplicity target)
        sixSupportOrder4 sixCompletionGroups4 0 sixCompactDegreesZero 0
        (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target)
        finalCount := by
  have hGenerated := sixEarlyGeneratedDominated_restrict (lowCount := 4) (by omega)
    target hValid ∅ sixTypedSupportOrder4 sixCompletionGroups4 0 (by decide) (by simp)
    (by intro s hNonzero hs; exact sixTargetCovered_four target hValid s hNonzero) (by rfl)
  have hOrder : sixTypedSupportOrder4.map Fin.val = sixSupportOrder4 := by rfl
  have hRestrict : sixRestrictMultiplicity target ∅ = fun _ ↦ 0 := by
    funext s
    simp [sixRestrictMultiplicity]
  rw [hOrder, hRestrict, sixCompactEncode_zero_function,
    sixCompactDegrees_zero_function] at hGenerated
  exact hGenerated

theorem sixEarlyGeneratedDominated_five (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid 5 (sixMultiplicityOfFunction target)) :
    ∃ finalCount,
      SixEarlyGeneratedDominated 5 (sixCompactEncodeMultiplicity target)
        sixSupportOrder5 sixCompletionGroups5 0 sixCompactDegreesZero 0
        (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target)
        finalCount := by
  have hGenerated := sixEarlyGeneratedDominated_restrict (lowCount := 5) (by omega)
    target hValid ∅ sixTypedSupportOrder5 sixCompletionGroups5 0 (by decide) (by simp)
    (by intro s hNonzero hs; exact sixTargetCovered_five target hValid s hNonzero) (by rfl)
  have hOrder : sixTypedSupportOrder5.map Fin.val = sixSupportOrder5 := by rfl
  have hRestrict : sixRestrictMultiplicity target ∅ = fun _ ↦ 0 := by
    funext s
    simp [sixRestrictMultiplicity]
  rw [hOrder, hRestrict, sixCompactEncode_zero_function,
    sixCompactDegrees_zero_function] at hGenerated
  exact hGenerated

theorem sixEarlyGeneratedDominated_six (target : Fin 21 → Fin 4)
    (hValid : SixMultiplicityValid 6 (sixMultiplicityOfFunction target)) :
    ∃ finalCount,
      SixEarlyGeneratedDominated 6 (sixCompactEncodeMultiplicity target)
        sixSupportOrder6 sixCompletionGroups6 0 sixCompactDegreesZero 0
        (sixCompactEncodeMultiplicity target) (sixCompactDegreesOfFunction target)
        finalCount := by
  have hGenerated := sixEarlyGeneratedDominated_restrict (lowCount := 6) (by omega)
    target hValid ∅ sixTypedSupportOrder6 sixCompletionGroups6 0 (by decide) (by simp)
    (by intro s hNonzero hs; exact sixTargetCovered_six target s hNonzero) (by rfl)
  have hOrder : sixTypedSupportOrder6.map Fin.val = sixSupportOrder6 := by rfl
  have hRestrict : sixRestrictMultiplicity target ∅ = fun _ ↦ 0 := by
    funext s
    simp [sixRestrictMultiplicity]
  rw [hOrder, hRestrict, sixCompactEncode_zero_function,
    sixCompactDegrees_zero_function] at hGenerated
  exact hGenerated

end AiMathLab.P0054.G417
