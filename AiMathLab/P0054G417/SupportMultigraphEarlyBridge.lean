import AiMathLab.P0054G417.SupportMultigraphEarlySound

namespace AiMathLab.P0054.G417

theorem sixCompactMultiplicityDigit_eq_div_mod (m s : Nat) :
    sixCompactMultiplicityDigit m s = m / 4 ^ s % 4 := by
  change ((m >>> (2 * s)) &&& 3) = m / 4 ^ s % 4
  rw [show 3 = 2 ^ 2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (2 * s) = 4 ^ s by rw [pow_mul]; norm_num]

theorem sixOfDigits_digit (digits : List Nat)
    (hDigits : ∀ digit ∈ digits, digit < 4) (i : Nat) :
    Nat.ofDigits 4 digits / 4 ^ i % 4 = digits.getD i 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i (by norm_num) digits hDigits]
  rw [Nat.ofDigits_mod_eq_head!]
  by_cases hi : i < digits.length
  · have hDrop := List.drop_eq_getElem_cons hi
    have hDigit : digits[i] < 4 := hDigits digits[i] (List.getElem_mem hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hDrop]
    simp only [List.head!_cons]
    exact Nat.mod_eq_of_lt hDigit
  · have hDrop : digits.drop i = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
    rw [hDrop]
    simp [List.getD_eq_getElem?_getD, hi]

def sixCompactEncodeMultiplicity (m : Fin 21 → Fin 4) : Nat :=
  Nat.ofDigits 4 (List.ofFn fun s : Fin 21 ↦ (m s).val)

@[simp] theorem sixCompactMultiplicityDigit_encode
    (m : Fin 21 → Fin 4) (s : Fin 21) :
    sixCompactMultiplicityDigit (sixCompactEncodeMultiplicity m) s.val = (m s).val := by
  rw [sixCompactMultiplicityDigit_eq_div_mod]
  unfold sixCompactEncodeMultiplicity
  rw [sixOfDigits_digit]
  · have hs : s.val < (List.ofFn fun i : Fin 21 ↦ (m i).val).length := by simp
    rw [List.getD_eq_getElem?_getD]
    simp only [List.getElem?_eq_getElem hs, Option.getD_some]
    rw [List.getElem_ofFn]
  · intro digit hDigit
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hDigit
    exact (m i).isLt

def sixMultiplicityOfFunction (m : Fin 21 → Fin 4) : SixMultiplicity :=
  Array.ofFn fun s : Fin 21 ↦ (m s).val

def sixCompactEncodeCover : List SixSupportIndex → Nat
  | [] => 0
  | s :: supports => s.val + 1 + 32 * sixCompactEncodeCover supports

def sixCompactCoverHeadSlot : List SixSupportIndex → Nat
  | [] => 0
  | s :: _ => s.val + 1

@[simp] theorem sixCompactEncodeCover_shiftRight_five (C : List SixSupportIndex) :
    sixCompactEncodeCover C >>> 5 = sixCompactEncodeCover C.tail := by
  cases C with
  | nil => rfl
  | cons s supports =>
      simp only [sixCompactEncodeCover, List.tail_cons]
      rw [Nat.shiftRight_eq_div_pow]
      norm_num
      have hs := s.isLt
      omega

theorem sixCompactEncodeCover_shiftRight (C : List SixSupportIndex) (n : Nat) :
    sixCompactEncodeCover C >>> (5 * n) = sixCompactEncodeCover (C.drop n) := by
  induction n generalizing C with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Nat.shiftRight_add, ih, sixCompactEncodeCover_shiftRight_five]
      simp

@[simp] theorem sixCompactEncodeCover_land (C : List SixSupportIndex) :
    sixCompactEncodeCover C &&& 31 = sixCompactCoverHeadSlot C := by
  cases C with
  | nil => rfl
  | cons s supports =>
      simp only [sixCompactEncodeCover, sixCompactCoverHeadSlot]
      rw [show 31 = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
      norm_num
      have hs := s.isLt
      omega

@[simp] theorem sixCompactCoverSlotValue_encode
    (m : Fin 21 → Fin 4) (s : SixSupportIndex) :
    sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m) (s.val + 1) = (m s).val := by
  simp [sixCompactCoverSlotValue]

set_option maxHeartbeats 0 in
-- The six-slot decoder normalizes symbolic bit operations and products.
theorem sixCompactCoverValue_encode (m : Fin 21 → Fin 4)
    (C : List SixSupportIndex) (hLength : C.length ≤ 6) :
    sixCompactCoverValue (sixCompactEncodeMultiplicity m) (sixCompactEncodeCover C) =
      (C.map fun s ↦ (m s).val).prod := by
  rw [sixCompactCoverValue]
  change
    sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
            (sixCompactEncodeCover C &&& 31) *
          sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
            (sixCompactEncodeCover C >>> 5 &&& 31) *
        sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
          (sixCompactEncodeCover C >>> 10 &&& 31) *
      sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
        (sixCompactEncodeCover C >>> 15 &&& 31) *
      sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
        (sixCompactEncodeCover C >>> 20 &&& 31) *
      sixCompactCoverSlotValue (sixCompactEncodeMultiplicity m)
        (sixCompactEncodeCover C >>> 25 &&& 31) =
      (C.map fun s ↦ (m s).val).prod
  rw [show sixCompactEncodeCover C >>> 5 &&& 31 =
        sixCompactCoverHeadSlot (C.drop 1) by
      rw [show sixCompactEncodeCover C >>> 5 = sixCompactEncodeCover (C.drop 1) by
        exact sixCompactEncodeCover_shiftRight C 1, sixCompactEncodeCover_land],
    show sixCompactEncodeCover C >>> 10 &&& 31 =
        sixCompactCoverHeadSlot (C.drop 2) by
      rw [show sixCompactEncodeCover C >>> 10 = sixCompactEncodeCover (C.drop 2) by
        exact sixCompactEncodeCover_shiftRight C 2, sixCompactEncodeCover_land],
    show sixCompactEncodeCover C >>> 15 &&& 31 =
        sixCompactCoverHeadSlot (C.drop 3) by
      rw [show sixCompactEncodeCover C >>> 15 = sixCompactEncodeCover (C.drop 3) by
        exact sixCompactEncodeCover_shiftRight C 3, sixCompactEncodeCover_land],
    show sixCompactEncodeCover C >>> 20 &&& 31 =
        sixCompactCoverHeadSlot (C.drop 4) by
      rw [show sixCompactEncodeCover C >>> 20 = sixCompactEncodeCover (C.drop 4) by
        exact sixCompactEncodeCover_shiftRight C 4, sixCompactEncodeCover_land],
    show sixCompactEncodeCover C >>> 25 &&& 31 =
        sixCompactCoverHeadSlot (C.drop 5) by
      rw [show sixCompactEncodeCover C >>> 25 = sixCompactEncodeCover (C.drop 5) by
        exact sixCompactEncodeCover_shiftRight C 5, sixCompactEncodeCover_land]]
  rcases C with _ | ⟨s0, C⟩
  · rfl
  rcases C with _ | ⟨s1, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
  rcases C with _ | ⟨s2, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
  rcases C with _ | ⟨s3, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
    ring
  rcases C with _ | ⟨s4, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
    ring
  rcases C with _ | ⟨s5, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
    ring
  rcases C with _ | ⟨s6, C⟩
  · simp [sixCompactCoverHeadSlot, sixCompactCoverSlotValue]
    ring
  simp at hLength
  omega

def sixCompletionGroupsValue (encoded : Nat) (groups : List (List Nat)) : Nat :=
  (groups.map fun group ↦ sixCompactCoverGroupValue encoded group).sum

theorem sixCompletionGroupsValue_eq_flatten
    (encoded : Nat) (groups : List (List Nat)) :
    sixCompletionGroupsValue encoded groups =
      (groups.flatten.map fun code ↦ sixCompactCoverValue encoded code).sum := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      simp only [sixCompletionGroupsValue, sixCompactCoverGroupValue, List.map_cons,
        List.sum_cons, List.flatten_cons, List.map_append, List.sum_append]
      exact congrArg (fun n ↦ sixCompactCoverGroupValue encoded group + n) ih

def sixGroupedByStage (stageCount : Nat) (xs : List (Nat × Option Nat)) :
    List (List Nat) :=
  (List.range stageCount).map fun stage ↦
    xs.filterMap fun x ↦ if x.2 = some stage then some x.1 else none

def sixStageValue (stage : Nat) (xs : List (Nat × Option Nat))
    (f : Nat → Nat) : Nat :=
  ((xs.filterMap fun x ↦ if x.2 = some stage then some x.1 else none).map f).sum

def sixGroupedValue (stageCount : Nat) (xs : List (Nat × Option Nat))
    (f : Nat → Nat) : Nat :=
  ((List.range stageCount).map fun stage ↦ sixStageValue stage xs f).sum

theorem sixGroupedByStage_sum_eq (stageCount : Nat)
    (xs : List (Nat × Option Nat)) (f : Nat → Nat) :
    ((sixGroupedByStage stageCount xs).flatten.map f).sum =
      sixGroupedValue stageCount xs f := by
  simp [sixGroupedByStage, sixGroupedValue, sixStageValue, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def]

theorem sixStageValue_cons (stage : Nat) (x : Nat × Option Nat)
    (xs : List (Nat × Option Nat)) (f : Nat → Nat) :
    sixStageValue stage (x :: xs) f =
      (if x.2 = some stage then f x.1 else 0) + sixStageValue stage xs f := by
  simp only [sixStageValue, List.filterMap_cons]
  split <;> simp_all

theorem sixGroupedValue_cons (stageCount : Nat) (x : Nat × Option Nat)
    (xs : List (Nat × Option Nat)) (f : Nat → Nat) :
    sixGroupedValue stageCount (x :: xs) f =
      ((List.range stageCount).map fun stage ↦
        if x.2 = some stage then f x.1 else 0).sum +
      sixGroupedValue stageCount xs f := by
  simp only [sixGroupedValue, sixStageValue_cons]
  exact List.sum_map_add

theorem sixStageIndicator_sum_le (stageCount value : Nat) (assigned : Option Nat) :
    ((List.range stageCount).map fun stage ↦
      if assigned = some stage then value else 0).sum ≤ value := by
  cases assigned with
  | none => simp
  | some assigned =>
      rw [← List.sum_toFinset _
        (List.nodup_range : (List.range stageCount).Nodup)]
      simp
      split <;> simp

theorem sixGroupedByStage_sum_le (stageCount : Nat)
    (xs : List (Nat × Option Nat)) (f : Nat → Nat) :
    ((sixGroupedByStage stageCount xs).flatten.map f).sum ≤
      (xs.map fun x ↦ f x.1).sum := by
  rw [sixGroupedByStage_sum_eq]
  induction xs with
  | nil => simp [sixGroupedValue, sixStageValue]
  | cons x xs ih =>
      rw [sixGroupedValue_cons]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (sixStageIndicator_sum_le stageCount (f x.1) x.2) ih

def sixCompletionGroupsFromStages
    (stageCount : Nat) (stages : List (Option Nat)) : List (List Nat) :=
  sixGroupedByStage stageCount (List.zip sixEncodedMinimalSupportCovers stages)

set_option maxRecDepth 1000000 in
theorem six_completion_groups_four_eq_stages :
    sixCompletionGroups4 = sixCompletionGroupsFromStages 18 sixCompletionStages4 := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_completion_groups_five_eq_stages :
    sixCompletionGroups5 = sixCompletionGroupsFromStages 20 sixCompletionStages5 := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_completion_groups_six_eq_stages :
    sixCompletionGroups6 = sixCompletionGroupsFromStages 21 sixCompletionStages6 := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_completion_data_four_codes :
    (List.zip sixEncodedMinimalSupportCovers sixCompletionStages4).map Prod.fst =
      sixEncodedMinimalSupportCovers := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_completion_data_five_codes :
    (List.zip sixEncodedMinimalSupportCovers sixCompletionStages5).map Prod.fst =
      sixEncodedMinimalSupportCovers := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_completion_data_six_codes :
    (List.zip sixEncodedMinimalSupportCovers sixCompletionStages6).map Prod.fst =
      sixEncodedMinimalSupportCovers := by
  rfl

set_option maxRecDepth 1000000 in
theorem six_encoded_minimal_support_covers_eq_map :
    sixEncodedMinimalSupportCovers =
      sixMinimalSupportCovers.map sixCompactEncodeCover := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed certificate checks all 562 cover lengths by kernel reduction.
theorem six_minimal_support_cover_lengths_le_six :
    sixMinimalSupportCovers.all (fun C ↦ decide (C.length ≤ 6)) = true := by
  decide

@[simp] theorem sixMultiplicityOfFunction_digit
    (m : Fin 21 → Fin 4) (s : Fin 21) :
    sixMultiplicityDigit (sixMultiplicityOfFunction m) s.val = (m s).val := by
  simp [sixMultiplicityDigit, sixMultiplicityOfFunction, Array.getD]

theorem sixList_sum_map_eq_of_all {α : Type*}
    (items : List α) (predicate : α → Bool) (hAll : items.all predicate = true)
    (left right : α → Nat)
    (hEqual : ∀ item, predicate item = true → left item = right item) :
    (items.map left).sum = (items.map right).sum := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      have hParts := Bool.and_eq_true_iff.mp hAll
      simp only [List.map_cons, List.sum_cons, hEqual item hParts.1, ih hParts.2]

theorem sixCompactCoverValue_encode_function
    (m : Fin 21 → Fin 4) (C : List SixSupportIndex) (hLength : C.length ≤ 6) :
    sixCompactCoverValue (sixCompactEncodeMultiplicity m) (sixCompactEncodeCover C) =
      (C.map fun s : SixSupportIndex ↦
        sixMultiplicityDigit (sixMultiplicityOfFunction m) s.val).prod := by
  rw [sixCompactCoverValue_encode m C hLength]
  apply congrArg List.prod
  apply List.map_congr_left
  intro s hs
  exact (sixMultiplicityOfFunction_digit m s).symm

set_option maxRecDepth 1000000 in
theorem six_encoded_cover_list_value
    (covers : List (List SixSupportIndex))
    (hLengths : covers.all (fun C ↦ decide (C.length ≤ 6)) = true)
    (m : Fin 21 → Fin 4) :
    ((covers.map sixCompactEncodeCover).map fun code ↦
      sixCompactCoverValue (sixCompactEncodeMultiplicity m) code).sum =
      (covers.map fun C ↦
        (C.map fun s : SixSupportIndex ↦
          sixMultiplicityDigit (sixMultiplicityOfFunction m) s.val).prod).sum := by
  rw [List.map_map]
  apply sixList_sum_map_eq_of_all covers
    (fun C ↦ decide (C.length ≤ 6)) hLengths
  intro C hLength
  simp only [Function.comp_apply]
  exact sixCompactCoverValue_encode_function m C (decide_eq_true_eq.mp hLength)

set_option maxRecDepth 1000000 in
theorem six_mapped_minimal_support_covers_value
    (m : Fin 21 → Fin 4) :
    ((sixMinimalSupportCovers.map sixCompactEncodeCover).map fun code ↦
      sixCompactCoverValue (sixCompactEncodeMultiplicity m) code).sum =
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  unfold sixWeightedCoverCount
  exact six_encoded_cover_list_value sixMinimalSupportCovers
    six_minimal_support_cover_lengths_le_six m

set_option maxRecDepth 1000000 in
theorem six_encoded_minimal_support_covers_value
    (m : Fin 21 → Fin 4) :
    (sixEncodedMinimalSupportCovers.map fun code ↦
      sixCompactCoverValue (sixCompactEncodeMultiplicity m) code).sum =
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  rw [six_encoded_minimal_support_covers_eq_map]
  exact six_mapped_minimal_support_covers_value m

theorem sixCompletionGroupsValue_le_weightedCoverCount
    (stageCount : Nat) (stages : List (Option Nat))
    (hCodes : (List.zip sixEncodedMinimalSupportCovers stages).map Prod.fst =
      sixEncodedMinimalSupportCovers)
    (m : Fin 21 → Fin 4) :
    sixCompletionGroupsValue (sixCompactEncodeMultiplicity m)
        (sixCompletionGroupsFromStages stageCount stages) ≤
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  rw [sixCompletionGroupsValue_eq_flatten]
  have hBound := sixGroupedByStage_sum_le stageCount
    (List.zip sixEncodedMinimalSupportCovers stages)
    (fun code ↦ sixCompactCoverValue (sixCompactEncodeMultiplicity m) code)
  have hMapped :
      (List.zip sixEncodedMinimalSupportCovers stages).map
          (fun x ↦ sixCompactCoverValue (sixCompactEncodeMultiplicity m) x.1) =
        sixEncodedMinimalSupportCovers.map
          (fun code ↦ sixCompactCoverValue (sixCompactEncodeMultiplicity m) code) := by
    calc
      _ = ((List.zip sixEncodedMinimalSupportCovers stages).map Prod.fst).map
          (fun code ↦ sixCompactCoverValue (sixCompactEncodeMultiplicity m) code) := by
            rw [List.map_map]
            apply congrArg (fun f : Nat × Option Nat → Nat ↦
              (List.zip sixEncodedMinimalSupportCovers stages).map f)
            funext x
            rfl
      _ = _ := congrArg
        (List.map fun code ↦ sixCompactCoverValue (sixCompactEncodeMultiplicity m) code)
        hCodes
  rw [hMapped] at hBound
  exact hBound.trans_eq (six_encoded_minimal_support_covers_value m)

theorem sixCompletionGroups4_value_le_weightedCoverCount
    (m : Fin 21 → Fin 4) :
    sixCompletionGroupsValue (sixCompactEncodeMultiplicity m) sixCompletionGroups4 ≤
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  rw [six_completion_groups_four_eq_stages]
  exact sixCompletionGroupsValue_le_weightedCoverCount 18 sixCompletionStages4
    six_completion_data_four_codes m

theorem sixCompletionGroups5_value_le_weightedCoverCount
    (m : Fin 21 → Fin 4) :
    sixCompletionGroupsValue (sixCompactEncodeMultiplicity m) sixCompletionGroups5 ≤
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  rw [six_completion_groups_five_eq_stages]
  exact sixCompletionGroupsValue_le_weightedCoverCount 20 sixCompletionStages5
    six_completion_data_five_codes m

theorem sixCompletionGroups6_value_le_weightedCoverCount
    (m : Fin 21 → Fin 4) :
    sixCompletionGroupsValue (sixCompactEncodeMultiplicity m) sixCompletionGroups6 ≤
      sixWeightedCoverCount (sixMultiplicityOfFunction m) := by
  rw [six_completion_groups_six_eq_stages]
  exact sixCompletionGroupsValue_le_weightedCoverCount 21 sixCompletionStages6
    six_completion_data_six_codes m

end AiMathLab.P0054.G417
