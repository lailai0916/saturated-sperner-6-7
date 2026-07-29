import AiMathLab.P0054G420.MiddleFourClassificationPrefixes00219

namespace AiMathLab.P0054.G420

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into bounded branches.
theorem middle_four_classification_mask_00219 :
    middleFourClassificationMaskCheck 219 = true := by
  apply middleFourClassificationMaskCheck_of_two_prefixes
    219 0 1 [3, 4, 6, 7] rfl rfl
  intro k hk l hl
  have hAdmissible : middleFourTwoPrefixAdmissible 219 k l = true := by
    simp only [middleFourTwoPrefixAdmissible]
    rw [show fourMaskSupports 219 = [0, 1, 3, 4, 6, 7] by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ 8 := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ 8 := by
    have hlRange := (List.mem_filter.mp hl).1
    simp only [List.mem_map, List.mem_range] at hlRange
    obtain ⟨n, hn, rfl⟩ := hlRange
    omega
  have hkLower := hkBounds.1
  have hkUpper := hkBounds.2
  have hlLower := hlBounds.1
  have hlUpper := hlBounds.2
  interval_cases k <;> interval_cases l
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 1 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 1 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 1 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 2 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 3 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 4 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 5 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00219 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 6 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 7 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 219 8 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G420
