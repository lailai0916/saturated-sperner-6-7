import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00490
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00653

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into bounded branches.
theorem middle_four_classification_mask_00653 :
    middleFourClassificationMaskCheck 653 = true := by
  apply middleFourClassificationMaskCheck_of_two_prefixes
    653 0 2 [3, 7, 9] rfl rfl
  intro k hk l hl
  have hAdmissible : middleFourTwoPrefixAdmissible 653 k l = true := by
    simp only [middleFourTwoPrefixAdmissible]
    rw [show fourMaskSupports 653 = [0, 2, 3, 7, 9] by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ 9 := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ 9 := by
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
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 1 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 1 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 1 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 2 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 3 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 4 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 5 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 6 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_00653 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 7 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 8 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 653 9 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.MiddleSevenNineFinite
