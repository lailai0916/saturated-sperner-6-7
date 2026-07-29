import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00818
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01178
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01179

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into bounded branches.
theorem middle_four_classification_mask_01179 :
    middleFourClassificationMaskCheck 1179 = true := by
  apply middleFourClassificationMaskCheck_of_two_prefixes
    1179 0 1 [3, 4, 7, 10] rfl rfl
  intro k hk l hl
  have hAdmissible : middleFourTwoPrefixAdmissible 1179 k l = true := by
    simp only [middleFourTwoPrefixAdmissible]
    rw [show fourMaskSupports 1179 = [0, 1, 3, 4, 7, 10] by rfl]
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
      middle_four_classification_prefixes_01179 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 1 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 2 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 3 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 4 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 5 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact middleFourClassificationValuesCheck_of_list
      middle_four_classification_prefixes_01179 (by decide)
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 6 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 7 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 8 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 7 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 8 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      middleFourTwoPrefixAdmissible 1179 9 9 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.MiddleSevenNineFinite
