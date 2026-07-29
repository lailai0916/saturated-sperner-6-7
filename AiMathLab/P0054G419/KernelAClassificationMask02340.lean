import AiMathLab.P0054G419.KernelAClassificationPrefix0234011
import AiMathLab.P0054G419.KernelAClassificationPrefix0234012
import AiMathLab.P0054G419.KernelAClassificationPrefix0234013
import AiMathLab.P0054G419.KernelAClassificationPrefix0234014
import AiMathLab.P0054G419.KernelAClassificationPrefix0234015
import AiMathLab.P0054G419.KernelAClassificationPrefix0234021
import AiMathLab.P0054G419.KernelAClassificationPrefix0234022
import AiMathLab.P0054G419.KernelAClassificationPrefix0234023
import AiMathLab.P0054G419.KernelAClassificationPrefix0234024
import AiMathLab.P0054G419.KernelAClassificationPrefix0234031
import AiMathLab.P0054G419.KernelAClassificationPrefix0234032
import AiMathLab.P0054G419.KernelAClassificationPrefix0234033
import AiMathLab.P0054G419.KernelAClassificationPrefix0234041
import AiMathLab.P0054G419.KernelAClassificationPrefix0234042
import AiMathLab.P0054G419.KernelAClassificationPrefix0234051

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_02340 :
    fourKernelAClassificationMaskCheck 2340 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    2340 2 5 [8, 11] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 2340 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 2340 = [2, 5, 8, 11] by rfl]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hk, decide_eq_true hl⟩
  have hkBounds : 1 ≤ k ∧ k ≤ 6 := by
    have hkRange := (List.mem_filter.mp hk).1
    simp only [List.mem_map, List.mem_range] at hkRange
    obtain ⟨n, hn, rfl⟩ := hkRange
    omega
  have hlBounds : 1 ≤ l ∧ l ≤ 6 := by
    have hlRange := (List.mem_filter.mp hl).1
    simp only [List.mem_map, List.mem_range] at hlRange
    obtain ⟨n, hn, rfl⟩ := hlRange
    omega
  have hkLower := hkBounds.1
  have hkUpper := hkBounds.2
  have hlLower := hlBounds.1
  have hlUpper := hlBounds.2
  interval_cases k <;> interval_cases l
  · exact four_kernel_a_classification_prefix_02340_1_1
  · exact four_kernel_a_classification_prefix_02340_1_2
  · exact four_kernel_a_classification_prefix_02340_1_3
  · exact four_kernel_a_classification_prefix_02340_1_4
  · exact four_kernel_a_classification_prefix_02340_1_5
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02340_2_1
  · exact four_kernel_a_classification_prefix_02340_2_2
  · exact four_kernel_a_classification_prefix_02340_2_3
  · exact four_kernel_a_classification_prefix_02340_2_4
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02340_3_1
  · exact four_kernel_a_classification_prefix_02340_3_2
  · exact four_kernel_a_classification_prefix_02340_3_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02340_4_1
  · exact four_kernel_a_classification_prefix_02340_4_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02340_5_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2340 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
