import AiMathLab.P0054G419.KernelAClassificationPrefix0077911
import AiMathLab.P0054G419.KernelAClassificationPrefix0077912
import AiMathLab.P0054G419.KernelAClassificationPrefix0077913
import AiMathLab.P0054G419.KernelAClassificationPrefix0077914
import AiMathLab.P0054G419.KernelAClassificationPrefix0077921
import AiMathLab.P0054G419.KernelAClassificationPrefix0077922
import AiMathLab.P0054G419.KernelAClassificationPrefix0077923
import AiMathLab.P0054G419.KernelAClassificationPrefix0077931
import AiMathLab.P0054G419.KernelAClassificationPrefix0077932
import AiMathLab.P0054G419.KernelAClassificationPrefix0077941

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_00779 :
    fourKernelAClassificationMaskCheck 779 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    779 0 1 [3, 8, 9] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 779 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 779 = [0, 1, 3, 8, 9] by rfl]
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
  · exact four_kernel_a_classification_prefix_00779_1_1
  · exact four_kernel_a_classification_prefix_00779_1_2
  · exact four_kernel_a_classification_prefix_00779_1_3
  · exact four_kernel_a_classification_prefix_00779_1_4
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00779_2_1
  · exact four_kernel_a_classification_prefix_00779_2_2
  · exact four_kernel_a_classification_prefix_00779_2_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00779_3_1
  · exact four_kernel_a_classification_prefix_00779_3_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00779_4_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 779 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
