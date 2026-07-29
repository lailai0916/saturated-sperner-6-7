import AiMathLab.P0054G419.KernelAClassificationPrefix0081711
import AiMathLab.P0054G419.KernelAClassificationPrefix0081712
import AiMathLab.P0054G419.KernelAClassificationPrefix0081713
import AiMathLab.P0054G419.KernelAClassificationPrefix0081714
import AiMathLab.P0054G419.KernelAClassificationPrefix0081721
import AiMathLab.P0054G419.KernelAClassificationPrefix0081722
import AiMathLab.P0054G419.KernelAClassificationPrefix0081723
import AiMathLab.P0054G419.KernelAClassificationPrefix0081731
import AiMathLab.P0054G419.KernelAClassificationPrefix0081732
import AiMathLab.P0054G419.KernelAClassificationPrefix0081741

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_00817 :
    fourKernelAClassificationMaskCheck 817 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    817 0 4 [5, 8, 9] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 817 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 817 = [0, 4, 5, 8, 9] by rfl]
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
  · exact four_kernel_a_classification_prefix_00817_1_1
  · exact four_kernel_a_classification_prefix_00817_1_2
  · exact four_kernel_a_classification_prefix_00817_1_3
  · exact four_kernel_a_classification_prefix_00817_1_4
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00817_2_1
  · exact four_kernel_a_classification_prefix_00817_2_2
  · exact four_kernel_a_classification_prefix_00817_2_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00817_3_1
  · exact four_kernel_a_classification_prefix_00817_3_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00817_4_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 817 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
