import AiMathLab.P0054G419.KernelAClassificationPrefix0081611
import AiMathLab.P0054G419.KernelAClassificationPrefix0081612
import AiMathLab.P0054G419.KernelAClassificationPrefix0081613
import AiMathLab.P0054G419.KernelAClassificationPrefix0081614
import AiMathLab.P0054G419.KernelAClassificationPrefix0081615
import AiMathLab.P0054G419.KernelAClassificationPrefix0081621
import AiMathLab.P0054G419.KernelAClassificationPrefix0081622
import AiMathLab.P0054G419.KernelAClassificationPrefix0081623
import AiMathLab.P0054G419.KernelAClassificationPrefix0081624
import AiMathLab.P0054G419.KernelAClassificationPrefix0081631
import AiMathLab.P0054G419.KernelAClassificationPrefix0081632
import AiMathLab.P0054G419.KernelAClassificationPrefix0081633
import AiMathLab.P0054G419.KernelAClassificationPrefix0081641
import AiMathLab.P0054G419.KernelAClassificationPrefix0081642
import AiMathLab.P0054G419.KernelAClassificationPrefix0081651

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_00816 :
    fourKernelAClassificationMaskCheck 816 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    816 4 5 [8, 9] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 816 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 816 = [4, 5, 8, 9] by rfl]
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
  · exact four_kernel_a_classification_prefix_00816_1_1
  · exact four_kernel_a_classification_prefix_00816_1_2
  · exact four_kernel_a_classification_prefix_00816_1_3
  · exact four_kernel_a_classification_prefix_00816_1_4
  · exact four_kernel_a_classification_prefix_00816_1_5
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00816_2_1
  · exact four_kernel_a_classification_prefix_00816_2_2
  · exact four_kernel_a_classification_prefix_00816_2_3
  · exact four_kernel_a_classification_prefix_00816_2_4
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00816_3_1
  · exact four_kernel_a_classification_prefix_00816_3_2
  · exact four_kernel_a_classification_prefix_00816_3_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00816_4_1
  · exact four_kernel_a_classification_prefix_00816_4_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00816_5_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 816 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
