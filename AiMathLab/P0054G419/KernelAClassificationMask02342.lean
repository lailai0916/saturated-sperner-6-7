import AiMathLab.P0054G419.KernelAClassificationPrefix0234211
import AiMathLab.P0054G419.KernelAClassificationPrefix0234212
import AiMathLab.P0054G419.KernelAClassificationPrefix0234213
import AiMathLab.P0054G419.KernelAClassificationPrefix0234214
import AiMathLab.P0054G419.KernelAClassificationPrefix0234221
import AiMathLab.P0054G419.KernelAClassificationPrefix0234222
import AiMathLab.P0054G419.KernelAClassificationPrefix0234223
import AiMathLab.P0054G419.KernelAClassificationPrefix0234231
import AiMathLab.P0054G419.KernelAClassificationPrefix0234232
import AiMathLab.P0054G419.KernelAClassificationPrefix0234241

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_02342 :
    fourKernelAClassificationMaskCheck 2342 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    2342 1 2 [5, 8, 11] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 2342 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 2342 = [1, 2, 5, 8, 11] by rfl]
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
  · exact four_kernel_a_classification_prefix_02342_1_1
  · exact four_kernel_a_classification_prefix_02342_1_2
  · exact four_kernel_a_classification_prefix_02342_1_3
  · exact four_kernel_a_classification_prefix_02342_1_4
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 1 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 1 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02342_2_1
  · exact four_kernel_a_classification_prefix_02342_2_2
  · exact four_kernel_a_classification_prefix_02342_2_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02342_3_1
  · exact four_kernel_a_classification_prefix_02342_3_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_02342_4_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 1 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 2342 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
