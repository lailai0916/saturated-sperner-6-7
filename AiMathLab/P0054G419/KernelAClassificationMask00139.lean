import AiMathLab.P0054G419.KernelAClassificationPrefix0013911
import AiMathLab.P0054G419.KernelAClassificationPrefix0013912
import AiMathLab.P0054G419.KernelAClassificationPrefix0013913
import AiMathLab.P0054G419.KernelAClassificationPrefix0013914
import AiMathLab.P0054G419.KernelAClassificationPrefix0013915
import AiMathLab.P0054G419.KernelAClassificationPrefix0013916
import AiMathLab.P0054G419.KernelAClassificationPrefix0013921
import AiMathLab.P0054G419.KernelAClassificationPrefix0013922
import AiMathLab.P0054G419.KernelAClassificationPrefix0013923
import AiMathLab.P0054G419.KernelAClassificationPrefix0013931
import AiMathLab.P0054G419.KernelAClassificationPrefix0013932
import AiMathLab.P0054G419.KernelAClassificationPrefix0013941
import AiMathLab.P0054G419.KernelAClassificationPrefix0013951
import AiMathLab.P0054G419.KernelAClassificationPrefix0013961

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Two fixed digits split a wide multiplicity tree into kernel-reducible branches.
theorem four_kernel_a_classification_mask_00139 :
    fourKernelAClassificationMaskCheck 139 = true := by
  apply fourKernelAClassificationMaskCheck_of_two_prefixes
    139 0 1 [3, 7] rfl rfl
  intro k hk l hl
  have hAdmissible : fourKernelATwoPrefixAdmissible 139 k l = true := by
    simp only [fourKernelATwoPrefixAdmissible]
    rw [show fourMaskSupports 139 = [0, 1, 3, 7] by rfl]
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
  · exact four_kernel_a_classification_prefix_00139_1_1
  · exact four_kernel_a_classification_prefix_00139_1_2
  · exact four_kernel_a_classification_prefix_00139_1_3
  · exact four_kernel_a_classification_prefix_00139_1_4
  · exact four_kernel_a_classification_prefix_00139_1_5
  · exact four_kernel_a_classification_prefix_00139_1_6
  · exact four_kernel_a_classification_prefix_00139_2_1
  · exact four_kernel_a_classification_prefix_00139_2_2
  · exact four_kernel_a_classification_prefix_00139_2_3
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 2 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 2 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 2 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00139_3_1
  · exact four_kernel_a_classification_prefix_00139_3_2
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 3 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 3 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 3 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 3 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00139_4_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 4 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 4 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 4 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 4 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 4 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00139_5_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 5 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 5 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 5 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 5 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 5 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · exact four_kernel_a_classification_prefix_00139_6_1
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 6 2 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 6 3 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 6 4 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 6 5 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction
  · have hFalse :
      fourKernelATwoPrefixAdmissible 139 6 6 = false := by rfl
    rw [hFalse] at hAdmissible
    contradiction

end AiMathLab.P0054.G419
