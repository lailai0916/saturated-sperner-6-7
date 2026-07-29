/-
Copyright (c) 2026 AI Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhi Chen
-/
import AiMathLab.P0054Size55WitnessBlocks

/-! # Kernel-checked certificate for the P0054 size-55 construction -/

namespace AiMathLab.P0054

open AiMathLab.SaturatedSperner

/-- The 32 checked blocks cover every eleven-bit mask. -/
private theorem size55_witness_masks_complete (m : Nat) (hm : m < 2048) :
    let S := maskSubset m
    S ∈ size55 ∨ HasStrictChainLength 8 (insert S size55) := by
  by_cases h00 : m < 64
  · have h := size55_witness_block_00 ⟨m - 0, by omega⟩
    have heq : 0 + (m - 0) = m := by omega
    simpa only [heq] using h
  by_cases h01 : m < 128
  · have h := size55_witness_block_01 ⟨m - 64, by omega⟩
    have heq : 64 + (m - 64) = m := by omega
    simpa only [heq] using h
  by_cases h02 : m < 192
  · have h := size55_witness_block_02 ⟨m - 128, by omega⟩
    have heq : 128 + (m - 128) = m := by omega
    simpa only [heq] using h
  by_cases h03 : m < 256
  · have h := size55_witness_block_03 ⟨m - 192, by omega⟩
    have heq : 192 + (m - 192) = m := by omega
    simpa only [heq] using h
  by_cases h04 : m < 320
  · have h := size55_witness_block_04 ⟨m - 256, by omega⟩
    have heq : 256 + (m - 256) = m := by omega
    simpa only [heq] using h
  by_cases h05 : m < 384
  · have h := size55_witness_block_05 ⟨m - 320, by omega⟩
    have heq : 320 + (m - 320) = m := by omega
    simpa only [heq] using h
  by_cases h06 : m < 448
  · have h := size55_witness_block_06 ⟨m - 384, by omega⟩
    have heq : 384 + (m - 384) = m := by omega
    simpa only [heq] using h
  by_cases h07 : m < 512
  · have h := size55_witness_block_07 ⟨m - 448, by omega⟩
    have heq : 448 + (m - 448) = m := by omega
    simpa only [heq] using h
  by_cases h08 : m < 576
  · have h := size55_witness_block_08 ⟨m - 512, by omega⟩
    have heq : 512 + (m - 512) = m := by omega
    simpa only [heq] using h
  by_cases h09 : m < 640
  · have h := size55_witness_block_09 ⟨m - 576, by omega⟩
    have heq : 576 + (m - 576) = m := by omega
    simpa only [heq] using h
  by_cases h10 : m < 704
  · have h := size55_witness_block_10 ⟨m - 640, by omega⟩
    have heq : 640 + (m - 640) = m := by omega
    simpa only [heq] using h
  by_cases h11 : m < 768
  · have h := size55_witness_block_11 ⟨m - 704, by omega⟩
    have heq : 704 + (m - 704) = m := by omega
    simpa only [heq] using h
  by_cases h12 : m < 832
  · have h := size55_witness_block_12 ⟨m - 768, by omega⟩
    have heq : 768 + (m - 768) = m := by omega
    simpa only [heq] using h
  by_cases h13 : m < 896
  · have h := size55_witness_block_13 ⟨m - 832, by omega⟩
    have heq : 832 + (m - 832) = m := by omega
    simpa only [heq] using h
  by_cases h14 : m < 960
  · have h := size55_witness_block_14 ⟨m - 896, by omega⟩
    have heq : 896 + (m - 896) = m := by omega
    simpa only [heq] using h
  by_cases h15 : m < 1024
  · have h := size55_witness_block_15 ⟨m - 960, by omega⟩
    have heq : 960 + (m - 960) = m := by omega
    simpa only [heq] using h
  by_cases h16 : m < 1088
  · have h := size55_witness_block_16 ⟨m - 1024, by omega⟩
    have heq : 1024 + (m - 1024) = m := by omega
    simpa only [heq] using h
  by_cases h17 : m < 1152
  · have h := size55_witness_block_17 ⟨m - 1088, by omega⟩
    have heq : 1088 + (m - 1088) = m := by omega
    simpa only [heq] using h
  by_cases h18 : m < 1216
  · have h := size55_witness_block_18 ⟨m - 1152, by omega⟩
    have heq : 1152 + (m - 1152) = m := by omega
    simpa only [heq] using h
  by_cases h19 : m < 1280
  · have h := size55_witness_block_19 ⟨m - 1216, by omega⟩
    have heq : 1216 + (m - 1216) = m := by omega
    simpa only [heq] using h
  by_cases h20 : m < 1344
  · have h := size55_witness_block_20 ⟨m - 1280, by omega⟩
    have heq : 1280 + (m - 1280) = m := by omega
    simpa only [heq] using h
  by_cases h21 : m < 1408
  · have h := size55_witness_block_21 ⟨m - 1344, by omega⟩
    have heq : 1344 + (m - 1344) = m := by omega
    simpa only [heq] using h
  by_cases h22 : m < 1472
  · have h := size55_witness_block_22 ⟨m - 1408, by omega⟩
    have heq : 1408 + (m - 1408) = m := by omega
    simpa only [heq] using h
  by_cases h23 : m < 1536
  · have h := size55_witness_block_23 ⟨m - 1472, by omega⟩
    have heq : 1472 + (m - 1472) = m := by omega
    simpa only [heq] using h
  by_cases h24 : m < 1600
  · have h := size55_witness_block_24 ⟨m - 1536, by omega⟩
    have heq : 1536 + (m - 1536) = m := by omega
    simpa only [heq] using h
  by_cases h25 : m < 1664
  · have h := size55_witness_block_25 ⟨m - 1600, by omega⟩
    have heq : 1600 + (m - 1600) = m := by omega
    simpa only [heq] using h
  by_cases h26 : m < 1728
  · have h := size55_witness_block_26 ⟨m - 1664, by omega⟩
    have heq : 1664 + (m - 1664) = m := by omega
    simpa only [heq] using h
  by_cases h27 : m < 1792
  · have h := size55_witness_block_27 ⟨m - 1728, by omega⟩
    have heq : 1728 + (m - 1728) = m := by omega
    simpa only [heq] using h
  by_cases h28 : m < 1856
  · have h := size55_witness_block_28 ⟨m - 1792, by omega⟩
    have heq : 1792 + (m - 1792) = m := by omega
    simpa only [heq] using h
  by_cases h29 : m < 1920
  · have h := size55_witness_block_29 ⟨m - 1856, by omega⟩
    have heq : 1856 + (m - 1856) = m := by omega
    simpa only [heq] using h
  by_cases h30 : m < 1984
  · have h := size55_witness_block_30 ⟨m - 1920, by omega⟩
    have heq : 1920 + (m - 1920) = m := by omega
    simpa only [heq] using h
  have h := size55_witness_block_31 ⟨m - 1984, by omega⟩
  have heq : 1984 + (m - 1984) = m := by omega
  simpa only [heq] using h

private theorem size55_witnesses_complete :
    ∀ S : GroundSubset,
      S ∈ size55 ∨ HasStrictChainLength 8 (insert S size55) := by
  intro S
  have h := size55_witness_masks_complete
    (subsetMask S) (subsetMask_lt_2048 S)
  simpa only [maskSubset_subsetMask] using h

/-- The explicit 55-member family is saturated 7-Sperner. -/
theorem size55_saturated : IsSaturatedKSperner 7 size55 := by
  refine ⟨size55_seven_sperner, ?_⟩
  intro S hSF
  exact (size55_witnesses_complete S).resolve_left hSF

/-- The complete finite certificate for the 55-member construction. -/
theorem size55_full_certificate :
    size55.card = 55 ∧ IsSaturatedKSperner 7 size55 :=
  ⟨size55_card, size55_saturated⟩

end AiMathLab.P0054
