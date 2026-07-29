import AiMathLab.P0054G415.DegreeThree
import Mathlib

namespace AiMathLab.P0054.G416

open scoped BigOperators

abbrev FiveVertex := Fin 5

abbrev FiveSupportIndex := Fin 15

abbrev FiveMultiplicity := Array Nat

def fiveMultiplicityDigit (m : FiveMultiplicity) (s : Nat) : Nat :=
  m.getD s 0

abbrev FiveDegreeState := Array Nat

def fiveSupport : FiveSupportIndex → Finset FiveVertex
  | ⟨0, _⟩ => {0}
  | ⟨1, _⟩ => {1}
  | ⟨2, _⟩ => {2}
  | ⟨3, _⟩ => {3}
  | ⟨4, _⟩ => {4}
  | ⟨5, _⟩ => {0, 1}
  | ⟨6, _⟩ => {0, 2}
  | ⟨7, _⟩ => {0, 3}
  | ⟨8, _⟩ => {0, 4}
  | ⟨9, _⟩ => {1, 2}
  | ⟨10, _⟩ => {1, 3}
  | ⟨11, _⟩ => {1, 4}
  | ⟨12, _⟩ => {2, 3}
  | ⟨13, _⟩ => {2, 4}
  | ⟨14, _⟩ => {3, 4}
  | ⟨n + 15, h⟩ => by omega

def fiveSupportCovers (C : Finset FiveSupportIndex) : Prop :=
  ∀ v : FiveVertex, ∃ s ∈ C, v ∈ fiveSupport s

def fiveMinimalSupportCover (C : Finset FiveSupportIndex) : Prop :=
  fiveSupportCovers C ∧ ∀ s ∈ C, ¬ fiveSupportCovers (C.erase s)

instance (C : Finset FiveSupportIndex) : Decidable (fiveSupportCovers C) := by
  unfold fiveSupportCovers
  infer_instance

instance (C : Finset FiveSupportIndex) : Decidable (fiveMinimalSupportCover C) := by
  unfold fiveMinimalSupportCover
  infer_instance

def fiveMinimalSupportCovers : List (List FiveSupportIndex) :=
  [
    [0, 9, 14],
    [0, 10, 13],
    [0, 11, 12],
    [1, 6, 14],
    [1, 7, 13],
    [1, 8, 12],
    [2, 5, 14],
    [2, 7, 11],
    [2, 8, 10],
    [3, 5, 13],
    [3, 6, 11],
    [3, 8, 9],
    [4, 5, 12],
    [4, 6, 10],
    [4, 7, 9],
    [5, 6, 14],
    [5, 7, 13],
    [5, 8, 12],
    [5, 9, 14],
    [5, 10, 13],
    [5, 11, 12],
    [5, 12, 13],
    [5, 12, 14],
    [5, 13, 14],
    [6, 7, 11],
    [6, 8, 10],
    [6, 9, 14],
    [6, 10, 11],
    [6, 10, 13],
    [6, 10, 14],
    [6, 11, 12],
    [6, 11, 14],
    [7, 8, 9],
    [7, 9, 11],
    [7, 9, 13],
    [7, 9, 14],
    [7, 10, 13],
    [7, 11, 12],
    [7, 11, 13],
    [8, 9, 10],
    [8, 9, 12],
    [8, 9, 14],
    [8, 10, 12],
    [8, 10, 13],
    [8, 11, 12],
    [0, 1, 2, 14],
    [0, 1, 3, 13],
    [0, 1, 4, 12],
    [0, 1, 12, 13],
    [0, 1, 12, 14],
    [0, 1, 13, 14],
    [0, 2, 3, 11],
    [0, 2, 4, 10],
    [0, 2, 10, 11],
    [0, 2, 10, 14],
    [0, 2, 11, 14],
    [0, 3, 4, 9],
    [0, 3, 9, 11],
    [0, 3, 9, 13],
    [0, 3, 11, 13],
    [0, 4, 9, 10],
    [0, 4, 9, 12],
    [0, 4, 10, 12],
    [0, 9, 10, 11],
    [0, 9, 12, 13],
    [0, 10, 12, 14],
    [0, 11, 13, 14],
    [1, 2, 3, 8],
    [1, 2, 4, 7],
    [1, 2, 7, 8],
    [1, 2, 7, 14],
    [1, 2, 8, 14],
    [1, 3, 4, 6],
    [1, 3, 6, 8],
    [1, 3, 6, 13],
    [1, 3, 8, 13],
    [1, 4, 6, 7],
    [1, 4, 6, 12],
    [1, 4, 7, 12],
    [1, 6, 7, 8],
    [1, 6, 12, 13],
    [1, 7, 12, 14],
    [1, 8, 13, 14],
    [2, 3, 4, 5],
    [2, 3, 5, 8],
    [2, 3, 5, 11],
    [2, 3, 8, 11],
    [2, 4, 5, 7],
    [2, 4, 5, 10],
    [2, 4, 7, 10],
    [2, 5, 7, 8],
    [2, 5, 10, 11],
    [2, 7, 10, 14],
    [2, 8, 11, 14],
    [3, 4, 5, 6],
    [3, 4, 5, 9],
    [3, 4, 6, 9],
    [3, 5, 6, 8],
    [3, 5, 9, 11],
    [3, 6, 9, 13],
    [3, 8, 11, 13],
    [4, 5, 6, 7],
    [4, 5, 9, 10],
    [4, 6, 9, 12],
    [4, 7, 10, 12],
    [5, 6, 7, 8],
    [5, 9, 10, 11],
    [6, 9, 12, 13],
    [7, 10, 12, 14],
    [8, 11, 13, 14],
    [0, 1, 2, 3, 4]
  ]

def fiveWeightedCoverCount (m : FiveMultiplicity) : Nat :=
  (fiveMinimalSupportCovers.map fun C ↦
    (C.map fun s ↦ fiveMultiplicityDigit m s).prod).sum

def fiveSupportDegree (m : FiveMultiplicity) (v : FiveVertex) : Nat :=
  ∑ s : FiveSupportIndex,
    if v ∈ fiveSupport s then fiveMultiplicityDigit m s.val else 0

def fiveSupportTouchesLow (lowCount : Nat) (s : FiveSupportIndex) : Prop :=
  ∃ v ∈ fiveSupport s, v.val < lowCount

instance (lowCount : Nat) (s : FiveSupportIndex) :
    Decidable (fiveSupportTouchesLow lowCount s) := by
  unfold fiveSupportTouchesLow
  infer_instance

def FiveMultiplicityValid (lowCount : Nat) (m : FiveMultiplicity) : Prop :=
  (∀ v : FiveVertex, if v.val < lowCount then fiveSupportDegree m v = 3
    else 4 ≤ fiveSupportDegree m v) ∧
  ∀ s : FiveSupportIndex, 0 < fiveMultiplicityDigit m s.val →
    fiveSupportTouchesLow lowCount s

instance (lowCount : Nat) (m : FiveMultiplicity) :
    Decidable (FiveMultiplicityValid lowCount m) := by
  unfold FiveMultiplicityValid
  infer_instance

def fiveMultiplicityZero : FiveMultiplicity := Array.replicate 15 0

def fiveDegreeStateZero : FiveDegreeState := Array.replicate 5 0

def fiveSupportMask : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 3
  | 6 => 5
  | 7 => 9
  | 8 => 17
  | 9 => 6
  | 10 => 10
  | 11 => 18
  | 12 => 12
  | 13 => 20
  | 14 => 24
  | _ => 0

def fiveSupportContains (s v : Nat) : Bool :=
  (fiveSupportMask s).testBit v

def fiveSupportTouchesLowBool (lowCount s : Nat) : Bool :=
  (List.range lowCount).any fun v ↦ fiveSupportContains s v

def addFiveSupportDegree
    (degrees : FiveDegreeState) (s k : Nat) : FiveDegreeState :=
  Array.ofFn fun v : FiveVertex ↦
    degrees.getD v.val 0 + if fiveSupportContains s v.val then k else 0

def fiveDegreeStateValidBool (lowCount : Nat) (degrees : FiveDegreeState) : Bool :=
  (List.range 5).all fun v ↦
    if v < lowCount then decide (degrees.getD v 0 = 3)
    else decide (4 ≤ degrees.getD v 0)

def fiveMultiplicityChoices
    (lowCount : Nat) (degrees : FiveDegreeState) (s : Nat) : List Nat :=
  (List.range 4).filter fun k ↦
    (decide (k = 0) || fiveSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !fiveSupportContains s v || decide (degrees.getD v 0 + k ≤ 3)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_minimal_support_covers_length : fiveMinimalSupportCovers.length = 111 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_minimal_support_covers_sound_check :
    fiveMinimalSupportCovers.all (fun C ↦ decide (fiveMinimalSupportCover C.toFinset)) =
      true := by
  decide

theorem five_minimal_support_covers_sound {C : List FiveSupportIndex}
    (hC : C ∈ fiveMinimalSupportCovers) : fiveMinimalSupportCover C.toFinset := by
  have hCheck := five_minimal_support_covers_sound_check
  simp only [List.all_eq_true, decide_eq_true_eq] at hCheck
  exact hCheck C hC

def fiveSupportMultigraphCheckAux
    (lowCount minimum : Nat) : List Nat → FiveMultiplicity → FiveDegreeState → Bool
  | [], m, degrees =>
      if fiveDegreeStateValidBool lowCount degrees then
        decide (minimum ≤ fiveWeightedCoverCount m)
      else true
  | s :: supports, m, degrees =>
      (fiveMultiplicityChoices lowCount degrees s).all fun k ↦
        fiveSupportMultigraphCheckAux lowCount minimum supports (m.set! s k)
          (addFiveSupportDegree degrees s k)

def fiveSupportMultigraphBranchCheck (lowCount minimum : Nat) : Bool :=
  fiveSupportMultigraphCheckAux lowCount minimum (List.range 15)
    fiveMultiplicityZero fiveDegreeStateZero

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-
theorem five_support_multigraph_low_three_certificate :
    fiveSupportMultigraphBranchCheck 3 19 = true := by
  decide
-/

def fiveMultiplicityAfterThree (a b c : Nat) : FiveMultiplicity :=
  ((fiveMultiplicityZero.set! 0 a).set! 1 b).set! 2 c

def fiveDegreeStateAfterThree (a b c : Nat) : FiveDegreeState :=
  #[(a : Nat), b, c, 0, 0]

def fiveSupportMultigraphLowThreeSubcheck (a b c : Nat) : Bool :=
  fiveSupportMultigraphCheckAux 3 19 ((List.range 15).drop 3)
    (fiveMultiplicityAfterThree a b c) (fiveDegreeStateAfterThree a b c)

def fiveSupportMultigraphLowThreeSplitCheck : Bool :=
  (List.range 4).all fun a ↦
    (List.range 4).all fun b ↦
      (List.range 4).all fun c ↦ fiveSupportMultigraphLowThreeSubcheck a b c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_000 :
    fiveSupportMultigraphLowThreeSubcheck 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_001 :
    fiveSupportMultigraphLowThreeSubcheck 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_002 :
    fiveSupportMultigraphLowThreeSubcheck 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_003 :
    fiveSupportMultigraphLowThreeSubcheck 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_010 :
    fiveSupportMultigraphLowThreeSubcheck 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_011 :
    fiveSupportMultigraphLowThreeSubcheck 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_012 :
    fiveSupportMultigraphLowThreeSubcheck 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_013 :
    fiveSupportMultigraphLowThreeSubcheck 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_020 :
    fiveSupportMultigraphLowThreeSubcheck 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_021 :
    fiveSupportMultigraphLowThreeSubcheck 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_022 :
    fiveSupportMultigraphLowThreeSubcheck 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_023 :
    fiveSupportMultigraphLowThreeSubcheck 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_030 :
    fiveSupportMultigraphLowThreeSubcheck 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_031 :
    fiveSupportMultigraphLowThreeSubcheck 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_032 :
    fiveSupportMultigraphLowThreeSubcheck 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_033 :
    fiveSupportMultigraphLowThreeSubcheck 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_100 :
    fiveSupportMultigraphLowThreeSubcheck 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_101 :
    fiveSupportMultigraphLowThreeSubcheck 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_102 :
    fiveSupportMultigraphLowThreeSubcheck 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_103 :
    fiveSupportMultigraphLowThreeSubcheck 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_110 :
    fiveSupportMultigraphLowThreeSubcheck 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_111 :
    fiveSupportMultigraphLowThreeSubcheck 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_112 :
    fiveSupportMultigraphLowThreeSubcheck 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_113 :
    fiveSupportMultigraphLowThreeSubcheck 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_120 :
    fiveSupportMultigraphLowThreeSubcheck 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_121 :
    fiveSupportMultigraphLowThreeSubcheck 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_122 :
    fiveSupportMultigraphLowThreeSubcheck 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_123 :
    fiveSupportMultigraphLowThreeSubcheck 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_130 :
    fiveSupportMultigraphLowThreeSubcheck 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_131 :
    fiveSupportMultigraphLowThreeSubcheck 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_132 :
    fiveSupportMultigraphLowThreeSubcheck 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_133 :
    fiveSupportMultigraphLowThreeSubcheck 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_200 :
    fiveSupportMultigraphLowThreeSubcheck 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_201 :
    fiveSupportMultigraphLowThreeSubcheck 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_202 :
    fiveSupportMultigraphLowThreeSubcheck 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_203 :
    fiveSupportMultigraphLowThreeSubcheck 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_210 :
    fiveSupportMultigraphLowThreeSubcheck 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_211 :
    fiveSupportMultigraphLowThreeSubcheck 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_212 :
    fiveSupportMultigraphLowThreeSubcheck 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_213 :
    fiveSupportMultigraphLowThreeSubcheck 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_220 :
    fiveSupportMultigraphLowThreeSubcheck 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_221 :
    fiveSupportMultigraphLowThreeSubcheck 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_222 :
    fiveSupportMultigraphLowThreeSubcheck 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_223 :
    fiveSupportMultigraphLowThreeSubcheck 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_230 :
    fiveSupportMultigraphLowThreeSubcheck 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_231 :
    fiveSupportMultigraphLowThreeSubcheck 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_232 :
    fiveSupportMultigraphLowThreeSubcheck 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_233 :
    fiveSupportMultigraphLowThreeSubcheck 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_300 :
    fiveSupportMultigraphLowThreeSubcheck 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_301 :
    fiveSupportMultigraphLowThreeSubcheck 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_302 :
    fiveSupportMultigraphLowThreeSubcheck 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_303 :
    fiveSupportMultigraphLowThreeSubcheck 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_310 :
    fiveSupportMultigraphLowThreeSubcheck 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_311 :
    fiveSupportMultigraphLowThreeSubcheck 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_312 :
    fiveSupportMultigraphLowThreeSubcheck 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_313 :
    fiveSupportMultigraphLowThreeSubcheck 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_320 :
    fiveSupportMultigraphLowThreeSubcheck 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_321 :
    fiveSupportMultigraphLowThreeSubcheck 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_322 :
    fiveSupportMultigraphLowThreeSubcheck 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_323 :
    fiveSupportMultigraphLowThreeSubcheck 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_330 :
    fiveSupportMultigraphLowThreeSubcheck 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_331 :
    fiveSupportMultigraphLowThreeSubcheck 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_332 :
    fiveSupportMultigraphLowThreeSubcheck 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_three_333 :
    fiveSupportMultigraphLowThreeSubcheck 3 3 3 = true := by
  decide

end AiMathLab.P0054.G416
