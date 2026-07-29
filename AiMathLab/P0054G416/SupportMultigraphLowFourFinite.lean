import AiMathLab.P0054G416.SupportMultigraphFinite

namespace AiMathLab.P0054.G416

def fiveMultiplicityAfterFour (a b c d : Nat) : FiveMultiplicity :=
  (((fiveMultiplicityZero.set! 0 a).set! 1 b).set! 2 c).set! 3 d

def fiveDegreeStateAfterFour (a b c d : Nat) : FiveDegreeState :=
  #[(a : Nat), b, c, d, 0]

def fiveSupportMultigraphLowFourSubcheck (a b c d : Nat) : Bool :=
  fiveSupportMultigraphCheckAux 4 16 ((List.range 15).drop 4)
    (fiveMultiplicityAfterFour a b c d) (fiveDegreeStateAfterFour a b c d)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0000 :
    fiveSupportMultigraphLowFourSubcheck 0 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0001 :
    fiveSupportMultigraphLowFourSubcheck 0 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0002 :
    fiveSupportMultigraphLowFourSubcheck 0 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0003 :
    fiveSupportMultigraphLowFourSubcheck 0 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0010 :
    fiveSupportMultigraphLowFourSubcheck 0 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0011 :
    fiveSupportMultigraphLowFourSubcheck 0 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0012 :
    fiveSupportMultigraphLowFourSubcheck 0 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0013 :
    fiveSupportMultigraphLowFourSubcheck 0 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0020 :
    fiveSupportMultigraphLowFourSubcheck 0 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0021 :
    fiveSupportMultigraphLowFourSubcheck 0 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0022 :
    fiveSupportMultigraphLowFourSubcheck 0 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0023 :
    fiveSupportMultigraphLowFourSubcheck 0 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0030 :
    fiveSupportMultigraphLowFourSubcheck 0 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0031 :
    fiveSupportMultigraphLowFourSubcheck 0 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0032 :
    fiveSupportMultigraphLowFourSubcheck 0 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0033 :
    fiveSupportMultigraphLowFourSubcheck 0 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0100 :
    fiveSupportMultigraphLowFourSubcheck 0 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0101 :
    fiveSupportMultigraphLowFourSubcheck 0 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0102 :
    fiveSupportMultigraphLowFourSubcheck 0 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0103 :
    fiveSupportMultigraphLowFourSubcheck 0 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0110 :
    fiveSupportMultigraphLowFourSubcheck 0 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0111 :
    fiveSupportMultigraphLowFourSubcheck 0 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0112 :
    fiveSupportMultigraphLowFourSubcheck 0 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0113 :
    fiveSupportMultigraphLowFourSubcheck 0 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0120 :
    fiveSupportMultigraphLowFourSubcheck 0 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0121 :
    fiveSupportMultigraphLowFourSubcheck 0 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0122 :
    fiveSupportMultigraphLowFourSubcheck 0 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0123 :
    fiveSupportMultigraphLowFourSubcheck 0 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0130 :
    fiveSupportMultigraphLowFourSubcheck 0 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0131 :
    fiveSupportMultigraphLowFourSubcheck 0 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0132 :
    fiveSupportMultigraphLowFourSubcheck 0 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0133 :
    fiveSupportMultigraphLowFourSubcheck 0 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0200 :
    fiveSupportMultigraphLowFourSubcheck 0 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0201 :
    fiveSupportMultigraphLowFourSubcheck 0 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0202 :
    fiveSupportMultigraphLowFourSubcheck 0 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0203 :
    fiveSupportMultigraphLowFourSubcheck 0 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0210 :
    fiveSupportMultigraphLowFourSubcheck 0 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0211 :
    fiveSupportMultigraphLowFourSubcheck 0 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0212 :
    fiveSupportMultigraphLowFourSubcheck 0 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0213 :
    fiveSupportMultigraphLowFourSubcheck 0 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0220 :
    fiveSupportMultigraphLowFourSubcheck 0 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0221 :
    fiveSupportMultigraphLowFourSubcheck 0 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0222 :
    fiveSupportMultigraphLowFourSubcheck 0 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0223 :
    fiveSupportMultigraphLowFourSubcheck 0 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0230 :
    fiveSupportMultigraphLowFourSubcheck 0 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0231 :
    fiveSupportMultigraphLowFourSubcheck 0 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0232 :
    fiveSupportMultigraphLowFourSubcheck 0 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0233 :
    fiveSupportMultigraphLowFourSubcheck 0 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0300 :
    fiveSupportMultigraphLowFourSubcheck 0 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0301 :
    fiveSupportMultigraphLowFourSubcheck 0 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0302 :
    fiveSupportMultigraphLowFourSubcheck 0 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0303 :
    fiveSupportMultigraphLowFourSubcheck 0 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0310 :
    fiveSupportMultigraphLowFourSubcheck 0 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0311 :
    fiveSupportMultigraphLowFourSubcheck 0 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0312 :
    fiveSupportMultigraphLowFourSubcheck 0 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0313 :
    fiveSupportMultigraphLowFourSubcheck 0 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0320 :
    fiveSupportMultigraphLowFourSubcheck 0 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0321 :
    fiveSupportMultigraphLowFourSubcheck 0 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0322 :
    fiveSupportMultigraphLowFourSubcheck 0 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0323 :
    fiveSupportMultigraphLowFourSubcheck 0 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0330 :
    fiveSupportMultigraphLowFourSubcheck 0 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0331 :
    fiveSupportMultigraphLowFourSubcheck 0 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0332 :
    fiveSupportMultigraphLowFourSubcheck 0 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_0333 :
    fiveSupportMultigraphLowFourSubcheck 0 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1000 :
    fiveSupportMultigraphLowFourSubcheck 1 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1001 :
    fiveSupportMultigraphLowFourSubcheck 1 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1002 :
    fiveSupportMultigraphLowFourSubcheck 1 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1003 :
    fiveSupportMultigraphLowFourSubcheck 1 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1010 :
    fiveSupportMultigraphLowFourSubcheck 1 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1011 :
    fiveSupportMultigraphLowFourSubcheck 1 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1012 :
    fiveSupportMultigraphLowFourSubcheck 1 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1013 :
    fiveSupportMultigraphLowFourSubcheck 1 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1020 :
    fiveSupportMultigraphLowFourSubcheck 1 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1021 :
    fiveSupportMultigraphLowFourSubcheck 1 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1022 :
    fiveSupportMultigraphLowFourSubcheck 1 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1023 :
    fiveSupportMultigraphLowFourSubcheck 1 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1030 :
    fiveSupportMultigraphLowFourSubcheck 1 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1031 :
    fiveSupportMultigraphLowFourSubcheck 1 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1032 :
    fiveSupportMultigraphLowFourSubcheck 1 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1033 :
    fiveSupportMultigraphLowFourSubcheck 1 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1100 :
    fiveSupportMultigraphLowFourSubcheck 1 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1101 :
    fiveSupportMultigraphLowFourSubcheck 1 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1102 :
    fiveSupportMultigraphLowFourSubcheck 1 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1103 :
    fiveSupportMultigraphLowFourSubcheck 1 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1110 :
    fiveSupportMultigraphLowFourSubcheck 1 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1111 :
    fiveSupportMultigraphLowFourSubcheck 1 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1112 :
    fiveSupportMultigraphLowFourSubcheck 1 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1113 :
    fiveSupportMultigraphLowFourSubcheck 1 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1120 :
    fiveSupportMultigraphLowFourSubcheck 1 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1121 :
    fiveSupportMultigraphLowFourSubcheck 1 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1122 :
    fiveSupportMultigraphLowFourSubcheck 1 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1123 :
    fiveSupportMultigraphLowFourSubcheck 1 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1130 :
    fiveSupportMultigraphLowFourSubcheck 1 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1131 :
    fiveSupportMultigraphLowFourSubcheck 1 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1132 :
    fiveSupportMultigraphLowFourSubcheck 1 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1133 :
    fiveSupportMultigraphLowFourSubcheck 1 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1200 :
    fiveSupportMultigraphLowFourSubcheck 1 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1201 :
    fiveSupportMultigraphLowFourSubcheck 1 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1202 :
    fiveSupportMultigraphLowFourSubcheck 1 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1203 :
    fiveSupportMultigraphLowFourSubcheck 1 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1210 :
    fiveSupportMultigraphLowFourSubcheck 1 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1211 :
    fiveSupportMultigraphLowFourSubcheck 1 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1212 :
    fiveSupportMultigraphLowFourSubcheck 1 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1213 :
    fiveSupportMultigraphLowFourSubcheck 1 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1220 :
    fiveSupportMultigraphLowFourSubcheck 1 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1221 :
    fiveSupportMultigraphLowFourSubcheck 1 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1222 :
    fiveSupportMultigraphLowFourSubcheck 1 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1223 :
    fiveSupportMultigraphLowFourSubcheck 1 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1230 :
    fiveSupportMultigraphLowFourSubcheck 1 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1231 :
    fiveSupportMultigraphLowFourSubcheck 1 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1232 :
    fiveSupportMultigraphLowFourSubcheck 1 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1233 :
    fiveSupportMultigraphLowFourSubcheck 1 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1300 :
    fiveSupportMultigraphLowFourSubcheck 1 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1301 :
    fiveSupportMultigraphLowFourSubcheck 1 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1302 :
    fiveSupportMultigraphLowFourSubcheck 1 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1303 :
    fiveSupportMultigraphLowFourSubcheck 1 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1310 :
    fiveSupportMultigraphLowFourSubcheck 1 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1311 :
    fiveSupportMultigraphLowFourSubcheck 1 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1312 :
    fiveSupportMultigraphLowFourSubcheck 1 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1313 :
    fiveSupportMultigraphLowFourSubcheck 1 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1320 :
    fiveSupportMultigraphLowFourSubcheck 1 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1321 :
    fiveSupportMultigraphLowFourSubcheck 1 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1322 :
    fiveSupportMultigraphLowFourSubcheck 1 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1323 :
    fiveSupportMultigraphLowFourSubcheck 1 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1330 :
    fiveSupportMultigraphLowFourSubcheck 1 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1331 :
    fiveSupportMultigraphLowFourSubcheck 1 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1332 :
    fiveSupportMultigraphLowFourSubcheck 1 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_1333 :
    fiveSupportMultigraphLowFourSubcheck 1 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2000 :
    fiveSupportMultigraphLowFourSubcheck 2 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2001 :
    fiveSupportMultigraphLowFourSubcheck 2 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2002 :
    fiveSupportMultigraphLowFourSubcheck 2 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2003 :
    fiveSupportMultigraphLowFourSubcheck 2 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2010 :
    fiveSupportMultigraphLowFourSubcheck 2 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2011 :
    fiveSupportMultigraphLowFourSubcheck 2 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2012 :
    fiveSupportMultigraphLowFourSubcheck 2 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2013 :
    fiveSupportMultigraphLowFourSubcheck 2 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2020 :
    fiveSupportMultigraphLowFourSubcheck 2 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2021 :
    fiveSupportMultigraphLowFourSubcheck 2 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2022 :
    fiveSupportMultigraphLowFourSubcheck 2 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2023 :
    fiveSupportMultigraphLowFourSubcheck 2 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2030 :
    fiveSupportMultigraphLowFourSubcheck 2 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2031 :
    fiveSupportMultigraphLowFourSubcheck 2 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2032 :
    fiveSupportMultigraphLowFourSubcheck 2 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2033 :
    fiveSupportMultigraphLowFourSubcheck 2 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2100 :
    fiveSupportMultigraphLowFourSubcheck 2 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2101 :
    fiveSupportMultigraphLowFourSubcheck 2 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2102 :
    fiveSupportMultigraphLowFourSubcheck 2 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2103 :
    fiveSupportMultigraphLowFourSubcheck 2 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2110 :
    fiveSupportMultigraphLowFourSubcheck 2 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2111 :
    fiveSupportMultigraphLowFourSubcheck 2 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2112 :
    fiveSupportMultigraphLowFourSubcheck 2 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2113 :
    fiveSupportMultigraphLowFourSubcheck 2 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2120 :
    fiveSupportMultigraphLowFourSubcheck 2 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2121 :
    fiveSupportMultigraphLowFourSubcheck 2 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2122 :
    fiveSupportMultigraphLowFourSubcheck 2 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2123 :
    fiveSupportMultigraphLowFourSubcheck 2 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2130 :
    fiveSupportMultigraphLowFourSubcheck 2 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2131 :
    fiveSupportMultigraphLowFourSubcheck 2 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2132 :
    fiveSupportMultigraphLowFourSubcheck 2 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2133 :
    fiveSupportMultigraphLowFourSubcheck 2 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2200 :
    fiveSupportMultigraphLowFourSubcheck 2 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2201 :
    fiveSupportMultigraphLowFourSubcheck 2 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2202 :
    fiveSupportMultigraphLowFourSubcheck 2 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2203 :
    fiveSupportMultigraphLowFourSubcheck 2 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2210 :
    fiveSupportMultigraphLowFourSubcheck 2 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2211 :
    fiveSupportMultigraphLowFourSubcheck 2 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2212 :
    fiveSupportMultigraphLowFourSubcheck 2 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2213 :
    fiveSupportMultigraphLowFourSubcheck 2 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2220 :
    fiveSupportMultigraphLowFourSubcheck 2 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2221 :
    fiveSupportMultigraphLowFourSubcheck 2 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2222 :
    fiveSupportMultigraphLowFourSubcheck 2 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2223 :
    fiveSupportMultigraphLowFourSubcheck 2 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2230 :
    fiveSupportMultigraphLowFourSubcheck 2 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2231 :
    fiveSupportMultigraphLowFourSubcheck 2 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2232 :
    fiveSupportMultigraphLowFourSubcheck 2 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2233 :
    fiveSupportMultigraphLowFourSubcheck 2 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2300 :
    fiveSupportMultigraphLowFourSubcheck 2 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2301 :
    fiveSupportMultigraphLowFourSubcheck 2 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2302 :
    fiveSupportMultigraphLowFourSubcheck 2 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2303 :
    fiveSupportMultigraphLowFourSubcheck 2 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2310 :
    fiveSupportMultigraphLowFourSubcheck 2 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2311 :
    fiveSupportMultigraphLowFourSubcheck 2 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2312 :
    fiveSupportMultigraphLowFourSubcheck 2 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2313 :
    fiveSupportMultigraphLowFourSubcheck 2 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2320 :
    fiveSupportMultigraphLowFourSubcheck 2 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2321 :
    fiveSupportMultigraphLowFourSubcheck 2 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2322 :
    fiveSupportMultigraphLowFourSubcheck 2 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2323 :
    fiveSupportMultigraphLowFourSubcheck 2 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2330 :
    fiveSupportMultigraphLowFourSubcheck 2 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2331 :
    fiveSupportMultigraphLowFourSubcheck 2 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2332 :
    fiveSupportMultigraphLowFourSubcheck 2 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_2333 :
    fiveSupportMultigraphLowFourSubcheck 2 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3000 :
    fiveSupportMultigraphLowFourSubcheck 3 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3001 :
    fiveSupportMultigraphLowFourSubcheck 3 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3002 :
    fiveSupportMultigraphLowFourSubcheck 3 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3003 :
    fiveSupportMultigraphLowFourSubcheck 3 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3010 :
    fiveSupportMultigraphLowFourSubcheck 3 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3011 :
    fiveSupportMultigraphLowFourSubcheck 3 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3012 :
    fiveSupportMultigraphLowFourSubcheck 3 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3013 :
    fiveSupportMultigraphLowFourSubcheck 3 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3020 :
    fiveSupportMultigraphLowFourSubcheck 3 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3021 :
    fiveSupportMultigraphLowFourSubcheck 3 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3022 :
    fiveSupportMultigraphLowFourSubcheck 3 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3023 :
    fiveSupportMultigraphLowFourSubcheck 3 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3030 :
    fiveSupportMultigraphLowFourSubcheck 3 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3031 :
    fiveSupportMultigraphLowFourSubcheck 3 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3032 :
    fiveSupportMultigraphLowFourSubcheck 3 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3033 :
    fiveSupportMultigraphLowFourSubcheck 3 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3100 :
    fiveSupportMultigraphLowFourSubcheck 3 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3101 :
    fiveSupportMultigraphLowFourSubcheck 3 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3102 :
    fiveSupportMultigraphLowFourSubcheck 3 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3103 :
    fiveSupportMultigraphLowFourSubcheck 3 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3110 :
    fiveSupportMultigraphLowFourSubcheck 3 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3111 :
    fiveSupportMultigraphLowFourSubcheck 3 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3112 :
    fiveSupportMultigraphLowFourSubcheck 3 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3113 :
    fiveSupportMultigraphLowFourSubcheck 3 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3120 :
    fiveSupportMultigraphLowFourSubcheck 3 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3121 :
    fiveSupportMultigraphLowFourSubcheck 3 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3122 :
    fiveSupportMultigraphLowFourSubcheck 3 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3123 :
    fiveSupportMultigraphLowFourSubcheck 3 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3130 :
    fiveSupportMultigraphLowFourSubcheck 3 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3131 :
    fiveSupportMultigraphLowFourSubcheck 3 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3132 :
    fiveSupportMultigraphLowFourSubcheck 3 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3133 :
    fiveSupportMultigraphLowFourSubcheck 3 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3200 :
    fiveSupportMultigraphLowFourSubcheck 3 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3201 :
    fiveSupportMultigraphLowFourSubcheck 3 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3202 :
    fiveSupportMultigraphLowFourSubcheck 3 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3203 :
    fiveSupportMultigraphLowFourSubcheck 3 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3210 :
    fiveSupportMultigraphLowFourSubcheck 3 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3211 :
    fiveSupportMultigraphLowFourSubcheck 3 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3212 :
    fiveSupportMultigraphLowFourSubcheck 3 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3213 :
    fiveSupportMultigraphLowFourSubcheck 3 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3220 :
    fiveSupportMultigraphLowFourSubcheck 3 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3221 :
    fiveSupportMultigraphLowFourSubcheck 3 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3222 :
    fiveSupportMultigraphLowFourSubcheck 3 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3223 :
    fiveSupportMultigraphLowFourSubcheck 3 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3230 :
    fiveSupportMultigraphLowFourSubcheck 3 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3231 :
    fiveSupportMultigraphLowFourSubcheck 3 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3232 :
    fiveSupportMultigraphLowFourSubcheck 3 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3233 :
    fiveSupportMultigraphLowFourSubcheck 3 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3300 :
    fiveSupportMultigraphLowFourSubcheck 3 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3301 :
    fiveSupportMultigraphLowFourSubcheck 3 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3302 :
    fiveSupportMultigraphLowFourSubcheck 3 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3303 :
    fiveSupportMultigraphLowFourSubcheck 3 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3310 :
    fiveSupportMultigraphLowFourSubcheck 3 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3311 :
    fiveSupportMultigraphLowFourSubcheck 3 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3312 :
    fiveSupportMultigraphLowFourSubcheck 3 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3313 :
    fiveSupportMultigraphLowFourSubcheck 3 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3320 :
    fiveSupportMultigraphLowFourSubcheck 3 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3321 :
    fiveSupportMultigraphLowFourSubcheck 3 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3322 :
    fiveSupportMultigraphLowFourSubcheck 3 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3323 :
    fiveSupportMultigraphLowFourSubcheck 3 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3330 :
    fiveSupportMultigraphLowFourSubcheck 3 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3331 :
    fiveSupportMultigraphLowFourSubcheck 3 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3332 :
    fiveSupportMultigraphLowFourSubcheck 3 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_four_3333 :
    fiveSupportMultigraphLowFourSubcheck 3 3 3 3 = true := by
  decide

end AiMathLab.P0054.G416
