import AiMathLab.P0054G416.SupportMultigraphLowFourFinite

namespace AiMathLab.P0054.G416

def fiveSupportMultigraphLowFiveSubcheck (a b c d : Nat) : Bool :=
  fiveSupportMultigraphCheckAux 5 15 ((List.range 15).drop 4)
    (fiveMultiplicityAfterFour a b c d) (fiveDegreeStateAfterFour a b c d)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0000 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0001 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0002 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0003 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0010 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0011 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0012 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0013 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0020 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0021 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0022 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0023 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0030 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0031 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0032 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0033 :
    fiveSupportMultigraphLowFiveSubcheck 0 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0100 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0101 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0102 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0103 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0110 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0111 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0112 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0113 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0120 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0121 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0122 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0123 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0130 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0131 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0132 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0133 :
    fiveSupportMultigraphLowFiveSubcheck 0 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0200 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0201 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0202 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0203 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0210 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0211 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0212 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0213 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0220 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0221 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0222 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0223 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0230 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0231 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0232 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0233 :
    fiveSupportMultigraphLowFiveSubcheck 0 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0300 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0301 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0302 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0303 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0310 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0311 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0312 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0313 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0320 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0321 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0322 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0323 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0330 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0331 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0332 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_0333 :
    fiveSupportMultigraphLowFiveSubcheck 0 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1000 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1001 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1002 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1003 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1010 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1011 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1012 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1013 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1020 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1021 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1022 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1023 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1030 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1031 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1032 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1033 :
    fiveSupportMultigraphLowFiveSubcheck 1 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1100 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1101 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1102 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1103 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1110 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1111 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1112 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1113 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1120 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1121 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1122 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1123 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1130 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1131 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1132 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1133 :
    fiveSupportMultigraphLowFiveSubcheck 1 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1200 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1201 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1202 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1203 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1210 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1211 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1212 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1213 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1220 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1221 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1222 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1223 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1230 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1231 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1232 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1233 :
    fiveSupportMultigraphLowFiveSubcheck 1 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1300 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1301 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1302 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1303 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1310 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1311 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1312 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1313 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1320 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1321 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1322 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1323 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1330 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1331 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1332 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_1333 :
    fiveSupportMultigraphLowFiveSubcheck 1 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2000 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2001 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2002 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2003 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2010 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2011 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2012 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2013 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2020 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2021 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2022 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2023 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2030 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2031 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2032 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2033 :
    fiveSupportMultigraphLowFiveSubcheck 2 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2100 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2101 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2102 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2103 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2110 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2111 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2112 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2113 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2120 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2121 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2122 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2123 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2130 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2131 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2132 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2133 :
    fiveSupportMultigraphLowFiveSubcheck 2 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2200 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2201 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2202 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2203 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2210 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2211 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2212 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2213 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2220 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2221 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2222 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2223 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2230 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2231 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2232 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2233 :
    fiveSupportMultigraphLowFiveSubcheck 2 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2300 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2301 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2302 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2303 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2310 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2311 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2312 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2313 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2320 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2321 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2322 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2323 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2330 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2331 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2332 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_2333 :
    fiveSupportMultigraphLowFiveSubcheck 2 3 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3000 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3001 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3002 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3003 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3010 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3011 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3012 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3013 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3020 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3021 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3022 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3023 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3030 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3031 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3032 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3033 :
    fiveSupportMultigraphLowFiveSubcheck 3 0 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3100 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3101 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3102 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3103 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3110 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3111 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3112 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3113 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3120 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3121 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3122 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3123 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3130 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3131 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3132 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3133 :
    fiveSupportMultigraphLowFiveSubcheck 3 1 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3200 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3201 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3202 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3203 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3210 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3211 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3212 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3213 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3220 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3221 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3222 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3223 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3230 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3231 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3232 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3233 :
    fiveSupportMultigraphLowFiveSubcheck 3 2 3 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3300 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 0 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3301 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 0 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3302 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 0 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3303 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 0 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3310 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 1 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3311 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 1 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3312 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 1 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3313 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 1 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3320 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 2 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3321 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 2 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3322 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 2 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3323 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 2 3 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3330 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 3 0 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3331 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 3 1 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3332 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 3 2 = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem five_support_multigraph_low_five_3333 :
    fiveSupportMultigraphLowFiveSubcheck 3 3 3 3 = true := by
  decide

end AiMathLab.P0054.G416
