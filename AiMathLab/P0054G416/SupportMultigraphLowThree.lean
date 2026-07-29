import AiMathLab.P0054G416.SupportMultigraphFinite

namespace AiMathLab.P0054.G416

theorem five_support_multigraph_low_three_subcheck_all :
    ∀ a b c : Fin 4,
      fiveSupportMultigraphLowThreeSubcheck a.val b.val c.val = true
  | ⟨0, _⟩, ⟨0, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_000
  | ⟨0, _⟩, ⟨0, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_001
  | ⟨0, _⟩, ⟨0, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_002
  | ⟨0, _⟩, ⟨0, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_003
  | ⟨0, _⟩, ⟨1, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_010
  | ⟨0, _⟩, ⟨1, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_011
  | ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_012
  | ⟨0, _⟩, ⟨1, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_013
  | ⟨0, _⟩, ⟨2, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_020
  | ⟨0, _⟩, ⟨2, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_021
  | ⟨0, _⟩, ⟨2, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_022
  | ⟨0, _⟩, ⟨2, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_023
  | ⟨0, _⟩, ⟨3, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_030
  | ⟨0, _⟩, ⟨3, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_031
  | ⟨0, _⟩, ⟨3, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_032
  | ⟨0, _⟩, ⟨3, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_033
  | ⟨1, _⟩, ⟨0, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_100
  | ⟨1, _⟩, ⟨0, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_101
  | ⟨1, _⟩, ⟨0, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_102
  | ⟨1, _⟩, ⟨0, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_103
  | ⟨1, _⟩, ⟨1, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_110
  | ⟨1, _⟩, ⟨1, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_111
  | ⟨1, _⟩, ⟨1, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_112
  | ⟨1, _⟩, ⟨1, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_113
  | ⟨1, _⟩, ⟨2, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_120
  | ⟨1, _⟩, ⟨2, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_121
  | ⟨1, _⟩, ⟨2, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_122
  | ⟨1, _⟩, ⟨2, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_123
  | ⟨1, _⟩, ⟨3, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_130
  | ⟨1, _⟩, ⟨3, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_131
  | ⟨1, _⟩, ⟨3, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_132
  | ⟨1, _⟩, ⟨3, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_133
  | ⟨2, _⟩, ⟨0, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_200
  | ⟨2, _⟩, ⟨0, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_201
  | ⟨2, _⟩, ⟨0, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_202
  | ⟨2, _⟩, ⟨0, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_203
  | ⟨2, _⟩, ⟨1, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_210
  | ⟨2, _⟩, ⟨1, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_211
  | ⟨2, _⟩, ⟨1, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_212
  | ⟨2, _⟩, ⟨1, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_213
  | ⟨2, _⟩, ⟨2, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_220
  | ⟨2, _⟩, ⟨2, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_221
  | ⟨2, _⟩, ⟨2, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_222
  | ⟨2, _⟩, ⟨2, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_223
  | ⟨2, _⟩, ⟨3, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_230
  | ⟨2, _⟩, ⟨3, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_231
  | ⟨2, _⟩, ⟨3, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_232
  | ⟨2, _⟩, ⟨3, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_233
  | ⟨3, _⟩, ⟨0, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_300
  | ⟨3, _⟩, ⟨0, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_301
  | ⟨3, _⟩, ⟨0, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_302
  | ⟨3, _⟩, ⟨0, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_303
  | ⟨3, _⟩, ⟨1, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_310
  | ⟨3, _⟩, ⟨1, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_311
  | ⟨3, _⟩, ⟨1, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_312
  | ⟨3, _⟩, ⟨1, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_313
  | ⟨3, _⟩, ⟨2, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_320
  | ⟨3, _⟩, ⟨2, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_321
  | ⟨3, _⟩, ⟨2, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_322
  | ⟨3, _⟩, ⟨2, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_323
  | ⟨3, _⟩, ⟨3, _⟩, ⟨0, _⟩ => five_support_multigraph_low_three_330
  | ⟨3, _⟩, ⟨3, _⟩, ⟨1, _⟩ => five_support_multigraph_low_three_331
  | ⟨3, _⟩, ⟨3, _⟩, ⟨2, _⟩ => five_support_multigraph_low_three_332
  | ⟨3, _⟩, ⟨3, _⟩, ⟨3, _⟩ => five_support_multigraph_low_three_333
  | ⟨a + 4, ha⟩, _, _ => by omega
  | _, ⟨b + 4, hb⟩, _ => by omega
  | _, _, ⟨c + 4, hc⟩ => by omega

theorem five_support_multigraph_low_three_split_certificate :
    fiveSupportMultigraphLowThreeSplitCheck = true := by
  simp only [fiveSupportMultigraphLowThreeSplitCheck, List.all_eq_true, List.mem_range]
  intro a ha b hb c hc
  exact five_support_multigraph_low_three_subcheck_all ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩

end AiMathLab.P0054.G416
