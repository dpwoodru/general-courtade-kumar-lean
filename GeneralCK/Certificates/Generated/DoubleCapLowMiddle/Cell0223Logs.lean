import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (20257641 / 40000000) ≤ -Real.log (320 / 531) ∧
    -Real.log (320 / 531) ≤ (253220513 / 500000000) := by
  have h := checkLog_sound (w := (211 / 851)) (n := 12)
    (lo := (20257641 / 40000000)) (hi := (253220513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(531 / 320) = 1/(320 / 531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20257641 / 40000000) (253220513 / 500000000) (Real.log (531 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (531 / 320) = -Real.log (320 / 531) := by
    rw [show ((531 / 320) : ℝ) = ((320 / 531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1076973113 / 1000000000) ≤ -Real.log (109 / 320) ∧
    -Real.log (109 / 320) ≤ (215394623 / 200000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 109) = 1/(109 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-215394623 / 200000000) (-1076973113 / 1000000000) (Real.log (109 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (499258987 / 1000000000) ≤ -Real.log (400 / 659) ∧
    -Real.log (400 / 659) ≤ (124814747 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1059)) (n := 12)
    (lo := (499258987 / 1000000000)) (hi := (124814747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 400) = 1/(400 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (499258987 / 1000000000) (124814747 / 250000000) (Real.log (659 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (659 / 400) = -Real.log (400 / 659) := by
    rw [show ((659 / 400) : ℝ) = ((400 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65169041 / 62500000) ≤ -Real.log (141 / 400) ∧
    -Real.log (141 / 400) ≤ (521352329 / 500000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 141) = 1/(141 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-521352329 / 500000000) (-65169041 / 62500000) (Real.log (141 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (138342159 / 500000000) ≤ -Real.log (160 / 211) ∧
    -Real.log (160 / 211) ≤ (276684319 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 371)) (n := 12)
    (lo := (138342159 / 500000000)) (hi := (276684319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 160) = 1/(160 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (138342159 / 500000000) (276684319 / 1000000000) (Real.log (211 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (211 / 160) = -Real.log (160 / 211) := by
    rw [show ((211 / 160) : ℝ) = ((160 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (383825933 / 1000000000) ≤ -Real.log (109 / 160) ∧
    -Real.log (109 / 160) ≤ (191912967 / 500000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 109) = 1/(109 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-191912967 / 500000000) (-383825933 / 1000000000) (Real.log (109 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36755379 / 62500000) ≤ -Real.log (1000000 / 1800539) ∧
    -Real.log (1000000 / 1800539) ≤ (117617213 / 200000000) := by
  have h := checkLog_sound (w := (800539 / 2800539)) (n := 12)
    (lo := (36755379 / 62500000)) (hi := (117617213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1800539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1800539 / 1000000) = 1/(1000000 / 1800539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36755379 / 62500000) (117617213 / 200000000) (Real.log (1800539 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1800539 / 1000000) = -Real.log (1000000 / 1800539) := by
    rw [show ((1800539 / 1000000) : ℝ) = ((1000000 / 1800539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1612136549 / 1000000000) ≤ -Real.log (199461 / 1000000) ∧
    -Real.log (199461 / 1000000) ≤ (201517069 / 125000000) := by
  have h := checkLog_sound (w := (50539 / 449461)) (n := 12)
    (lo := (225842189 / 1000000000)) (hi := (22584219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199461) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 199461) = 1/(199461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-201517069 / 125000000) (-1612136549 / 1000000000) (Real.log (199461 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147494399 / 250000000) ≤ -Real.log (250000 / 450987) ∧
    -Real.log (250000 / 450987) ≤ (589977597 / 1000000000) := by
  have h := checkLog_sound (w := (200987 / 700987)) (n := 12)
    (lo := (147494399 / 250000000)) (hi := (589977597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450987 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450987 / 250000) = 1/(250000 / 450987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147494399 / 250000000) (589977597 / 1000000000) (Real.log (450987 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (450987 / 250000) = -Real.log (250000 / 450987) := by
    rw [show ((450987 / 250000) : ℝ) = ((250000 / 450987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1629375347 / 1000000000) ≤ -Real.log (49013 / 250000) ∧
    -Real.log (49013 / 250000) ≤ (32587507 / 20000000) := by
  have h := checkLog_sound (w := (13487 / 111513)) (n := 12)
    (lo := (243080987 / 1000000000)) (hi := (60770247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49013) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 49013) = 1/(49013 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32587507 / 20000000) (-1629375347 / 1000000000) (Real.log (49013 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (139992217 / 250000000) ≤ -Real.log (500000 / 875309) ∧
    -Real.log (500000 / 875309) ≤ (559968869 / 1000000000) := by
  have h := checkLog_sound (w := (375309 / 1375309)) (n := 12)
    (lo := (139992217 / 250000000)) (hi := (559968869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875309 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875309 / 500000) = 1/(500000 / 875309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (139992217 / 250000000) (559968869 / 1000000000) (Real.log (875309 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (875309 / 500000) = -Real.log (500000 / 875309) := by
    rw [show ((875309 / 500000) : ℝ) = ((500000 / 875309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69438471 / 50000000) ≤ -Real.log (124691 / 500000) ∧
    -Real.log (124691 / 500000) ≤ (1388769423 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 249691)) (n := 12)
    (lo := (123753 / 50000000)) (hi := (2475061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 124691) = 1/(124691 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1388769423 / 1000000000) (-69438471 / 50000000) (Real.log (124691 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (564260413 / 1000000000) ≤ -Real.log (1000000 / 1758147) ∧
    -Real.log (1000000 / 1758147) ≤ (282130207 / 500000000) := by
  have h := checkLog_sound (w := (758147 / 2758147)) (n := 12)
    (lo := (564260413 / 1000000000)) (hi := (282130207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1758147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1758147 / 1000000) = 1/(1000000 / 1758147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (564260413 / 1000000000) (282130207 / 500000000) (Real.log (1758147 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1758147 / 1000000) = -Real.log (1000000 / 1758147) := by
    rw [show ((1758147 / 1000000) : ℝ) = ((1000000 / 1758147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (709712587 / 500000000) ≤ -Real.log (241853 / 1000000) ∧
    -Real.log (241853 / 1000000) ≤ (1419425177 / 1000000000) := by
  have h := checkLog_sound (w := (8147 / 491853)) (n := 12)
    (lo := (16565407 / 500000000)) (hi := (6626163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241853) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 241853) = 1/(241853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1419425177 / 1000000000) (-709712587 / 500000000) (Real.log (241853 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2200222613 / 1000000000) ≤ -Real.log (250000000000 / 2256755706629) ∧
    -Real.log (250000000000 / 2256755706629) ≤ (2200222617 / 1000000000) := by
  have h := checkLog_sound (w := (256755706629 / 4256755706629)) (n := 12)
    (lo := (120781073 / 1000000000)) (hi := (60390537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2256755706629 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2256755706629 / 2000000000000) = 1/(250000000000 / 2256755706629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2200222613 / 1000000000) (2200222617 / 1000000000) (Real.log (2256755706629 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2256755706629 / 250000000000) = -Real.log (250000000000 / 2256755706629) := by
    rw [show ((2256755706629 / 250000000000) : ℝ) = ((250000000000 / 2256755706629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2219352943 / 1000000000) ≤ -Real.log (100000000000 / 920137514537) ∧
    -Real.log (100000000000 / 920137514537) ≤ (2219352947 / 1000000000) := by
  have h := checkLog_sound (w := (120137514537 / 1720137514537)) (n := 12)
    (lo := (139911403 / 1000000000)) (hi := (34977851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920137514537 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(920137514537 / 800000000000) = 1/(100000000000 / 920137514537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2219352943 / 1000000000) (2219352947 / 1000000000) (Real.log (920137514537 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (920137514537 / 100000000000) = -Real.log (100000000000 / 920137514537) := by
    rw [show ((920137514537 / 100000000000) : ℝ) = ((100000000000 / 920137514537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (121796143 / 62500000) ≤ -Real.log (500000000000 / 3509912503709) ∧
    -Real.log (500000000000 / 3509912503709) ≤ (1948738291 / 1000000000) := by
  have h := checkLog_sound (w := (1509912503709 / 5509912503709)) (n := 12)
    (lo := (70305491 / 125000000)) (hi := (562443929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3509912503709 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3509912503709 / 2000000000000) = 1/(500000000000 / 3509912503709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (121796143 / 62500000) (1948738291 / 1000000000) (Real.log (3509912503709 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3509912503709 / 500000000000) = -Real.log (500000000000 / 3509912503709) := by
    rw [show ((3509912503709 / 500000000000) : ℝ) = ((500000000000 / 3509912503709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1983685587 / 1000000000) ≤ -Real.log (500000000000 / 3634743005049) ∧
    -Real.log (500000000000 / 3634743005049) ≤ (198368559 / 100000000) := by
  have h := checkLog_sound (w := (1634743005049 / 5634743005049)) (n := 12)
    (lo := (597391227 / 1000000000)) (hi := (149347807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3634743005049 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3634743005049 / 2000000000000) = 1/(500000000000 / 3634743005049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1983685587 / 1000000000) (198368559 / 100000000) (Real.log (3634743005049 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3634743005049 / 500000000000) = -Real.log (500000000000 / 3634743005049) := by
    rw [show ((3634743005049 / 500000000000) : ℝ) = ((500000000000 / 3634743005049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223
