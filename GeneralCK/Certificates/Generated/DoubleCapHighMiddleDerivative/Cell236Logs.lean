import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell236
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (328488441 / 1000000000) ≤ -Real.log (5120 / 7111) ∧
    -Real.log (5120 / 7111) ≤ (164244221 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 12231)) (n := 12)
    (lo := (328488441 / 1000000000)) (hi := (164244221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7111 / 5120) = 1/(5120 / 7111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (328488441 / 1000000000) (164244221 / 500000000) (Real.log (7111 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7111 / 5120) = -Real.log (5120 / 7111) := by
    rw [show ((7111 / 5120) : ℝ) = ((5120 / 7111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246220487 / 500000000) ≤ -Real.log (3129 / 5120) ∧
    -Real.log (3129 / 5120) ≤ (19697639 / 40000000) := by
  have h := checkLog_sound (w := (1991 / 8249)) (n := 12)
    (lo := (246220487 / 500000000)) (hi := (19697639 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3129) = 1/(3129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-19697639 / 40000000) (-246220487 / 500000000) (Real.log (3129 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (328066471 / 1000000000) ≤ -Real.log (1280 / 1777) ∧
    -Real.log (1280 / 1777) ≤ (41008309 / 125000000) := by
  have h := checkLog_sound (w := (497 / 3057)) (n := 12)
    (lo := (328066471 / 1000000000)) (hi := (41008309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777 / 1280) = 1/(1280 / 1777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (328066471 / 1000000000) (41008309 / 125000000) (Real.log (1777 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1777 / 1280) = -Real.log (1280 / 1777) := by
    rw [show ((1777 / 1280) : ℝ) = ((1280 / 1777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24574133 / 50000000) ≤ -Real.log (783 / 1280) ∧
    -Real.log (783 / 1280) ≤ (491482661 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2063)) (n := 12)
    (lo := (24574133 / 50000000)) (hi := (491482661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 783) = 1/(783 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-491482661 / 1000000000) (-24574133 / 50000000) (Real.log (783 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3813157 / 15625000) ≤ -Real.log (500000 / 638199) ∧
    -Real.log (500000 / 638199) ≤ (244042049 / 1000000000) := by
  have h := checkLog_sound (w := (138199 / 1138199)) (n := 12)
    (lo := (3813157 / 15625000)) (hi := (244042049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638199 / 500000) = 1/(500000 / 638199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3813157 / 15625000) (244042049 / 1000000000) (Real.log (638199 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (638199 / 500000) = -Real.log (500000 / 638199) := by
    rw [show ((638199 / 500000) : ℝ) = ((500000 / 638199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323513761 / 1000000000) ≤ -Real.log (361801 / 500000) ∧
    -Real.log (361801 / 500000) ≤ (161756881 / 500000000) := by
  have h := checkLog_sound (w := (138199 / 861801)) (n := 12)
    (lo := (323513761 / 1000000000)) (hi := (161756881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 361801) = 1/(361801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-161756881 / 500000000) (-323513761 / 1000000000) (Real.log (361801 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122187089 / 500000000) ≤ -Real.log (500000 / 638411) ∧
    -Real.log (500000 / 638411) ≤ (244374179 / 1000000000) := by
  have h := checkLog_sound (w := (138411 / 1138411)) (n := 12)
    (lo := (122187089 / 500000000)) (hi := (244374179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638411 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638411 / 500000) = 1/(500000 / 638411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122187089 / 500000000) (244374179 / 1000000000) (Real.log (638411 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (638411 / 500000) = -Real.log (500000 / 638411) := by
    rw [show ((638411 / 500000) : ℝ) = ((500000 / 638411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (32409989 / 100000000) ≤ -Real.log (361589 / 500000) ∧
    -Real.log (361589 / 500000) ≤ (324099891 / 1000000000) := by
  have h := checkLog_sound (w := (138411 / 861589)) (n := 12)
    (lo := (32409989 / 100000000)) (hi := (324099891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 361589) = 1/(361589 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324099891 / 1000000000) (-32409989 / 100000000) (Real.log (361589 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91022009 / 500000000) ≤ -Real.log (1000000 / 1199667) ∧
    -Real.log (1000000 / 1199667) ≤ (182044019 / 1000000000) := by
  have h := checkLog_sound (w := (199667 / 2199667)) (n := 12)
    (lo := (91022009 / 500000000)) (hi := (182044019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199667 / 1000000) = 1/(1000000 / 1199667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91022009 / 500000000) (182044019 / 1000000000) (Real.log (1199667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1199667 / 1000000) = -Real.log (1000000 / 1199667) := by
    rw [show ((1199667 / 1000000) : ℝ) = ((1000000 / 1199667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (222727387 / 1000000000) ≤ -Real.log (800333 / 1000000) ∧
    -Real.log (800333 / 1000000) ≤ (55681847 / 250000000) := by
  have h := checkLog_sound (w := (199667 / 1800333)) (n := 12)
    (lo := (222727387 / 1000000000)) (hi := (55681847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800333) = 1/(800333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55681847 / 250000000) (-222727387 / 1000000000) (Real.log (800333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182310723 / 1000000000) ≤ -Real.log (1000000 / 1199987) ∧
    -Real.log (1000000 / 1199987) ≤ (45577681 / 250000000) := by
  have h := checkLog_sound (w := (199987 / 2199987)) (n := 12)
    (lo := (182310723 / 1000000000)) (hi := (45577681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199987 / 1000000) = 1/(1000000 / 1199987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182310723 / 1000000000) (45577681 / 250000000) (Real.log (1199987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199987 / 1000000) = -Real.log (1000000 / 1199987) := by
    rw [show ((1199987 / 1000000) : ℝ) = ((1000000 / 1199987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (223127301 / 1000000000) ≤ -Real.log (800013 / 1000000) ∧
    -Real.log (800013 / 1000000) ≤ (111563651 / 500000000) := by
  have h := checkLog_sound (w := (199987 / 1800013)) (n := 12)
    (lo := (223127301 / 1000000000)) (hi := (111563651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800013) = 1/(800013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111563651 / 500000000) (-223127301 / 1000000000) (Real.log (800013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (819549131 / 1000000000) ≤ -Real.log (250000000000 / 567369093231) ∧
    -Real.log (250000000000 / 567369093231) ≤ (819549133 / 1000000000) := by
  have h := checkLog_sound (w := (67369093231 / 1067369093231)) (n := 12)
    (lo := (126401951 / 1000000000)) (hi := (3950061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567369093231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567369093231 / 500000000000) = 1/(250000000000 / 567369093231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (819549131 / 1000000000) (819549133 / 1000000000) (Real.log (567369093231 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (567369093231 / 250000000000) = -Real.log (250000000000 / 567369093231) := by
    rw [show ((567369093231 / 250000000000) : ℝ) = ((250000000000 / 567369093231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (164185883 / 200000000) ≤ -Real.log (500000000000 / 1136305528923) ∧
    -Real.log (500000000000 / 1136305528923) ≤ (820929417 / 1000000000) := by
  have h := checkLog_sound (w := (136305528923 / 2136305528923)) (n := 12)
    (lo := (25556447 / 200000000)) (hi := (31945559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136305528923 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1136305528923 / 1000000000000) = 1/(500000000000 / 1136305528923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (164185883 / 200000000) (820929417 / 1000000000) (Real.log (1136305528923 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1136305528923 / 500000000000) = -Real.log (500000000000 / 1136305528923) := by
    rw [show ((1136305528923 / 500000000000) : ℝ) = ((500000000000 / 1136305528923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (56755581 / 100000000) ≤ -Real.log (500000000000 / 881975174197) ∧
    -Real.log (500000000000 / 881975174197) ≤ (567555811 / 1000000000) := by
  have h := checkLog_sound (w := (381975174197 / 1381975174197)) (n := 12)
    (lo := (56755581 / 100000000)) (hi := (567555811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881975174197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881975174197 / 500000000000) = 1/(500000000000 / 881975174197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56755581 / 100000000) (567555811 / 1000000000) (Real.log (881975174197 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (881975174197 / 500000000000) = -Real.log (500000000000 / 881975174197) := by
    rw [show ((881975174197 / 500000000000) : ℝ) = ((500000000000 / 881975174197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (142118517 / 250000000) ≤ -Real.log (100000000000 / 176557085531) ∧
    -Real.log (100000000000 / 176557085531) ≤ (568474069 / 1000000000) := by
  have h := checkLog_sound (w := (76557085531 / 276557085531)) (n := 12)
    (lo := (142118517 / 250000000)) (hi := (568474069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176557085531 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176557085531 / 100000000000) = 1/(100000000000 / 176557085531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (142118517 / 250000000) (568474069 / 1000000000) (Real.log (176557085531 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (176557085531 / 100000000000) = -Real.log (100000000000 / 176557085531) := by
    rw [show ((176557085531 / 100000000000) : ℝ) = ((100000000000 / 176557085531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (202385703 / 500000000) ≤ -Real.log (500000000000 / 749479903989) ∧
    -Real.log (500000000000 / 749479903989) ≤ (404771407 / 1000000000) := by
  have h := checkLog_sound (w := (249479903989 / 1249479903989)) (n := 12)
    (lo := (202385703 / 500000000)) (hi := (404771407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749479903989 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749479903989 / 500000000000) = 1/(500000000000 / 749479903989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (202385703 / 500000000) (404771407 / 1000000000) (Real.log (749479903989 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (749479903989 / 500000000000) = -Real.log (500000000000 / 749479903989) := by
    rw [show ((749479903989 / 500000000000) : ℝ) = ((500000000000 / 749479903989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (50679753 / 125000000) ≤ -Real.log (500000000000 / 749979687831) ∧
    -Real.log (500000000000 / 749979687831) ≤ (16217521 / 40000000) := by
  have h := checkLog_sound (w := (249979687831 / 1249979687831)) (n := 12)
    (lo := (50679753 / 125000000)) (hi := (16217521 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749979687831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749979687831 / 500000000000) = 1/(500000000000 / 749979687831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (50679753 / 125000000) (16217521 / 40000000) (Real.log (749979687831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (749979687831 / 500000000000) = -Real.log (500000000000 / 749979687831) := by
    rw [show ((749979687831 / 500000000000) : ℝ) = ((500000000000 / 749979687831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20408289 / 500000000) ≤ -Real.log (960005199831 / 1000000000000) ∧
    -Real.log (960005199831 / 1000000000000) ≤ (40816579 / 1000000000) := by
  have h := checkLog_sound (w := (39994800169 / 1960005199831)) (n := 12)
    (lo := (20408289 / 500000000)) (hi := (40816579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960005199831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960005199831) = 1/(960005199831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40816579 / 1000000000) (-20408289 / 500000000) (Real.log (960005199831 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40683369 / 1000000000) ≤ -Real.log (960133089111 / 1000000000000) ∧
    -Real.log (960133089111 / 1000000000000) ≤ (4068337 / 100000000) := by
  have h := checkLog_sound (w := (39866910889 / 1960133089111)) (n := 12)
    (lo := (40683369 / 1000000000)) (hi := (4068337 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960133089111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960133089111) = 1/(960133089111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4068337 / 100000000) (-40683369 / 1000000000) (Real.log (960133089111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell236
