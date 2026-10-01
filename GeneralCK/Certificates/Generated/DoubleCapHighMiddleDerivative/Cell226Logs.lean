import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell226
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

theorem reflection_log_1_neg : (324260701 / 1000000000) ≤ -Real.log (5120 / 7081) ∧
    -Real.log (5120 / 7081) ≤ (162130351 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 12201)) (n := 12)
    (lo := (324260701 / 1000000000)) (hi := (162130351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7081 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7081 / 5120) = 1/(5120 / 7081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324260701 / 1000000000) (162130351 / 500000000) (Real.log (7081 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7081 / 5120) = -Real.log (5120 / 7081) := by
    rw [show ((7081 / 5120) : ℝ) = ((5120 / 7081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (482898917 / 1000000000) ≤ -Real.log (3159 / 5120) ∧
    -Real.log (3159 / 5120) ≤ (241449459 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 8279)) (n := 12)
    (lo := (482898917 / 1000000000)) (hi := (241449459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3159) = 1/(3159 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-241449459 / 500000000) (-482898917 / 1000000000) (Real.log (3159 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (161918471 / 500000000) ≤ -Real.log (2560 / 3539) ∧
    -Real.log (2560 / 3539) ≤ (323836943 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 6099)) (n := 12)
    (lo := (161918471 / 500000000)) (hi := (323836943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3539 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3539 / 2560) = 1/(2560 / 3539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (161918471 / 500000000) (323836943 / 1000000000) (Real.log (3539 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3539 / 2560) = -Real.log (2560 / 3539) := by
    rw [show ((3539 / 2560) : ℝ) = ((2560 / 3539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4819497 / 10000000) ≤ -Real.log (1581 / 2560) ∧
    -Real.log (1581 / 2560) ≤ (481949701 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 4141)) (n := 12)
    (lo := (4819497 / 10000000)) (hi := (481949701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1581) = 1/(1581 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-481949701 / 1000000000) (-4819497 / 10000000) (Real.log (1581 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240723317 / 1000000000) ≤ -Real.log (1000000 / 1272169) ∧
    -Real.log (1000000 / 1272169) ≤ (120361659 / 500000000) := by
  have h := checkLog_sound (w := (272169 / 2272169)) (n := 12)
    (lo := (240723317 / 1000000000)) (hi := (120361659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272169 / 1000000) = 1/(1000000 / 1272169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240723317 / 1000000000) (120361659 / 500000000) (Real.log (1272169 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1272169 / 1000000) = -Real.log (1000000 / 1272169) := by
    rw [show ((1272169 / 1000000) : ℝ) = ((1000000 / 1272169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (99277 / 312500) ≤ -Real.log (727831 / 1000000) ∧
    -Real.log (727831 / 1000000) ≤ (317686401 / 1000000000) := by
  have h := checkLog_sound (w := (272169 / 1727831)) (n := 12)
    (lo := (99277 / 312500)) (hi := (317686401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727831) = 1/(727831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317686401 / 1000000000) (-99277 / 312500) (Real.log (727831 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48211153 / 200000000) ≤ -Real.log (62500 / 79537) ∧
    -Real.log (62500 / 79537) ≤ (120527883 / 500000000) := by
  have h := checkLog_sound (w := (17037 / 142037)) (n := 12)
    (lo := (48211153 / 200000000)) (hi := (120527883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79537 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79537 / 62500) = 1/(62500 / 79537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48211153 / 200000000) (120527883 / 500000000) (Real.log (79537 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (79537 / 62500) = -Real.log (62500 / 79537) := by
    rw [show ((79537 / 62500) : ℝ) = ((62500 / 79537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (79566937 / 250000000) ≤ -Real.log (45463 / 62500) ∧
    -Real.log (45463 / 62500) ≤ (318267749 / 1000000000) := by
  have h := checkLog_sound (w := (17037 / 107963)) (n := 12)
    (lo := (79566937 / 250000000)) (hi := (318267749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45463) = 1/(45463 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-318267749 / 1000000000) (-79566937 / 250000000) (Real.log (45463 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8969321 / 50000000) ≤ -Real.log (1000000 / 1196483) ∧
    -Real.log (1000000 / 1196483) ≤ (179386421 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 2196483)) (n := 12)
    (lo := (8969321 / 50000000)) (hi := (179386421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196483 / 1000000) = 1/(1000000 / 1196483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8969321 / 50000000) (179386421 / 1000000000) (Real.log (1196483 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1196483 / 1000000) = -Real.log (1000000 / 1196483) := by
    rw [show ((1196483 / 1000000) : ℝ) = ((1000000 / 1196483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27344617 / 125000000) ≤ -Real.log (803517 / 1000000) ∧
    -Real.log (803517 / 1000000) ≤ (218756937 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 1803517)) (n := 12)
    (lo := (27344617 / 125000000)) (hi := (218756937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803517) = 1/(803517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218756937 / 1000000000) (-27344617 / 125000000) (Real.log (803517 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (179652999 / 1000000000) ≤ -Real.log (500000 / 598401) ∧
    -Real.log (500000 / 598401) ≤ (179653 / 1000000) := by
  have h := checkLog_sound (w := (98401 / 1098401)) (n := 12)
    (lo := (179652999 / 1000000000)) (hi := (179653 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598401 / 500000) = 1/(500000 / 598401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (179652999 / 1000000000) (179653 / 1000000) (Real.log (598401 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (598401 / 500000) = -Real.log (500000 / 598401) := by
    rw [show ((598401 / 500000) : ℝ) = ((500000 / 598401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10957701 / 50000000) ≤ -Real.log (401599 / 500000) ∧
    -Real.log (401599 / 500000) ≤ (219154021 / 1000000000) := by
  have h := checkLog_sound (w := (98401 / 901599)) (n := 12)
    (lo := (10957701 / 50000000)) (hi := (219154021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401599) = 1/(401599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219154021 / 1000000000) (-10957701 / 50000000) (Real.log (401599 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (402893321 / 500000000) ≤ -Real.log (100000000000 / 223845667299) ∧
    -Real.log (100000000000 / 223845667299) ≤ (201446661 / 250000000) := by
  have h := checkLog_sound (w := (23845667299 / 423845667299)) (n := 12)
    (lo := (56319731 / 500000000)) (hi := (112639463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223845667299 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(223845667299 / 200000000000) = 1/(100000000000 / 223845667299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (402893321 / 500000000) (201446661 / 250000000) (Real.log (223845667299 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (223845667299 / 100000000000) = -Real.log (100000000000 / 223845667299) := by
    rw [show ((223845667299 / 100000000000) : ℝ) = ((100000000000 / 223845667299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (403579809 / 500000000) ≤ -Real.log (500000000000 / 1120766065211) ∧
    -Real.log (500000000000 / 1120766065211) ≤ (40357981 / 50000000) := by
  have h := checkLog_sound (w := (120766065211 / 2120766065211)) (n := 12)
    (lo := (57006219 / 500000000)) (hi := (114012439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120766065211 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120766065211 / 1000000000000) = 1/(500000000000 / 1120766065211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (403579809 / 500000000) (40357981 / 50000000) (Real.log (1120766065211 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1120766065211 / 500000000000) = -Real.log (500000000000 / 1120766065211) := by
    rw [show ((1120766065211 / 500000000000) : ℝ) = ((500000000000 / 1120766065211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (279204859 / 500000000) ≤ -Real.log (500000000000 / 873945325219) ∧
    -Real.log (500000000000 / 873945325219) ≤ (558409719 / 1000000000) := by
  have h := checkLog_sound (w := (373945325219 / 1373945325219)) (n := 12)
    (lo := (279204859 / 500000000)) (hi := (558409719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873945325219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873945325219 / 500000000000) = 1/(500000000000 / 873945325219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (279204859 / 500000000) (558409719 / 1000000000) (Real.log (873945325219 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (873945325219 / 500000000000) = -Real.log (500000000000 / 873945325219) := by
    rw [show ((873945325219 / 500000000000) : ℝ) = ((500000000000 / 873945325219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (559323513 / 1000000000) ≤ -Real.log (500000000000 / 874744297561) ∧
    -Real.log (500000000000 / 874744297561) ≤ (279661757 / 500000000) := by
  have h := checkLog_sound (w := (374744297561 / 1374744297561)) (n := 12)
    (lo := (559323513 / 1000000000)) (hi := (279661757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874744297561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874744297561 / 500000000000) = 1/(500000000000 / 874744297561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (559323513 / 1000000000) (279661757 / 500000000) (Real.log (874744297561 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (874744297561 / 500000000000) = -Real.log (500000000000 / 874744297561) := by
    rw [show ((874744297561 / 500000000000) : ℝ) = ((500000000000 / 874744297561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (99535839 / 250000000) ≤ -Real.log (125000000000 / 186132185131) ∧
    -Real.log (125000000000 / 186132185131) ≤ (398143357 / 1000000000) := by
  have h := checkLog_sound (w := (61132185131 / 311132185131)) (n := 12)
    (lo := (99535839 / 250000000)) (hi := (398143357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186132185131 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186132185131 / 125000000000) = 1/(125000000000 / 186132185131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (99535839 / 250000000) (398143357 / 1000000000) (Real.log (186132185131 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (186132185131 / 125000000000) = -Real.log (125000000000 / 186132185131) := by
    rw [show ((186132185131 / 125000000000) : ℝ) = ((125000000000 / 186132185131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (398807019 / 1000000000) ≤ -Real.log (125000000000 / 186255755119) ∧
    -Real.log (125000000000 / 186255755119) ≤ (19940351 / 50000000) := by
  have h := checkLog_sound (w := (61255755119 / 311255755119)) (n := 12)
    (lo := (398807019 / 1000000000)) (hi := (19940351 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186255755119 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186255755119 / 125000000000) = 1/(125000000000 / 186255755119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (398807019 / 1000000000) (19940351 / 50000000) (Real.log (186255755119 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (186255755119 / 125000000000) = -Real.log (125000000000 / 186255755119) := by
    rw [show ((186255755119 / 125000000000) : ℝ) = ((125000000000 / 186255755119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1975051 / 50000000) ≤ -Real.log (240317243199 / 250000000000) ∧
    -Real.log (240317243199 / 250000000000) ≤ (39501021 / 1000000000) := by
  have h := checkLog_sound (w := (9682756801 / 490317243199)) (n := 12)
    (lo := (1975051 / 50000000)) (hi := (39501021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240317243199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240317243199) = 1/(240317243199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-39501021 / 1000000000) (-1975051 / 50000000) (Real.log (240317243199 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9842629 / 250000000) ≤ -Real.log (961394430711 / 1000000000000) ∧
    -Real.log (961394430711 / 1000000000000) ≤ (39370517 / 1000000000) := by
  have h := checkLog_sound (w := (38605569289 / 1961394430711)) (n := 12)
    (lo := (9842629 / 250000000)) (hi := (39370517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961394430711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961394430711) = 1/(961394430711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-39370517 / 1000000000) (-9842629 / 250000000) (Real.log (961394430711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell226
