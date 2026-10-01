import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0323
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

theorem reflection_log_1_neg : (341443 / 1562500) ≤ -Real.log (10240 / 12741) ∧
    -Real.log (10240 / 12741) ≤ (218523521 / 1000000000) := by
  have h := checkLog_sound (w := (2501 / 22981)) (n := 12)
    (lo := (341443 / 1562500)) (hi := (218523521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12741 / 10240) = 1/(10240 / 12741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341443 / 1562500) (218523521 / 1000000000) (Real.log (12741 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12741 / 10240) = -Real.log (10240 / 12741) := by
    rw [show ((12741 / 10240) : ℝ) = ((10240 / 12741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280029139 / 1000000000) ≤ -Real.log (7739 / 10240) ∧
    -Real.log (7739 / 10240) ≤ (14001457 / 50000000) := by
  have h := checkLog_sound (w := (2501 / 17979)) (n := 12)
    (lo := (280029139 / 1000000000)) (hi := (14001457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7739) = 1/(7739 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14001457 / 50000000) (-280029139 / 1000000000) (Real.log (7739 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6821501 / 31250000) ≤ -Real.log (5120 / 6369) ∧
    -Real.log (5120 / 6369) ≤ (218288033 / 1000000000) := by
  have h := checkLog_sound (w := (1249 / 11489)) (n := 12)
    (lo := (6821501 / 31250000)) (hi := (218288033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6369 / 5120) = 1/(5120 / 6369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6821501 / 31250000) (218288033 / 1000000000) (Real.log (6369 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6369 / 5120) = -Real.log (5120 / 6369) := by
    rw [show ((6369 / 5120) : ℝ) = ((5120 / 6369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (279641567 / 1000000000) ≤ -Real.log (3871 / 5120) ∧
    -Real.log (3871 / 5120) ≤ (8738799 / 31250000) := by
  have h := checkLog_sound (w := (1249 / 8991)) (n := 12)
    (lo := (279641567 / 1000000000)) (hi := (8738799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3871) = 1/(3871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8738799 / 31250000) (-279641567 / 1000000000) (Real.log (3871 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (79550631 / 200000000) ≤ -Real.log (5120 / 7621) ∧
    -Real.log (5120 / 7621) ≤ (99438289 / 250000000) := by
  have h := checkLog_sound (w := (2501 / 12741)) (n := 12)
    (lo := (79550631 / 200000000)) (hi := (99438289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7621 / 5120) = 1/(5120 / 7621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (79550631 / 200000000) (99438289 / 250000000) (Real.log (7621 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7621 / 5120) = -Real.log (5120 / 7621) := by
    rw [show ((7621 / 5120) : ℝ) = ((5120 / 7621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (670361873 / 1000000000) ≤ -Real.log (2619 / 5120) ∧
    -Real.log (2619 / 5120) ≤ (335180937 / 500000000) := by
  have h := checkLog_sound (w := (2501 / 7739)) (n := 12)
    (lo := (670361873 / 1000000000)) (hi := (335180937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2619) = 1/(2619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-335180937 / 500000000) (-670361873 / 1000000000) (Real.log (2619 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (397359429 / 1000000000) ≤ -Real.log (2560 / 3809) ∧
    -Real.log (2560 / 3809) ≤ (39735943 / 100000000) := by
  have h := checkLog_sound (w := (1249 / 6369)) (n := 12)
    (lo := (397359429 / 1000000000)) (hi := (39735943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3809 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3809 / 2560) = 1/(2560 / 3809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (397359429 / 1000000000) (39735943 / 100000000) (Real.log (3809 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3809 / 2560) = -Real.log (2560 / 3809) := by
    rw [show ((3809 / 2560) : ℝ) = ((2560 / 3809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (669217053 / 1000000000) ≤ -Real.log (1311 / 2560) ∧
    -Real.log (1311 / 2560) ≤ (334608527 / 500000000) := by
  have h := checkLog_sound (w := (1249 / 3871)) (n := 12)
    (lo := (669217053 / 1000000000)) (hi := (334608527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1311) = 1/(1311 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334608527 / 500000000) (-669217053 / 1000000000) (Real.log (1311 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74803827 / 250000000) ≤ -Real.log (625 / 843) ∧
    -Real.log (625 / 843) ≤ (299215309 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 734)) (n := 12)
    (lo := (74803827 / 250000000)) (hi := (299215309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 625) = 1/(625 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74803827 / 250000000) (299215309 / 1000000000) (Real.log (843 / 625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (843 / 625) = -Real.log (625 / 843) := by
    rw [show ((843 / 625) : ℝ) = ((625 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13404327 / 31250000) ≤ -Real.log (407 / 625) ∧
    -Real.log (407 / 625) ≤ (85787693 / 200000000) := by
  have h := checkLog_sound (w := (109 / 516)) (n := 12)
    (lo := (13404327 / 31250000)) (hi := (85787693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 407) = 1/(407 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-85787693 / 200000000) (-13404327 / 31250000) (Real.log (407 / 625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (748837 / 2500000) ≤ -Real.log (1000000 / 1349231) ∧
    -Real.log (1000000 / 1349231) ≤ (299534801 / 1000000000) := by
  have h := checkLog_sound (w := (349231 / 2349231)) (n := 12)
    (lo := (748837 / 2500000)) (hi := (299534801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349231 / 1000000) = 1/(1000000 / 1349231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (748837 / 2500000) (299534801 / 1000000000) (Real.log (1349231 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1349231 / 1000000) = -Real.log (1000000 / 1349231) := by
    rw [show ((1349231 / 1000000) : ℝ) = ((1000000 / 1349231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214800269 / 500000000) ≤ -Real.log (650769 / 1000000) ∧
    -Real.log (650769 / 1000000) ≤ (429600539 / 1000000000) := by
  have h := checkLog_sound (w := (349231 / 1650769)) (n := 12)
    (lo := (214800269 / 500000000)) (hi := (429600539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 650769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 650769) = 1/(650769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-429600539 / 1000000000) (-214800269 / 500000000) (Real.log (650769 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227319619 / 1000000000) ≤ -Real.log (1000000 / 1255231) ∧
    -Real.log (1000000 / 1255231) ≤ (11365981 / 50000000) := by
  have h := checkLog_sound (w := (255231 / 2255231)) (n := 12)
    (lo := (227319619 / 1000000000)) (hi := (11365981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255231 / 1000000) = 1/(1000000 / 1255231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227319619 / 1000000000) (11365981 / 50000000) (Real.log (1255231 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255231 / 1000000) = -Real.log (1000000 / 1255231) := by
    rw [show ((1255231 / 1000000) : ℝ) = ((1000000 / 1255231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11787247 / 40000000) ≤ -Real.log (744769 / 1000000) ∧
    -Real.log (744769 / 1000000) ≤ (36835147 / 125000000) := by
  have h := checkLog_sound (w := (255231 / 1744769)) (n := 12)
    (lo := (11787247 / 40000000)) (hi := (36835147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744769) = 1/(744769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-36835147 / 125000000) (-11787247 / 40000000) (Real.log (744769 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (227588059 / 1000000000) ≤ -Real.log (62500 / 78473) ∧
    -Real.log (62500 / 78473) ≤ (11379403 / 50000000) := by
  have h := checkLog_sound (w := (15973 / 140973)) (n := 12)
    (lo := (227588059 / 1000000000)) (hi := (11379403 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78473 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78473 / 62500) = 1/(62500 / 78473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (227588059 / 1000000000) (11379403 / 50000000) (Real.log (78473 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78473 / 62500) = -Real.log (62500 / 78473) := by
    rw [show ((78473 / 62500) : ℝ) = ((62500 / 78473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (295133767 / 1000000000) ≤ -Real.log (46527 / 62500) ∧
    -Real.log (46527 / 62500) ≤ (36891721 / 125000000) := by
  have h := checkLog_sound (w := (15973 / 109027)) (n := 12)
    (lo := (295133767 / 1000000000)) (hi := (36891721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46527) = 1/(46527 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-36891721 / 125000000) (-295133767 / 1000000000) (Real.log (46527 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (728153771 / 1000000000) ≤ -Real.log (250000000000 / 517813267813) ∧
    -Real.log (250000000000 / 517813267813) ≤ (728153773 / 1000000000) := by
  have h := checkLog_sound (w := (17813267813 / 1017813267813)) (n := 12)
    (lo := (35006591 / 1000000000)) (hi := (273489 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517813267813 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517813267813 / 500000000000) = 1/(250000000000 / 517813267813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (728153771 / 1000000000) (728153773 / 1000000000) (Real.log (517813267813 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (517813267813 / 250000000000) = -Real.log (250000000000 / 517813267813) := by
    rw [show ((517813267813 / 250000000000) : ℝ) = ((250000000000 / 517813267813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (364567669 / 500000000) ≤ -Real.log (250000000000 / 518321785457) ∧
    -Real.log (250000000000 / 518321785457) ≤ (36456767 / 50000000) := by
  have h := checkLog_sound (w := (18321785457 / 1018321785457)) (n := 12)
    (lo := (17994079 / 500000000)) (hi := (35988159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518321785457 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518321785457 / 500000000000) = 1/(250000000000 / 518321785457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (364567669 / 500000000) (36456767 / 50000000) (Real.log (518321785457 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (518321785457 / 250000000000) = -Real.log (250000000000 / 518321785457) := by
    rw [show ((518321785457 / 250000000000) : ℝ) = ((250000000000 / 518321785457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104400159 / 200000000) ≤ -Real.log (62500000000 / 105337275719) ∧
    -Real.log (62500000000 / 105337275719) ≤ (130500199 / 250000000) := by
  have h := checkLog_sound (w := (42837275719 / 167837275719)) (n := 12)
    (lo := (104400159 / 200000000)) (hi := (130500199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105337275719 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105337275719 / 62500000000) = 1/(62500000000 / 105337275719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104400159 / 200000000) (130500199 / 250000000) (Real.log (105337275719 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (105337275719 / 62500000000) = -Real.log (62500000000 / 105337275719) := by
    rw [show ((105337275719 / 62500000000) : ℝ) = ((62500000000 / 105337275719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (522721827 / 1000000000) ≤ -Real.log (100000000000 / 168661207471) ∧
    -Real.log (100000000000 / 168661207471) ≤ (130680457 / 250000000) := by
  have h := checkLog_sound (w := (68661207471 / 268661207471)) (n := 12)
    (lo := (522721827 / 1000000000)) (hi := (130680457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168661207471 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168661207471 / 100000000000) = 1/(100000000000 / 168661207471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (522721827 / 1000000000) (130680457 / 250000000) (Real.log (168661207471 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (168661207471 / 100000000000) = -Real.log (100000000000 / 168661207471) := by
    rw [show ((168661207471 / 100000000000) : ℝ) = ((100000000000 / 168661207471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0323
