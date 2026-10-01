import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0316
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

theorem reflection_log_1_neg : (44034077 / 200000000) ≤ -Real.log (5120 / 6381) ∧
    -Real.log (5120 / 6381) ≤ (110085193 / 500000000) := by
  have h := checkLog_sound (w := (1261 / 11501)) (n := 12)
    (lo := (44034077 / 200000000)) (hi := (110085193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6381 / 5120) = 1/(5120 / 6381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44034077 / 200000000) (110085193 / 500000000) (Real.log (6381 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6381 / 5120) = -Real.log (5120 / 6381) := by
    rw [show ((6381 / 5120) : ℝ) = ((5120 / 6381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (70686589 / 250000000) ≤ -Real.log (3859 / 5120) ∧
    -Real.log (3859 / 5120) ≤ (282746357 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 8979)) (n := 12)
    (lo := (70686589 / 250000000)) (hi := (282746357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3859) = 1/(3859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-282746357 / 1000000000) (-70686589 / 250000000) (Real.log (3859 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43987057 / 200000000) ≤ -Real.log (10240 / 12759) ∧
    -Real.log (10240 / 12759) ≤ (109967643 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 22999)) (n := 12)
    (lo := (43987057 / 200000000)) (hi := (109967643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12759 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12759 / 10240) = 1/(10240 / 12759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43987057 / 200000000) (109967643 / 500000000) (Real.log (12759 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12759 / 10240) = -Real.log (10240 / 12759) := by
    rw [show ((12759 / 10240) : ℝ) = ((10240 / 12759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28235773 / 100000000) ≤ -Real.log (7721 / 10240) ∧
    -Real.log (7721 / 10240) ≤ (282357731 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 17961)) (n := 12)
    (lo := (28235773 / 100000000)) (hi := (282357731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7721) = 1/(7721 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-282357731 / 1000000000) (-28235773 / 100000000) (Real.log (7721 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (400504909 / 1000000000) ≤ -Real.log (2560 / 3821) ∧
    -Real.log (2560 / 3821) ≤ (40050491 / 100000000) := by
  have h := checkLog_sound (w := (1261 / 6381)) (n := 12)
    (lo := (400504909 / 1000000000)) (hi := (40050491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3821 / 2560) = 1/(2560 / 3821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (400504909 / 1000000000) (40050491 / 100000000) (Real.log (3821 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3821 / 2560) = -Real.log (2560 / 3821) := by
    rw [show ((3821 / 2560) : ℝ) = ((2560 / 3821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16960313 / 25000000) ≤ -Real.log (1299 / 2560) ∧
    -Real.log (1299 / 2560) ≤ (678412521 / 1000000000) := by
  have h := checkLog_sound (w := (1261 / 3859)) (n := 12)
    (lo := (16960313 / 25000000)) (hi := (678412521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1299) = 1/(1299 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-678412521 / 1000000000) (-16960313 / 25000000) (Real.log (1299 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (80022453 / 200000000) ≤ -Real.log (5120 / 7639) ∧
    -Real.log (5120 / 7639) ≤ (200056133 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 12759)) (n := 12)
    (lo := (80022453 / 200000000)) (hi := (200056133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7639 / 5120) = 1/(5120 / 7639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (80022453 / 200000000) (200056133 / 500000000) (Real.log (7639 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7639 / 5120) = -Real.log (5120 / 7639) := by
    rw [show ((7639 / 5120) : ℝ) = ((5120 / 7639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (169314613 / 250000000) ≤ -Real.log (2601 / 5120) ∧
    -Real.log (2601 / 5120) ≤ (677258453 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 7721)) (n := 12)
    (lo := (169314613 / 250000000)) (hi := (677258453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2601) = 1/(2601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-677258453 / 1000000000) (-169314613 / 250000000) (Real.log (2601 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9420023 / 31250000) ≤ -Real.log (200000 / 270361) ∧
    -Real.log (200000 / 270361) ≤ (301440737 / 1000000000) := by
  have h := checkLog_sound (w := (70361 / 470361)) (n := 12)
    (lo := (9420023 / 31250000)) (hi := (301440737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270361 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270361 / 200000) = 1/(200000 / 270361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9420023 / 31250000) (301440737 / 1000000000) (Real.log (270361 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (270361 / 200000) = -Real.log (200000 / 270361) := by
    rw [show ((270361 / 200000) : ℝ) = ((200000 / 270361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (433563701 / 1000000000) ≤ -Real.log (129639 / 200000) ∧
    -Real.log (129639 / 200000) ≤ (216781851 / 500000000) := by
  have h := checkLog_sound (w := (70361 / 329639)) (n := 12)
    (lo := (433563701 / 1000000000)) (hi := (216781851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129639) = 1/(129639 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-216781851 / 500000000) (-433563701 / 1000000000) (Real.log (129639 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (150879759 / 500000000) ≤ -Real.log (250000 / 338059) ∧
    -Real.log (250000 / 338059) ≤ (301759519 / 1000000000) := by
  have h := checkLog_sound (w := (88059 / 588059)) (n := 12)
    (lo := (150879759 / 500000000)) (hi := (301759519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338059 / 250000) = 1/(250000 / 338059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (150879759 / 500000000) (301759519 / 1000000000) (Real.log (338059 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (338059 / 250000) = -Real.log (250000 / 338059) := by
    rw [show ((338059 / 250000) : ℝ) = ((250000 / 338059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (217114423 / 500000000) ≤ -Real.log (161941 / 250000) ∧
    -Real.log (161941 / 250000) ≤ (434228847 / 1000000000) := by
  have h := checkLog_sound (w := (88059 / 411941)) (n := 12)
    (lo := (217114423 / 500000000)) (hi := (434228847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161941) = 1/(161941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-434228847 / 1000000000) (-217114423 / 500000000) (Real.log (161941 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45838643 / 200000000) ≤ -Real.log (200000 / 251517) ∧
    -Real.log (200000 / 251517) ≤ (447643 / 1953125) := by
  have h := checkLog_sound (w := (51517 / 451517)) (n := 12)
    (lo := (45838643 / 200000000)) (hi := (447643 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251517 / 200000) = 1/(200000 / 251517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45838643 / 200000000) (447643 / 1953125) (Real.log (251517 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (251517 / 200000) = -Real.log (200000 / 251517) := by
    rw [show ((251517 / 200000) : ℝ) = ((200000 / 251517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74461723 / 250000000) ≤ -Real.log (148483 / 200000) ∧
    -Real.log (148483 / 200000) ≤ (297846893 / 1000000000) := by
  have h := checkLog_sound (w := (51517 / 348483)) (n := 12)
    (lo := (74461723 / 250000000)) (hi := (297846893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148483) = 1/(148483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-297846893 / 1000000000) (-74461723 / 250000000) (Real.log (148483 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229461153 / 1000000000) ≤ -Real.log (500000 / 628961) ∧
    -Real.log (500000 / 628961) ≤ (114730577 / 500000000) := by
  have h := checkLog_sound (w := (128961 / 1128961)) (n := 12)
    (lo := (229461153 / 1000000000)) (hi := (114730577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628961 / 500000) = 1/(500000 / 628961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229461153 / 1000000000) (114730577 / 500000000) (Real.log (628961 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (628961 / 500000) = -Real.log (500000 / 628961) := by
    rw [show ((628961 / 500000) : ℝ) = ((500000 / 628961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7457523 / 25000000) ≤ -Real.log (371039 / 500000) ∧
    -Real.log (371039 / 500000) ≤ (298300921 / 1000000000) := by
  have h := checkLog_sound (w := (128961 / 871039)) (n := 12)
    (lo := (7457523 / 25000000)) (hi := (298300921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371039) = 1/(371039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-298300921 / 1000000000) (-7457523 / 25000000) (Real.log (371039 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (735004437 / 1000000000) ≤ -Real.log (500000000000 / 1042745624387) ∧
    -Real.log (500000000000 / 1042745624387) ≤ (735004439 / 1000000000) := by
  have h := checkLog_sound (w := (42745624387 / 2042745624387)) (n := 12)
    (lo := (41857257 / 1000000000)) (hi := (20928629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1042745624387 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1042745624387 / 1000000000000) = 1/(500000000000 / 1042745624387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (735004437 / 1000000000) (735004439 / 1000000000) (Real.log (1042745624387 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1042745624387 / 500000000000) = -Real.log (500000000000 / 1042745624387) := by
    rw [show ((1042745624387 / 500000000000) : ℝ) = ((500000000000 / 1042745624387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (183997091 / 250000000) ≤ -Real.log (62500000000 / 130471514317) ∧
    -Real.log (62500000000 / 130471514317) ≤ (367994183 / 500000000) := by
  have h := checkLog_sound (w := (5471514317 / 255471514317)) (n := 12)
    (lo := (1338787 / 31250000)) (hi := (8568237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130471514317 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(130471514317 / 125000000000) = 1/(62500000000 / 130471514317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (183997091 / 250000000) (367994183 / 500000000) (Real.log (130471514317 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (130471514317 / 62500000000) = -Real.log (62500000000 / 130471514317) := by
    rw [show ((130471514317 / 62500000000) : ℝ) = ((62500000000 / 130471514317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (131760027 / 250000000) ≤ -Real.log (125000000000 / 211738885933) ∧
    -Real.log (125000000000 / 211738885933) ≤ (527040109 / 1000000000) := by
  have h := checkLog_sound (w := (86738885933 / 336738885933)) (n := 12)
    (lo := (131760027 / 250000000)) (hi := (527040109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211738885933 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211738885933 / 125000000000) = 1/(125000000000 / 211738885933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (131760027 / 250000000) (527040109 / 1000000000) (Real.log (211738885933 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (211738885933 / 125000000000) = -Real.log (125000000000 / 211738885933) := by
    rw [show ((211738885933 / 125000000000) : ℝ) = ((125000000000 / 211738885933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (527762073 / 1000000000) ≤ -Real.log (125000000000 / 211891809217) ∧
    -Real.log (125000000000 / 211891809217) ≤ (263881037 / 500000000) := by
  have h := checkLog_sound (w := (86891809217 / 336891809217)) (n := 12)
    (lo := (527762073 / 1000000000)) (hi := (263881037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211891809217 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211891809217 / 125000000000) = 1/(125000000000 / 211891809217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (527762073 / 1000000000) (263881037 / 500000000) (Real.log (211891809217 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (211891809217 / 125000000000) = -Real.log (125000000000 / 211891809217) := by
    rw [show ((211891809217 / 125000000000) : ℝ) = ((125000000000 / 211891809217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0316
