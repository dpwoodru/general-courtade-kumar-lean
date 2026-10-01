import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0294
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

theorem reflection_log_1_neg : (112664331 / 500000000) ≤ -Real.log (2560 / 3207) ∧
    -Real.log (2560 / 3207) ≤ (225328663 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 5767)) (n := 12)
    (lo := (112664331 / 500000000)) (hi := (225328663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3207 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3207 / 2560) = 1/(2560 / 3207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (112664331 / 500000000) (225328663 / 1000000000) (Real.log (3207 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3207 / 2560) = -Real.log (2560 / 3207) := by
    rw [show ((3207 / 2560) : ℝ) = ((2560 / 3207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36416821 / 125000000) ≤ -Real.log (1913 / 2560) ∧
    -Real.log (1913 / 2560) ≤ (291334569 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 4473)) (n := 12)
    (lo := (36416821 / 125000000)) (hi := (291334569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1913) = 1/(1913 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-291334569 / 1000000000) (-36416821 / 125000000) (Real.log (1913 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225094771 / 1000000000) ≤ -Real.log (2048 / 2565) ∧
    -Real.log (2048 / 2565) ≤ (56273693 / 250000000) := by
  have h := checkLog_sound (w := (517 / 4613)) (n := 12)
    (lo := (225094771 / 1000000000)) (hi := (56273693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2565 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2565 / 2048) = 1/(2048 / 2565) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225094771 / 1000000000) (56273693 / 250000000) (Real.log (2565 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2565 / 2048) = -Real.log (2048 / 2565) := by
    rw [show ((2565 / 2048) : ℝ) = ((2048 / 2565) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29094259 / 100000000) ≤ -Real.log (1531 / 2048) ∧
    -Real.log (1531 / 2048) ≤ (290942591 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 3579)) (n := 12)
    (lo := (29094259 / 100000000)) (hi := (290942591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1531) = 1/(1531 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290942591 / 1000000000) (-29094259 / 100000000) (Real.log (1531 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (409104311 / 1000000000) ≤ -Real.log (1280 / 1927) ∧
    -Real.log (1280 / 1927) ≤ (51138039 / 125000000) := by
  have h := checkLog_sound (w := (647 / 3207)) (n := 12)
    (lo := (409104311 / 1000000000)) (hi := (51138039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927 / 1280) = 1/(1280 / 1927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (409104311 / 1000000000) (51138039 / 125000000) (Real.log (1927 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1927 / 1280) = -Real.log (1280 / 1927) := by
    rw [show ((1927 / 1280) : ℝ) = ((1280 / 1927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (352072467 / 500000000) ≤ -Real.log (633 / 1280) ∧
    -Real.log (633 / 1280) ≤ (88018117 / 125000000) := by
  have h := checkLog_sound (w := (7 / 1273)) (n := 12)
    (lo := (5498877 / 500000000)) (hi := (2199551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 633) = 1/(633 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-88018117 / 125000000) (-352072467 / 500000000) (Real.log (633 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (408715029 / 1000000000) ≤ -Real.log (1024 / 1541) ∧
    -Real.log (1024 / 1541) ≤ (40871503 / 100000000) := by
  have h := checkLog_sound (w := (517 / 2565)) (n := 12)
    (lo := (408715029 / 1000000000)) (hi := (40871503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1541 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1541 / 1024) = 1/(1024 / 1541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (408715029 / 1000000000) (40871503 / 100000000) (Real.log (1541 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1541 / 1024) = -Real.log (1024 / 1541) := by
    rw [show ((1541 / 1024) : ℝ) = ((1024 / 1541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (702960801 / 1000000000) ≤ -Real.log (507 / 1024) ∧
    -Real.log (507 / 1024) ≤ (702960803 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 1019)) (n := 12)
    (lo := (9813621 / 1000000000)) (hi := (4906811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 507) = 1/(507 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-702960803 / 1000000000) (-702960801 / 1000000000) (Real.log (507 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (308413679 / 1000000000) ≤ -Real.log (62500 / 85079) ∧
    -Real.log (62500 / 85079) ≤ (3855171 / 12500000) := by
  have h := checkLog_sound (w := (22579 / 147579)) (n := 12)
    (lo := (308413679 / 1000000000)) (hi := (3855171 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85079 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85079 / 62500) = 1/(62500 / 85079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (308413679 / 1000000000) (3855171 / 12500000) (Real.log (85079 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (85079 / 62500) = -Real.log (62500 / 85079) := by
    rw [show ((85079 / 62500) : ℝ) = ((62500 / 85079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89652811 / 200000000) ≤ -Real.log (39921 / 62500) ∧
    -Real.log (39921 / 62500) ≤ (56033007 / 125000000) := by
  have h := checkLog_sound (w := (22579 / 102421)) (n := 12)
    (lo := (89652811 / 200000000)) (hi := (56033007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 39921) = 1/(39921 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-56033007 / 125000000) (-89652811 / 200000000) (Real.log (39921 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308730247 / 1000000000) ≤ -Real.log (200000 / 272339) ∧
    -Real.log (200000 / 272339) ≤ (38591281 / 125000000) := by
  have h := checkLog_sound (w := (72339 / 472339)) (n := 12)
    (lo := (308730247 / 1000000000)) (hi := (38591281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272339 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272339 / 200000) = 1/(200000 / 272339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308730247 / 1000000000) (38591281 / 125000000) (Real.log (272339 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (272339 / 200000) = -Real.log (200000 / 272339) := by
    rw [show ((272339 / 200000) : ℝ) = ((200000 / 272339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (448939053 / 1000000000) ≤ -Real.log (127661 / 200000) ∧
    -Real.log (127661 / 200000) ≤ (224469527 / 500000000) := by
  have h := checkLog_sound (w := (72339 / 327661)) (n := 12)
    (lo := (448939053 / 1000000000)) (hi := (224469527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127661) = 1/(127661 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224469527 / 500000000) (-448939053 / 1000000000) (Real.log (127661 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58771983 / 250000000) ≤ -Real.log (50000 / 63251) ∧
    -Real.log (50000 / 63251) ≤ (235087933 / 1000000000) := by
  have h := checkLog_sound (w := (13251 / 113251)) (n := 12)
    (lo := (58771983 / 250000000)) (hi := (235087933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63251 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63251 / 50000) = 1/(50000 / 63251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58771983 / 250000000) (235087933 / 1000000000) (Real.log (63251 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63251 / 50000) = -Real.log (50000 / 63251) := by
    rw [show ((63251 / 50000) : ℝ) = ((50000 / 63251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (307911991 / 1000000000) ≤ -Real.log (36749 / 50000) ∧
    -Real.log (36749 / 50000) ≤ (38488999 / 125000000) := by
  have h := checkLog_sound (w := (13251 / 86749)) (n := 12)
    (lo := (307911991 / 1000000000)) (hi := (38488999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36749) = 1/(36749 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38488999 / 125000000) (-307911991 / 1000000000) (Real.log (36749 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14709841 / 62500000) ≤ -Real.log (1000000 / 1265361) ∧
    -Real.log (1000000 / 1265361) ≤ (235357457 / 1000000000) := by
  have h := checkLog_sound (w := (265361 / 2265361)) (n := 12)
    (lo := (14709841 / 62500000)) (hi := (235357457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265361 / 1000000) = 1/(1000000 / 1265361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14709841 / 62500000) (235357457 / 1000000000) (Real.log (1265361 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1265361 / 1000000) = -Real.log (1000000 / 1265361) := by
    rw [show ((1265361 / 1000000) : ℝ) = ((1000000 / 1265361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (38547007 / 125000000) ≤ -Real.log (734639 / 1000000) ∧
    -Real.log (734639 / 1000000) ≤ (308376057 / 1000000000) := by
  have h := checkLog_sound (w := (265361 / 1734639)) (n := 12)
    (lo := (38547007 / 125000000)) (hi := (308376057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734639) = 1/(734639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-308376057 / 1000000000) (-38547007 / 125000000) (Real.log (734639 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (378338867 / 500000000) ≤ -Real.log (500000000000 / 1065592044287) ∧
    -Real.log (500000000000 / 1065592044287) ≤ (94584717 / 125000000) := by
  have h := checkLog_sound (w := (65592044287 / 2065592044287)) (n := 12)
    (lo := (31765277 / 500000000)) (hi := (12706111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1065592044287 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1065592044287 / 1000000000000) = 1/(500000000000 / 1065592044287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (378338867 / 500000000) (94584717 / 125000000) (Real.log (1065592044287 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1065592044287 / 500000000000) = -Real.log (500000000000 / 1065592044287) := by
    rw [show ((1065592044287 / 500000000000) : ℝ) = ((500000000000 / 1065592044287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7576693 / 10000000) ≤ -Real.log (250000000000 / 533324586209) ∧
    -Real.log (250000000000 / 533324586209) ≤ (378834651 / 500000000) := by
  have h := checkLog_sound (w := (33324586209 / 1033324586209)) (n := 12)
    (lo := (1613053 / 25000000)) (hi := (64522121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533324586209 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533324586209 / 500000000000) = 1/(250000000000 / 533324586209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7576693 / 10000000) (378834651 / 500000000) (Real.log (533324586209 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (533324586209 / 250000000000) = -Real.log (250000000000 / 533324586209) := by
    rw [show ((533324586209 / 250000000000) : ℝ) = ((250000000000 / 533324586209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (542999923 / 1000000000) ≤ -Real.log (100000000000 / 172116248061) ∧
    -Real.log (100000000000 / 172116248061) ≤ (135749981 / 250000000) := by
  have h := checkLog_sound (w := (72116248061 / 272116248061)) (n := 12)
    (lo := (542999923 / 1000000000)) (hi := (135749981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172116248061 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172116248061 / 100000000000) = 1/(100000000000 / 172116248061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (542999923 / 1000000000) (135749981 / 250000000) (Real.log (172116248061 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (172116248061 / 100000000000) = -Real.log (100000000000 / 172116248061) := by
    rw [show ((172116248061 / 100000000000) : ℝ) = ((100000000000 / 172116248061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (543733513 / 1000000000) ≤ -Real.log (15625000000 / 26912899567) ∧
    -Real.log (15625000000 / 26912899567) ≤ (271866757 / 500000000) := by
  have h := checkLog_sound (w := (11287899567 / 42537899567)) (n := 12)
    (lo := (543733513 / 1000000000)) (hi := (271866757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26912899567 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26912899567 / 15625000000) = 1/(15625000000 / 26912899567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (543733513 / 1000000000) (271866757 / 500000000) (Real.log (26912899567 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26912899567 / 15625000000) = -Real.log (15625000000 / 26912899567) := by
    rw [show ((26912899567 / 15625000000) : ℝ) = ((15625000000 / 26912899567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0294
