import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0173
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

theorem reflection_log_1_neg : (277720511 / 1000000000) ≤ -Real.log (5120 / 6759) ∧
    -Real.log (5120 / 6759) ≤ (4339383 / 15625000) := by
  have h := checkLog_sound (w := (1639 / 11879)) (n := 12)
    (lo := (277720511 / 1000000000)) (hi := (4339383 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6759 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6759 / 5120) = 1/(5120 / 6759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277720511 / 1000000000) (4339383 / 15625000) (Real.log (6759 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6759 / 5120) = -Real.log (5120 / 6759) := by
    rw [show ((6759 / 5120) : ℝ) = ((5120 / 6759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38583483 / 100000000) ≤ -Real.log (3481 / 5120) ∧
    -Real.log (3481 / 5120) ≤ (385834831 / 1000000000) := by
  have h := checkLog_sound (w := (1639 / 8601)) (n := 12)
    (lo := (38583483 / 100000000)) (hi := (385834831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3481) = 1/(3481 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-385834831 / 1000000000) (-38583483 / 100000000) (Real.log (3481 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277276559 / 1000000000) ≤ -Real.log (1280 / 1689) ∧
    -Real.log (1280 / 1689) ≤ (3465957 / 12500000) := by
  have h := checkLog_sound (w := (409 / 2969)) (n := 12)
    (lo := (277276559 / 1000000000)) (hi := (3465957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1280) = 1/(1280 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (277276559 / 1000000000) (3465957 / 12500000) (Real.log (1689 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1689 / 1280) = -Real.log (1280 / 1689) := by
    rw [show ((1689 / 1280) : ℝ) = ((1280 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19248669 / 50000000) ≤ -Real.log (871 / 1280) ∧
    -Real.log (871 / 1280) ≤ (384973381 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2151)) (n := 12)
    (lo := (19248669 / 50000000)) (hi := (384973381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 871) = 1/(871 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-384973381 / 1000000000) (-19248669 / 50000000) (Real.log (871 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (494839143 / 1000000000) ≤ -Real.log (2560 / 4199) ∧
    -Real.log (2560 / 4199) ≤ (61854893 / 125000000) := by
  have h := checkLog_sound (w := (1639 / 6759)) (n := 12)
    (lo := (494839143 / 1000000000)) (hi := (61854893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4199 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4199 / 2560) = 1/(2560 / 4199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (494839143 / 1000000000) (61854893 / 125000000) (Real.log (4199 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4199 / 2560) = -Real.log (2560 / 4199) := by
    rw [show ((4199 / 2560) : ℝ) = ((2560 / 4199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (408921 / 400000) ≤ -Real.log (921 / 2560) ∧
    -Real.log (921 / 2560) ≤ (511151251 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 921) = 1/(921 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-511151251 / 500000000) (-408921 / 400000) (Real.log (921 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30882777 / 62500000) ≤ -Real.log (640 / 1049) ∧
    -Real.log (640 / 1049) ≤ (494124433 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 1689)) (n := 12)
    (lo := (30882777 / 62500000)) (hi := (494124433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1049 / 640) = 1/(640 / 1049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30882777 / 62500000) (494124433 / 1000000000) (Real.log (1049 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1049 / 640) = -Real.log (640 / 1049) := by
    rw [show ((1049 / 640) : ℝ) = ((640 / 1049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (203810093 / 200000000) ≤ -Real.log (231 / 640) ∧
    -Real.log (231 / 640) ≤ (1019050467 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 231) = 1/(231 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1019050467 / 1000000000) (-203810093 / 200000000) (Real.log (231 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (94826651 / 250000000) ≤ -Real.log (1000000 / 1461271) ∧
    -Real.log (1000000 / 1461271) ≤ (75861321 / 200000000) := by
  have h := checkLog_sound (w := (461271 / 2461271)) (n := 12)
    (lo := (94826651 / 250000000)) (hi := (75861321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461271 / 1000000) = 1/(1000000 / 1461271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (94826651 / 250000000) (75861321 / 200000000) (Real.log (1461271 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1461271 / 1000000) = -Real.log (1000000 / 1461271) := by
    rw [show ((1461271 / 1000000) : ℝ) = ((1000000 / 1461271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (618542617 / 1000000000) ≤ -Real.log (538729 / 1000000) ∧
    -Real.log (538729 / 1000000) ≤ (309271309 / 500000000) := by
  have h := checkLog_sound (w := (461271 / 1538729)) (n := 12)
    (lo := (618542617 / 1000000000)) (hi := (309271309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 538729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 538729) = 1/(538729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-309271309 / 500000000) (-618542617 / 1000000000) (Real.log (538729 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (189957739 / 500000000) ≤ -Real.log (1000000 / 1462161) ∧
    -Real.log (1000000 / 1462161) ≤ (379915479 / 1000000000) := by
  have h := checkLog_sound (w := (462161 / 2462161)) (n := 12)
    (lo := (189957739 / 500000000)) (hi := (379915479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1462161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1462161 / 1000000) = 1/(1000000 / 1462161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (189957739 / 500000000) (379915479 / 1000000000) (Real.log (1462161 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1462161 / 1000000) = -Real.log (1000000 / 1462161) := by
    rw [show ((1462161 / 1000000) : ℝ) = ((1000000 / 1462161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31009801 / 50000000) ≤ -Real.log (537839 / 1000000) ∧
    -Real.log (537839 / 1000000) ≤ (620196021 / 1000000000) := by
  have h := checkLog_sound (w := (462161 / 1537839)) (n := 12)
    (lo := (31009801 / 50000000)) (hi := (620196021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 537839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 537839) = 1/(537839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-620196021 / 1000000000) (-31009801 / 50000000) (Real.log (537839 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (297526457 / 1000000000) ≤ -Real.log (250000 / 336631) ∧
    -Real.log (250000 / 336631) ≤ (148763229 / 500000000) := by
  have h := checkLog_sound (w := (86631 / 586631)) (n := 12)
    (lo := (297526457 / 1000000000)) (hi := (148763229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336631 / 250000) = 1/(250000 / 336631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (297526457 / 1000000000) (148763229 / 500000000) (Real.log (336631 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (336631 / 250000) = -Real.log (250000 / 336631) := by
    rw [show ((336631 / 250000) : ℝ) = ((250000 / 336631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (425449471 / 1000000000) ≤ -Real.log (163369 / 250000) ∧
    -Real.log (163369 / 250000) ≤ (830956 / 1953125) := by
  have h := checkLog_sound (w := (86631 / 413369)) (n := 12)
    (lo := (425449471 / 1000000000)) (hi := (830956 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163369) = 1/(163369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-830956 / 1953125) (-425449471 / 1000000000) (Real.log (163369 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (37260597 / 125000000) ≤ -Real.log (250000 / 336819) ∧
    -Real.log (250000 / 336819) ≤ (298084777 / 1000000000) := by
  have h := checkLog_sound (w := (86819 / 586819)) (n := 12)
    (lo := (37260597 / 125000000)) (hi := (298084777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336819 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336819 / 250000) = 1/(250000 / 336819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37260597 / 125000000) (298084777 / 1000000000) (Real.log (336819 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (336819 / 250000) = -Real.log (250000 / 336819) := by
    rw [show ((336819 / 250000) : ℝ) = ((250000 / 336819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (426600903 / 1000000000) ≤ -Real.log (163181 / 250000) ∧
    -Real.log (163181 / 250000) ≤ (53325113 / 125000000) := by
  have h := checkLog_sound (w := (86819 / 413181)) (n := 12)
    (lo := (426600903 / 1000000000)) (hi := (53325113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163181) = 1/(163181 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53325113 / 125000000) (-426600903 / 1000000000) (Real.log (163181 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (997849221 / 1000000000) ≤ -Real.log (500000000000 / 1356220845731) ∧
    -Real.log (500000000000 / 1356220845731) ≤ (997849223 / 1000000000) := by
  have h := checkLog_sound (w := (356220845731 / 2356220845731)) (n := 12)
    (lo := (304702041 / 1000000000)) (hi := (152351021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356220845731 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1356220845731 / 1000000000000) = 1/(500000000000 / 1356220845731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (997849221 / 1000000000) (997849223 / 1000000000) (Real.log (1356220845731 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1356220845731 / 500000000000) = -Real.log (500000000000 / 1356220845731) := by
    rw [show ((1356220845731 / 500000000000) : ℝ) = ((500000000000 / 1356220845731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1000111497 / 1000000000) ≤ -Real.log (250000000000 / 679646232423) ∧
    -Real.log (250000000000 / 679646232423) ≤ (1000111499 / 1000000000) := by
  have h := checkLog_sound (w := (179646232423 / 1179646232423)) (n := 12)
    (lo := (306964317 / 1000000000)) (hi := (153482159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679646232423 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(679646232423 / 500000000000) = 1/(250000000000 / 679646232423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1000111497 / 1000000000) (1000111499 / 1000000000) (Real.log (679646232423 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679646232423 / 250000000000) = -Real.log (250000000000 / 679646232423) := by
    rw [show ((679646232423 / 250000000000) : ℝ) = ((250000000000 / 679646232423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (90371991 / 125000000) ≤ -Real.log (500000000000 / 1030278082133) ∧
    -Real.log (500000000000 / 1030278082133) ≤ (72297593 / 100000000) := by
  have h := checkLog_sound (w := (30278082133 / 2030278082133)) (n := 12)
    (lo := (7457187 / 250000000)) (hi := (29828749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030278082133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030278082133 / 1000000000000) = 1/(500000000000 / 1030278082133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (90371991 / 125000000) (72297593 / 100000000) (Real.log (1030278082133 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1030278082133 / 500000000000) = -Real.log (500000000000 / 1030278082133) := by
    rw [show ((1030278082133 / 500000000000) : ℝ) = ((500000000000 / 1030278082133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (724685679 / 1000000000) ≤ -Real.log (31250000000 / 64502569233) ∧
    -Real.log (31250000000 / 64502569233) ≤ (724685681 / 1000000000) := by
  have h := checkLog_sound (w := (2002569233 / 127002569233)) (n := 12)
    (lo := (31538499 / 1000000000)) (hi := (63077 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64502569233 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64502569233 / 62500000000) = 1/(31250000000 / 64502569233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (724685679 / 1000000000) (724685681 / 1000000000) (Real.log (64502569233 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (64502569233 / 31250000000) = -Real.log (31250000000 / 64502569233) := by
    rw [show ((64502569233 / 31250000000) : ℝ) = ((31250000000 / 64502569233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0173
