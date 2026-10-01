import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0118
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

theorem reflection_log_1_neg : (318169599 / 1000000000) ≤ -Real.log (2560 / 3519) ∧
    -Real.log (2560 / 3519) ≤ (24857 / 78125) := by
  have h := checkLog_sound (w := (959 / 6079)) (n := 12)
    (lo := (318169599 / 1000000000)) (hi := (24857 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3519 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3519 / 2560) = 1/(2560 / 3519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (318169599 / 1000000000) (24857 / 78125) (Real.log (3519 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3519 / 2560) = -Real.log (2560 / 3519) := by
    rw [show ((3519 / 2560) : ℝ) = ((2560 / 3519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58672353 / 125000000) ≤ -Real.log (1601 / 2560) ∧
    -Real.log (1601 / 2560) ≤ (18775153 / 40000000) := by
  have h := checkLog_sound (w := (959 / 4161)) (n := 12)
    (lo := (58672353 / 125000000)) (hi := (18775153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1601) = 1/(1601 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18775153 / 40000000) (-58672353 / 125000000) (Real.log (1601 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (317316721 / 1000000000) ≤ -Real.log (640 / 879) ∧
    -Real.log (640 / 879) ≤ (158658361 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1519)) (n := 12)
    (lo := (317316721 / 1000000000)) (hi := (158658361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 640) = 1/(640 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (317316721 / 1000000000) (158658361 / 500000000) (Real.log (879 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (879 / 640) = -Real.log (640 / 879) := by
    rw [show ((879 / 640) : ℝ) = ((640 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (467506749 / 1000000000) ≤ -Real.log (401 / 640) ∧
    -Real.log (401 / 640) ≤ (1870027 / 4000000) := by
  have h := checkLog_sound (w := (239 / 1041)) (n := 12)
    (lo := (467506749 / 1000000000)) (hi := (1870027 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 401) = 1/(401 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1870027 / 4000000) (-467506749 / 1000000000) (Real.log (401 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (559169259 / 1000000000) ≤ -Real.log (1280 / 2239) ∧
    -Real.log (1280 / 2239) ≤ (27958463 / 50000000) := by
  have h := checkLog_sound (w := (959 / 3519)) (n := 12)
    (lo := (559169259 / 1000000000)) (hi := (27958463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2239 / 1280) = 1/(1280 / 2239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (559169259 / 1000000000) (27958463 / 50000000) (Real.log (2239 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2239 / 1280) = -Real.log (1280 / 2239) := by
    rw [show ((2239 / 1280) : ℝ) = ((1280 / 2239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1383174233 / 1000000000) ≤ -Real.log (321 / 1280) ∧
    -Real.log (321 / 1280) ≤ (276634847 / 200000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 321) = 1/(321 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-276634847 / 200000000) (-1383174233 / 1000000000) (Real.log (321 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (557828477 / 1000000000) ≤ -Real.log (320 / 559) ∧
    -Real.log (320 / 559) ≤ (278914239 / 500000000) := by
  have h := checkLog_sound (w := (239 / 879)) (n := 12)
    (lo := (557828477 / 1000000000)) (hi := (278914239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559 / 320) = 1/(320 / 559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (557828477 / 1000000000) (278914239 / 500000000) (Real.log (559 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (559 / 320) = -Real.log (320 / 559) := by
    rw [show ((559 / 320) : ℝ) = ((320 / 559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8586699 / 6250000) ≤ -Real.log (81 / 320) ∧
    -Real.log (81 / 320) ≤ (686935921 / 500000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 81) = 1/(81 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-686935921 / 500000000) (-8586699 / 6250000) (Real.log (81 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10869351 / 25000000) ≤ -Real.log (500000 / 772307) ∧
    -Real.log (500000 / 772307) ≤ (434774041 / 1000000000) := by
  have h := checkLog_sound (w := (272307 / 1272307)) (n := 12)
    (lo := (10869351 / 25000000)) (hi := (434774041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772307 / 500000) = 1/(500000 / 772307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10869351 / 25000000) (434774041 / 1000000000) (Real.log (772307 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (772307 / 500000) = -Real.log (500000 / 772307) := by
    rw [show ((772307 / 500000) : ℝ) = ((500000 / 772307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (786609867 / 1000000000) ≤ -Real.log (227693 / 500000) ∧
    -Real.log (227693 / 500000) ≤ (786609869 / 1000000000) := by
  have h := checkLog_sound (w := (22307 / 477693)) (n := 12)
    (lo := (93462687 / 1000000000)) (hi := (2920709 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227693) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 227693) = 1/(227693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-786609869 / 1000000000) (-786609867 / 1000000000) (Real.log (227693 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (217987457 / 500000000) ≤ -Real.log (100000 / 154647) ∧
    -Real.log (100000 / 154647) ≤ (87194983 / 200000000) := by
  have h := checkLog_sound (w := (54647 / 254647)) (n := 12)
    (lo := (217987457 / 500000000)) (hi := (87194983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154647 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154647 / 100000) = 1/(100000 / 154647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (217987457 / 500000000) (87194983 / 200000000) (Real.log (154647 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (154647 / 100000) = -Real.log (100000 / 154647) := by
    rw [show ((154647 / 100000) : ℝ) = ((100000 / 154647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (395346929 / 500000000) ≤ -Real.log (45353 / 100000) ∧
    -Real.log (45353 / 100000) ≤ (39534693 / 50000000) := by
  have h := checkLog_sound (w := (4647 / 95353)) (n := 12)
    (lo := (48773339 / 500000000)) (hi := (97546679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 45353) = 1/(45353 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39534693 / 50000000) (-395346929 / 500000000) (Real.log (45353 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (350203247 / 1000000000) ≤ -Real.log (250000 / 354839) ∧
    -Real.log (250000 / 354839) ≤ (21887703 / 62500000) := by
  have h := checkLog_sound (w := (104839 / 604839)) (n := 12)
    (lo := (350203247 / 1000000000)) (hi := (21887703 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354839 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354839 / 250000) = 1/(250000 / 354839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (350203247 / 1000000000) (21887703 / 62500000) (Real.log (354839 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (354839 / 250000) = -Real.log (250000 / 354839) := by
    rw [show ((354839 / 250000) : ℝ) = ((250000 / 354839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271808723 / 500000000) ≤ -Real.log (145161 / 250000) ∧
    -Real.log (145161 / 250000) ≤ (543617447 / 1000000000) := by
  have h := checkLog_sound (w := (104839 / 395161)) (n := 12)
    (lo := (271808723 / 500000000)) (hi := (543617447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145161) = 1/(145161 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-543617447 / 1000000000) (-271808723 / 500000000) (Real.log (145161 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (35138759 / 100000000) ≤ -Real.log (500000 / 710519) ∧
    -Real.log (500000 / 710519) ≤ (351387591 / 1000000000) := by
  have h := checkLog_sound (w := (210519 / 1210519)) (n := 12)
    (lo := (35138759 / 100000000)) (hi := (351387591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710519 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710519 / 500000) = 1/(500000 / 710519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (35138759 / 100000000) (351387591 / 1000000000) (Real.log (710519 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (710519 / 500000) = -Real.log (500000 / 710519) := by
    rw [show ((710519 / 500000) : ℝ) = ((500000 / 710519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (546518433 / 1000000000) ≤ -Real.log (289481 / 500000) ∧
    -Real.log (289481 / 500000) ≤ (273259217 / 500000000) := by
  have h := checkLog_sound (w := (210519 / 789481)) (n := 12)
    (lo := (546518433 / 1000000000)) (hi := (273259217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 289481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 289481) = 1/(289481 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273259217 / 500000000) (-546518433 / 1000000000) (Real.log (289481 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (305345977 / 250000000) ≤ -Real.log (500000000000 / 1695939269103) ∧
    -Real.log (500000000000 / 1695939269103) ≤ (122138391 / 100000000) := by
  have h := checkLog_sound (w := (695939269103 / 2695939269103)) (n := 12)
    (lo := (66029591 / 125000000)) (hi := (528236729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695939269103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1695939269103 / 1000000000000) = 1/(500000000000 / 1695939269103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305345977 / 250000000) (122138391 / 100000000) (Real.log (1695939269103 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1695939269103 / 500000000000) = -Real.log (500000000000 / 1695939269103) := by
    rw [show ((1695939269103 / 500000000000) : ℝ) = ((500000000000 / 1695939269103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1226668773 / 1000000000) ≤ -Real.log (500000000000 / 1704925804247) ∧
    -Real.log (500000000000 / 1704925804247) ≤ (49066751 / 40000000) := by
  have h := checkLog_sound (w := (704925804247 / 2704925804247)) (n := 12)
    (lo := (533521593 / 1000000000)) (hi := (266760797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704925804247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704925804247 / 1000000000000) = 1/(500000000000 / 1704925804247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1226668773 / 1000000000) (49066751 / 40000000) (Real.log (1704925804247 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1704925804247 / 500000000000) = -Real.log (500000000000 / 1704925804247) := by
    rw [show ((1704925804247 / 500000000000) : ℝ) = ((500000000000 / 1704925804247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (893820693 / 1000000000) ≤ -Real.log (500000000000 / 1222225666673) ∧
    -Real.log (500000000000 / 1222225666673) ≤ (178764139 / 200000000) := by
  have h := checkLog_sound (w := (222225666673 / 2222225666673)) (n := 12)
    (lo := (200673513 / 1000000000)) (hi := (100336757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222225666673 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1222225666673 / 1000000000000) = 1/(500000000000 / 1222225666673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (893820693 / 1000000000) (178764139 / 200000000) (Real.log (1222225666673 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1222225666673 / 500000000000) = -Real.log (500000000000 / 1222225666673) := by
    rw [show ((1222225666673 / 500000000000) : ℝ) = ((500000000000 / 1222225666673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (897906023 / 1000000000) ≤ -Real.log (125000000000 / 306807268871) ∧
    -Real.log (125000000000 / 306807268871) ≤ (35916241 / 40000000) := by
  have h := checkLog_sound (w := (56807268871 / 556807268871)) (n := 12)
    (lo := (204758843 / 1000000000)) (hi := (51189711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306807268871 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(306807268871 / 250000000000) = 1/(125000000000 / 306807268871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (897906023 / 1000000000) (35916241 / 40000000) (Real.log (306807268871 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (306807268871 / 125000000000) = -Real.log (125000000000 / 306807268871) := by
    rw [show ((306807268871 / 125000000000) : ℝ) = ((125000000000 / 306807268871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0118
