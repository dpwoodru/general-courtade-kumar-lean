import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0272
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

theorem reflection_log_1_neg : (58196107 / 250000000) ≤ -Real.log (2560 / 3231) ∧
    -Real.log (2560 / 3231) ≤ (232784429 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 5791)) (n := 12)
    (lo := (58196107 / 250000000)) (hi := (232784429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3231 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3231 / 2560) = 1/(2560 / 3231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58196107 / 250000000) (232784429 / 1000000000) (Real.log (3231 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3231 / 2560) = -Real.log (2560 / 3231) := by
    rw [show ((3231 / 2560) : ℝ) = ((2560 / 3231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303959669 / 1000000000) ≤ -Real.log (1889 / 2560) ∧
    -Real.log (1889 / 2560) ≤ (30395967 / 100000000) := by
  have h := checkLog_sound (w := (671 / 4449)) (n := 12)
    (lo := (303959669 / 1000000000)) (hi := (30395967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1889) = 1/(1889 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30395967 / 100000000) (-303959669 / 1000000000) (Real.log (1889 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (232320067 / 1000000000) ≤ -Real.log (5120 / 6459) ∧
    -Real.log (5120 / 6459) ≤ (58080017 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 11579)) (n := 12)
    (lo := (232320067 / 1000000000)) (hi := (58080017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6459 / 5120) = 1/(5120 / 6459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (232320067 / 1000000000) (58080017 / 250000000) (Real.log (6459 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6459 / 5120) = -Real.log (5120 / 6459) := by
    rw [show ((6459 / 5120) : ℝ) = ((5120 / 6459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (151582957 / 500000000) ≤ -Real.log (3781 / 5120) ∧
    -Real.log (3781 / 5120) ≤ (60633183 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 8901)) (n := 12)
    (lo := (151582957 / 500000000)) (hi := (60633183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3781) = 1/(3781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60633183 / 200000000) (-151582957 / 500000000) (Real.log (3781 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (421481983 / 1000000000) ≤ -Real.log (1280 / 1951) ∧
    -Real.log (1280 / 1951) ≤ (823207 / 1953125) := by
  have h := checkLog_sound (w := (671 / 3231)) (n := 12)
    (lo := (421481983 / 1000000000)) (hi := (823207 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1280) = 1/(1280 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (421481983 / 1000000000) (823207 / 1953125) (Real.log (1951 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1951 / 1280) = -Real.log (1280 / 1951) := by
    rw [show ((1951 / 1280) : ℝ) = ((1280 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23212409 / 31250000) ≤ -Real.log (609 / 1280) ∧
    -Real.log (609 / 1280) ≤ (74279709 / 100000000) := by
  have h := checkLog_sound (w := (31 / 1249)) (n := 12)
    (lo := (12412477 / 250000000)) (hi := (49649909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 609) = 1/(609 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-74279709 / 100000000) (-23212409 / 31250000) (Real.log (609 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (420712851 / 1000000000) ≤ -Real.log (2560 / 3899) ∧
    -Real.log (2560 / 3899) ≤ (105178213 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 6459)) (n := 12)
    (lo := (420712851 / 1000000000)) (hi := (105178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3899 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3899 / 2560) = 1/(2560 / 3899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (420712851 / 1000000000) (105178213 / 250000000) (Real.log (3899 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3899 / 2560) = -Real.log (2560 / 3899) := by
    rw [show ((3899 / 2560) : ℝ) = ((2560 / 3899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (370168531 / 500000000) ≤ -Real.log (1221 / 2560) ∧
    -Real.log (1221 / 2560) ≤ (92542133 / 125000000) := by
  have h := checkLog_sound (w := (59 / 2501)) (n := 12)
    (lo := (23594941 / 500000000)) (hi := (47189883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1221) = 1/(1221 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-92542133 / 125000000) (-370168531 / 500000000) (Real.log (1221 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79545969 / 250000000) ≤ -Real.log (1000000 / 1374629) ∧
    -Real.log (1000000 / 1374629) ≤ (318183877 / 1000000000) := by
  have h := checkLog_sound (w := (374629 / 2374629)) (n := 12)
    (lo := (79545969 / 250000000)) (hi := (318183877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374629 / 1000000) = 1/(1000000 / 1374629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79545969 / 250000000) (318183877 / 1000000000) (Real.log (1374629 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1374629 / 1000000) = -Real.log (1000000 / 1374629) := by
    rw [show ((1374629 / 1000000) : ℝ) = ((1000000 / 1374629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93882041 / 200000000) ≤ -Real.log (625371 / 1000000) ∧
    -Real.log (625371 / 1000000) ≤ (234705103 / 500000000) := by
  have h := checkLog_sound (w := (374629 / 1625371)) (n := 12)
    (lo := (93882041 / 200000000)) (hi := (234705103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625371) = 1/(625371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-234705103 / 500000000) (-93882041 / 200000000) (Real.log (625371 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318812939 / 1000000000) ≤ -Real.log (500000 / 687747) ∧
    -Real.log (500000 / 687747) ≤ (15940647 / 50000000) := by
  have h := checkLog_sound (w := (187747 / 1187747)) (n := 12)
    (lo := (318812939 / 1000000000)) (hi := (15940647 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687747 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687747 / 500000) = 1/(500000 / 687747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318812939 / 1000000000) (15940647 / 50000000) (Real.log (687747 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (687747 / 500000) = -Real.log (500000 / 687747) := by
    rw [show ((687747 / 500000) : ℝ) = ((500000 / 687747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (470794341 / 1000000000) ≤ -Real.log (312253 / 500000) ∧
    -Real.log (312253 / 500000) ≤ (235397171 / 500000000) := by
  have h := checkLog_sound (w := (187747 / 812253)) (n := 12)
    (lo := (470794341 / 1000000000)) (hi := (235397171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 312253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 312253) = 1/(312253 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-235397171 / 500000000) (-470794341 / 1000000000) (Real.log (312253 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1521359 / 6250000) ≤ -Real.log (1000000 / 1275601) ∧
    -Real.log (1000000 / 1275601) ≤ (243417441 / 1000000000) := by
  have h := checkLog_sound (w := (275601 / 2275601)) (n := 12)
    (lo := (1521359 / 6250000)) (hi := (243417441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275601 / 1000000) = 1/(1000000 / 1275601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1521359 / 6250000) (243417441 / 1000000000) (Real.log (1275601 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1275601 / 1000000) = -Real.log (1000000 / 1275601) := by
    rw [show ((1275601 / 1000000) : ℝ) = ((1000000 / 1275601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (322412933 / 1000000000) ≤ -Real.log (724399 / 1000000) ∧
    -Real.log (724399 / 1000000) ≤ (161206467 / 500000000) := by
  have h := checkLog_sound (w := (275601 / 1724399)) (n := 12)
    (lo := (322412933 / 1000000000)) (hi := (161206467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724399) = 1/(724399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-161206467 / 500000000) (-322412933 / 1000000000) (Real.log (724399 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30494581 / 125000000) ≤ -Real.log (1000000 / 1276289) ∧
    -Real.log (1000000 / 1276289) ≤ (243956649 / 1000000000) := by
  have h := checkLog_sound (w := (276289 / 2276289)) (n := 12)
    (lo := (30494581 / 125000000)) (hi := (243956649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276289 / 1000000) = 1/(1000000 / 1276289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30494581 / 125000000) (243956649 / 1000000000) (Real.log (1276289 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1276289 / 1000000) = -Real.log (1000000 / 1276289) := by
    rw [show ((1276289 / 1000000) : ℝ) = ((1000000 / 1276289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (323363137 / 1000000000) ≤ -Real.log (723711 / 1000000) ∧
    -Real.log (723711 / 1000000) ≤ (161681569 / 500000000) := by
  have h := checkLog_sound (w := (276289 / 1723711)) (n := 12)
    (lo := (323363137 / 1000000000)) (hi := (161681569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723711) = 1/(723711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-161681569 / 500000000) (-323363137 / 1000000000) (Real.log (723711 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (787594081 / 1000000000) ≤ -Real.log (500000000000 / 1099050803443) ∧
    -Real.log (500000000000 / 1099050803443) ≤ (787594083 / 1000000000) := by
  have h := checkLog_sound (w := (99050803443 / 2099050803443)) (n := 12)
    (lo := (94446901 / 1000000000)) (hi := (47223451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099050803443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099050803443 / 1000000000000) = 1/(500000000000 / 1099050803443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (787594081 / 1000000000) (787594083 / 1000000000) (Real.log (1099050803443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1099050803443 / 500000000000) = -Real.log (500000000000 / 1099050803443) := by
    rw [show ((1099050803443 / 500000000000) : ℝ) = ((500000000000 / 1099050803443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9870091 / 12500000) ≤ -Real.log (500000000000 / 1101265640363) ∧
    -Real.log (500000000000 / 1101265640363) ≤ (394803641 / 500000000) := by
  have h := checkLog_sound (w := (101265640363 / 2101265640363)) (n := 12)
    (lo := (964601 / 10000000)) (hi := (96460101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101265640363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101265640363 / 1000000000000) = 1/(500000000000 / 1101265640363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9870091 / 12500000) (394803641 / 500000000) (Real.log (1101265640363 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1101265640363 / 500000000000) = -Real.log (500000000000 / 1101265640363) := by
    rw [show ((1101265640363 / 500000000000) : ℝ) = ((500000000000 / 1101265640363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (565830373 / 1000000000) ≤ -Real.log (500000000000 / 880454694167) ∧
    -Real.log (500000000000 / 880454694167) ≤ (282915187 / 500000000) := by
  have h := checkLog_sound (w := (380454694167 / 1380454694167)) (n := 12)
    (lo := (565830373 / 1000000000)) (hi := (282915187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880454694167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880454694167 / 500000000000) = 1/(500000000000 / 880454694167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (565830373 / 1000000000) (282915187 / 500000000) (Real.log (880454694167 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (880454694167 / 500000000000) = -Real.log (500000000000 / 880454694167) := by
    rw [show ((880454694167 / 500000000000) : ℝ) = ((500000000000 / 880454694167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (113463957 / 200000000) ≤ -Real.log (100000000000 / 176353406263) ∧
    -Real.log (100000000000 / 176353406263) ≤ (283659893 / 500000000) := by
  have h := checkLog_sound (w := (76353406263 / 276353406263)) (n := 12)
    (lo := (113463957 / 200000000)) (hi := (283659893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176353406263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176353406263 / 100000000000) = 1/(100000000000 / 176353406263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (113463957 / 200000000) (283659893 / 500000000) (Real.log (176353406263 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (176353406263 / 100000000000) = -Real.log (100000000000 / 176353406263) := by
    rw [show ((176353406263 / 100000000000) : ℝ) = ((100000000000 / 176353406263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0272
