import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0101
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

theorem reflection_log_1_neg : (671219053 / 1000000000) ≤ -Real.log (51200 / 100179) ∧
    -Real.log (51200 / 100179) ≤ (335609527 / 500000000) := by
  have h := checkLog_sound (w := (48979 / 151379)) (n := 12)
    (lo := (671219053 / 1000000000)) (hi := (335609527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100179 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100179 / 51200) = 1/(51200 / 100179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (671219053 / 1000000000) (335609527 / 500000000) (Real.log (100179 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100179 / 51200) = -Real.log (51200 / 100179) := by
    rw [show ((100179 / 51200) : ℝ) = ((51200 / 100179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (98055687 / 31250000) ≤ -Real.log (2221 / 51200) ∧
    -Real.log (2221 / 51200) ≤ (3137781989 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2221) = 1/(2221 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3137781989 / 1000000000) (-98055687 / 31250000) (Real.log (2221 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1073647 / 1600000) ≤ -Real.log (160 / 313) ∧
    -Real.log (160 / 313) ≤ (5242417 / 7812500) := by
  have h := checkLog_sound (w := (153 / 473)) (n := 12)
    (lo := (1073647 / 1600000)) (hi := (5242417 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313 / 160) = 1/(160 / 313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1073647 / 1600000) (5242417 / 7812500) (Real.log (313 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (313 / 160) = -Real.log (160 / 313) := by
    rw [show ((313 / 160) : ℝ) = ((160 / 313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3129263663 / 1000000000) ≤ -Real.log (7 / 160) ∧
    -Real.log (7 / 160) ≤ (782315917 / 250000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 7) = 1/(7 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-782315917 / 250000000) (-3129263663 / 1000000000) (Real.log (7 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (648799283 / 1000000000) ≤ -Real.log (25600 / 48979) ∧
    -Real.log (25600 / 48979) ≤ (162199821 / 250000000) := by
  have h := checkLog_sound (w := (23379 / 74579)) (n := 12)
    (lo := (648799283 / 1000000000)) (hi := (162199821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48979 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48979 / 25600) = 1/(25600 / 48979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (648799283 / 1000000000) (162199821 / 250000000) (Real.log (48979 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48979 / 25600) = -Real.log (25600 / 48979) := by
    rw [show ((48979 / 25600) : ℝ) = ((25600 / 48979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (611158701 / 250000000) ≤ -Real.log (2221 / 25600) ∧
    -Real.log (2221 / 25600) ≤ (305579351 / 125000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2221) = 1/(2221 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-305579351 / 125000000) (-611158701 / 250000000) (Real.log (2221 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (324205643 / 500000000) ≤ -Real.log (80 / 153) ∧
    -Real.log (80 / 153) ≤ (648411287 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 233)) (n := 12)
    (lo := (324205643 / 500000000)) (hi := (648411287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 80) = 1/(80 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (324205643 / 500000000) (648411287 / 1000000000) (Real.log (153 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153 / 80) = -Real.log (80 / 153) := by
    rw [show ((153 / 80) : ℝ) = ((80 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2436116483 / 1000000000) ≤ -Real.log (7 / 80) ∧
    -Real.log (7 / 80) ≤ (2436116487 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 7) = 1/(7 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2436116487 / 1000000000) (-2436116483 / 1000000000) (Real.log (7 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675061109 / 1000000000) ≤ -Real.log (1000000 / 1964153) ∧
    -Real.log (1000000 / 1964153) ≤ (67506111 / 100000000) := by
  have h := checkLog_sound (w := (964153 / 2964153)) (n := 12)
    (lo := (675061109 / 1000000000)) (hi := (67506111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964153 / 1000000) = 1/(1000000 / 1964153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675061109 / 1000000000) (67506111 / 100000000) (Real.log (1964153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1964153 / 1000000) = -Real.log (1000000 / 1964153) := by
    rw [show ((1964153 / 1000000) : ℝ) = ((1000000 / 1964153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (665699079 / 200000000) ≤ -Real.log (35847 / 1000000) ∧
    -Real.log (35847 / 1000000) ≤ (16642477 / 5000000) := by
  have h := checkLog_sound (w := (26653 / 98347)) (n := 12)
    (lo := (22236267 / 40000000)) (hi := (138976669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35847) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35847) = 1/(35847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16642477 / 5000000) (-665699079 / 200000000) (Real.log (35847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (675207217 / 1000000000) ≤ -Real.log (25000 / 49111) ∧
    -Real.log (25000 / 49111) ≤ (337603609 / 500000000) := by
  have h := checkLog_sound (w := (24111 / 74111)) (n := 12)
    (lo := (675207217 / 1000000000)) (hi := (337603609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49111 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49111 / 25000) = 1/(25000 / 49111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (675207217 / 1000000000) (337603609 / 500000000) (Real.log (49111 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49111 / 25000) = -Real.log (25000 / 49111) := by
    rw [show ((49111 / 25000) : ℝ) = ((25000 / 49111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1668266933 / 500000000) ≤ -Real.log (889 / 25000) ∧
    -Real.log (889 / 25000) ≤ (3336533871 / 1000000000) := by
  have h := checkLog_sound (w := (1347 / 4903)) (n := 12)
    (lo := (281972573 / 500000000)) (hi := (563945147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1778) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1778) = 1/(889 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3336533871 / 1000000000) (-1668266933 / 500000000) (Real.log (889 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337440431 / 500000000) ≤ -Real.log (1000000 / 1963799) ∧
    -Real.log (1000000 / 1963799) ≤ (674880863 / 1000000000) := by
  have h := checkLog_sound (w := (963799 / 2963799)) (n := 12)
    (lo := (337440431 / 500000000)) (hi := (674880863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963799 / 1000000) = 1/(1000000 / 1963799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337440431 / 500000000) (674880863 / 1000000000) (Real.log (1963799 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1963799 / 1000000) = -Real.log (1000000 / 1963799) := by
    rw [show ((1963799 / 1000000) : ℝ) = ((1000000 / 1963799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3318668533 / 1000000000) ≤ -Real.log (36201 / 1000000) ∧
    -Real.log (36201 / 1000000) ≤ (1659334269 / 500000000) := by
  have h := checkLog_sound (w := (26299 / 98701)) (n := 12)
    (lo := (546079813 / 1000000000)) (hi := (273039907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36201) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36201) = 1/(36201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1659334269 / 500000000) (-3318668533 / 1000000000) (Real.log (36201 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (168757513 / 250000000) ≤ -Real.log (250000 / 491023) ∧
    -Real.log (250000 / 491023) ≤ (675030053 / 1000000000) := by
  have h := checkLog_sound (w := (241023 / 741023)) (n := 12)
    (lo := (168757513 / 250000000)) (hi := (675030053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491023 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491023 / 250000) = 1/(250000 / 491023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (168757513 / 250000000) (675030053 / 1000000000) (Real.log (491023 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (491023 / 250000) = -Real.log (250000 / 491023) := by
    rw [show ((491023 / 250000) : ℝ) = ((250000 / 491023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (831698791 / 250000000) ≤ -Real.log (8977 / 250000) ∧
    -Real.log (8977 / 250000) ≤ (3326795169 / 1000000000) := by
  have h := checkLog_sound (w := (3324 / 12301)) (n := 12)
    (lo := (138551611 / 250000000)) (hi := (110841289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8977) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8977) = 1/(8977 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3326795169 / 1000000000) (-831698791 / 250000000) (Real.log (8977 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4003556503 / 1000000000) ≤ -Real.log (125000000000 / 6849084302731) ∧
    -Real.log (125000000000 / 6849084302731) ≤ (4003556509 / 1000000000) := by
  have h := checkLog_sound (w := (2849084302731 / 10849084302731)) (n := 12)
    (lo := (537820603 / 1000000000)) (hi := (134455151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6849084302731 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6849084302731 / 4000000000000) = 1/(125000000000 / 6849084302731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4003556503 / 1000000000) (4003556509 / 1000000000) (Real.log (6849084302731 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6849084302731 / 125000000000) = -Real.log (125000000000 / 6849084302731) := by
    rw [show ((6849084302731 / 125000000000) : ℝ) = ((125000000000 / 6849084302731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2005870541 / 500000000) ≤ -Real.log (500000000000 / 27621484814399) ∧
    -Real.log (500000000000 / 27621484814399) ≤ (125366909 / 31250000) := by
  have h := checkLog_sound (w := (11621484814399 / 43621484814399)) (n := 12)
    (lo := (273002591 / 500000000)) (hi := (546005183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27621484814399 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27621484814399 / 16000000000000) = 1/(500000000000 / 27621484814399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2005870541 / 500000000) (125366909 / 31250000) (Real.log (27621484814399 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27621484814399 / 500000000000) = -Real.log (500000000000 / 27621484814399) := by
    rw [show ((27621484814399 / 500000000000) : ℝ) = ((500000000000 / 27621484814399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (798709879 / 200000000) ≤ -Real.log (4000000000 / 216988370487) ∧
    -Real.log (4000000000 / 216988370487) ≤ (3993549401 / 1000000000) := by
  have h := checkLog_sound (w := (88988370487 / 344988370487)) (n := 12)
    (lo := (105562699 / 200000000)) (hi := (65976687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216988370487 / 128000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(216988370487 / 128000000000) = 1/(4000000000 / 216988370487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (798709879 / 200000000) (3993549401 / 1000000000) (Real.log (216988370487 / 4000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216988370487 / 4000000000) = -Real.log (4000000000 / 216988370487) := by
    rw [show ((216988370487 / 4000000000) : ℝ) = ((4000000000 / 216988370487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (62528519 / 15625000) ≤ -Real.log (15625000000 / 854654603431) ∧
    -Real.log (15625000000 / 854654603431) ≤ (2000912611 / 500000000) := by
  have h := checkLog_sound (w := (354654603431 / 1354654603431)) (n := 12)
    (lo := (134022329 / 250000000)) (hi := (536089317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854654603431 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(854654603431 / 500000000000) = 1/(15625000000 / 854654603431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (62528519 / 15625000) (2000912611 / 500000000) (Real.log (854654603431 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (854654603431 / 15625000000) = -Real.log (15625000000 / 854654603431) := by
    rw [show ((854654603431 / 15625000000) : ℝ) = ((15625000000 / 854654603431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0101
