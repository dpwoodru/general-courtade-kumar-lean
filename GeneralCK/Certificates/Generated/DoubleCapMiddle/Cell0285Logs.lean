import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0285
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

theorem reflection_log_1_neg : (227431221 / 1000000000) ≤ -Real.log (2048 / 2571) ∧
    -Real.log (2048 / 2571) ≤ (113715611 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4619)) (n := 12)
    (lo := (227431221 / 1000000000)) (hi := (113715611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2048) = 1/(2048 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227431221 / 1000000000) (113715611 / 500000000) (Real.log (2571 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2571 / 2048) = -Real.log (2048 / 2571) := by
    rw [show ((2571 / 2048) : ℝ) = ((2048 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294869297 / 1000000000) ≤ -Real.log (1525 / 2048) ∧
    -Real.log (1525 / 2048) ≤ (147434649 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3573)) (n := 12)
    (lo := (294869297 / 1000000000)) (hi := (147434649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1525) = 1/(1525 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147434649 / 500000000) (-294869297 / 1000000000) (Real.log (1525 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227197821 / 1000000000) ≤ -Real.log (2560 / 3213) ∧
    -Real.log (2560 / 3213) ≤ (113598911 / 500000000) := by
  have h := checkLog_sound (w := (653 / 5773)) (n := 12)
    (lo := (227197821 / 1000000000)) (hi := (113598911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3213 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3213 / 2560) = 1/(2560 / 3213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227197821 / 1000000000) (113598911 / 500000000) (Real.log (3213 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3213 / 2560) = -Real.log (2560 / 3213) := by
    rw [show ((3213 / 2560) : ℝ) = ((2560 / 3213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294475931 / 1000000000) ≤ -Real.log (1907 / 2560) ∧
    -Real.log (1907 / 2560) ≤ (73618983 / 250000000) := by
  have h := checkLog_sound (w := (653 / 4467)) (n := 12)
    (lo := (294475931 / 1000000000)) (hi := (73618983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1907) = 1/(1907 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-73618983 / 250000000) (-294475931 / 1000000000) (Real.log (1907 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103150261 / 250000000) ≤ -Real.log (1024 / 1547) ∧
    -Real.log (1024 / 1547) ≤ (82520209 / 200000000) := by
  have h := checkLog_sound (w := (523 / 2571)) (n := 12)
    (lo := (103150261 / 250000000)) (hi := (82520209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547 / 1024) = 1/(1024 / 1547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103150261 / 250000000) (82520209 / 200000000) (Real.log (1547 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1547 / 1024) = -Real.log (1024 / 1547) := by
    rw [show ((1547 / 1024) : ℝ) = ((1024 / 1547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (714865703 / 1000000000) ≤ -Real.log (501 / 1024) ∧
    -Real.log (501 / 1024) ≤ (142973141 / 200000000) := by
  have h := checkLog_sound (w := (11 / 1013)) (n := 12)
    (lo := (21718523 / 1000000000)) (hi := (5429631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 501) = 1/(501 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-142973141 / 200000000) (-714865703 / 1000000000) (Real.log (501 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206106561 / 500000000) ≤ -Real.log (1280 / 1933) ∧
    -Real.log (1280 / 1933) ≤ (412213123 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 3213)) (n := 12)
    (lo := (206106561 / 500000000)) (hi := (412213123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933 / 1280) = 1/(1280 / 1933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206106561 / 500000000) (412213123 / 1000000000) (Real.log (1933 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1933 / 1280) = -Real.log (1280 / 1933) := by
    rw [show ((1933 / 1280) : ℝ) = ((1280 / 1933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142733763 / 200000000) ≤ -Real.log (627 / 1280) ∧
    -Real.log (627 / 1280) ≤ (713668817 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 1267)) (n := 12)
    (lo := (4104327 / 200000000)) (hi := (5130409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 627) = 1/(627 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-713668817 / 1000000000) (-142733763 / 200000000) (Real.log (627 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155628127 / 500000000) ≤ -Real.log (1000000 / 1365139) ∧
    -Real.log (1000000 / 1365139) ≤ (62251251 / 200000000) := by
  have h := checkLog_sound (w := (365139 / 2365139)) (n := 12)
    (lo := (155628127 / 500000000)) (hi := (62251251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365139 / 1000000) = 1/(1000000 / 1365139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155628127 / 500000000) (62251251 / 200000000) (Real.log (1365139 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1365139 / 1000000) = -Real.log (1000000 / 1365139) := by
    rw [show ((1365139 / 1000000) : ℝ) = ((1000000 / 1365139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (454349201 / 1000000000) ≤ -Real.log (634861 / 1000000) ∧
    -Real.log (634861 / 1000000) ≤ (227174601 / 500000000) := by
  have h := checkLog_sound (w := (365139 / 1634861)) (n := 12)
    (lo := (454349201 / 1000000000)) (hi := (227174601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634861) = 1/(634861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227174601 / 500000000) (-454349201 / 1000000000) (Real.log (634861 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (19473291 / 62500000) ≤ -Real.log (1000000 / 1365571) ∧
    -Real.log (1000000 / 1365571) ≤ (311572657 / 1000000000) := by
  have h := checkLog_sound (w := (365571 / 2365571)) (n := 12)
    (lo := (19473291 / 62500000)) (hi := (311572657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365571 / 1000000) = 1/(1000000 / 1365571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (19473291 / 62500000) (311572657 / 1000000000) (Real.log (1365571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1365571 / 1000000) = -Real.log (1000000 / 1365571) := by
    rw [show ((1365571 / 1000000) : ℝ) = ((1000000 / 1365571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (455029897 / 1000000000) ≤ -Real.log (634429 / 1000000) ∧
    -Real.log (634429 / 1000000) ≤ (227514949 / 500000000) := by
  have h := checkLog_sound (w := (365571 / 1634429)) (n := 12)
    (lo := (455029897 / 1000000000)) (hi := (227514949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634429) = 1/(634429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227514949 / 500000000) (-455029897 / 1000000000) (Real.log (634429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59375789 / 250000000) ≤ -Real.log (1000000 / 1268079) ∧
    -Real.log (1000000 / 1268079) ≤ (237503157 / 1000000000) := by
  have h := checkLog_sound (w := (268079 / 2268079)) (n := 12)
    (lo := (59375789 / 250000000)) (hi := (237503157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268079 / 1000000) = 1/(1000000 / 1268079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59375789 / 250000000) (237503157 / 1000000000) (Real.log (1268079 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1268079 / 1000000) = -Real.log (1000000 / 1268079) := by
    rw [show ((1268079 / 1000000) : ℝ) = ((1000000 / 1268079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (156041347 / 500000000) ≤ -Real.log (731921 / 1000000) ∧
    -Real.log (731921 / 1000000) ≤ (62416539 / 200000000) := by
  have h := checkLog_sound (w := (268079 / 1731921)) (n := 12)
    (lo := (156041347 / 500000000)) (hi := (62416539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731921) = 1/(731921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62416539 / 200000000) (-156041347 / 500000000) (Real.log (731921 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (237772819 / 1000000000) ≤ -Real.log (1000000 / 1268421) ∧
    -Real.log (1000000 / 1268421) ≤ (11888641 / 50000000) := by
  have h := checkLog_sound (w := (268421 / 2268421)) (n := 12)
    (lo := (237772819 / 1000000000)) (hi := (11888641 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268421 / 1000000) = 1/(1000000 / 1268421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237772819 / 1000000000) (11888641 / 50000000) (Real.log (1268421 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1268421 / 1000000) = -Real.log (1000000 / 1268421) := by
    rw [show ((1268421 / 1000000) : ℝ) = ((1000000 / 1268421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (312550067 / 1000000000) ≤ -Real.log (731579 / 1000000) ∧
    -Real.log (731579 / 1000000) ≤ (78137517 / 250000000) := by
  have h := checkLog_sound (w := (268421 / 1731579)) (n := 12)
    (lo := (312550067 / 1000000000)) (hi := (78137517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731579) = 1/(731579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78137517 / 250000000) (-312550067 / 1000000000) (Real.log (731579 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (47850341 / 62500000) ≤ -Real.log (50000000000 / 107514794577) ∧
    -Real.log (50000000000 / 107514794577) ≤ (382802729 / 500000000) := by
  have h := checkLog_sound (w := (7514794577 / 207514794577)) (n := 12)
    (lo := (18114569 / 250000000)) (hi := (72458277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107514794577 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(107514794577 / 100000000000) = 1/(50000000000 / 107514794577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (47850341 / 62500000) (382802729 / 500000000) (Real.log (107514794577 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (107514794577 / 50000000000) = -Real.log (50000000000 / 107514794577) := by
    rw [show ((107514794577 / 50000000000) : ℝ) = ((50000000000 / 107514794577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (95825319 / 125000000) ≤ -Real.log (100000000000 / 215244101389) ∧
    -Real.log (100000000000 / 215244101389) ≤ (383301277 / 500000000) := by
  have h := checkLog_sound (w := (15244101389 / 415244101389)) (n := 12)
    (lo := (18363843 / 250000000)) (hi := (73455373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215244101389 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215244101389 / 200000000000) = 1/(100000000000 / 215244101389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (95825319 / 125000000) (383301277 / 500000000) (Real.log (215244101389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (215244101389 / 100000000000) = -Real.log (100000000000 / 215244101389) := by
    rw [show ((215244101389 / 100000000000) : ℝ) = ((100000000000 / 215244101389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (549585851 / 1000000000) ≤ -Real.log (125000000000 / 216566917741) ∧
    -Real.log (125000000000 / 216566917741) ≤ (137396463 / 250000000) := by
  have h := checkLog_sound (w := (91566917741 / 341566917741)) (n := 12)
    (lo := (549585851 / 1000000000)) (hi := (137396463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216566917741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216566917741 / 125000000000) = 1/(125000000000 / 216566917741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (549585851 / 1000000000) (137396463 / 250000000) (Real.log (216566917741 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216566917741 / 125000000000) = -Real.log (125000000000 / 216566917741) := by
    rw [show ((216566917741 / 125000000000) : ℝ) = ((125000000000 / 216566917741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (275161443 / 500000000) ≤ -Real.log (250000000000 / 433453188241) ∧
    -Real.log (250000000000 / 433453188241) ≤ (550322887 / 1000000000) := by
  have h := checkLog_sound (w := (183453188241 / 683453188241)) (n := 12)
    (lo := (275161443 / 500000000)) (hi := (550322887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433453188241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433453188241 / 250000000000) = 1/(250000000000 / 433453188241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (275161443 / 500000000) (550322887 / 1000000000) (Real.log (433453188241 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (433453188241 / 250000000000) = -Real.log (250000000000 / 433453188241) := by
    rw [show ((433453188241 / 250000000000) : ℝ) = ((250000000000 / 433453188241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0285
