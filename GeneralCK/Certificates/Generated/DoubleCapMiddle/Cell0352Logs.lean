import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0352
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

theorem reflection_log_1_neg : (211671751 / 1000000000) ≤ -Real.log (5120 / 6327) ∧
    -Real.log (5120 / 6327) ≤ (26458969 / 125000000) := by
  have h := checkLog_sound (w := (1207 / 11447)) (n := 12)
    (lo := (211671751 / 1000000000)) (hi := (26458969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6327 / 5120) = 1/(5120 / 6327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (211671751 / 1000000000) (26458969 / 125000000) (Real.log (6327 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6327 / 5120) = -Real.log (5120 / 6327) := by
    rw [show ((6327 / 5120) : ℝ) = ((5120 / 6327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53770019 / 200000000) ≤ -Real.log (3913 / 5120) ∧
    -Real.log (3913 / 5120) ≤ (16803131 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 9033)) (n := 12)
    (lo := (53770019 / 200000000)) (hi := (16803131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3913) = 1/(3913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16803131 / 62500000) (-53770019 / 200000000) (Real.log (3913 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (211434643 / 1000000000) ≤ -Real.log (10240 / 12651) ∧
    -Real.log (10240 / 12651) ≤ (52858661 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 22891)) (n := 12)
    (lo := (211434643 / 1000000000)) (hi := (52858661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12651 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12651 / 10240) = 1/(10240 / 12651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (211434643 / 1000000000) (52858661 / 250000000) (Real.log (12651 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12651 / 10240) = -Real.log (10240 / 12651) := by
    rw [show ((12651 / 10240) : ℝ) = ((10240 / 12651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (268466831 / 1000000000) ≤ -Real.log (7829 / 10240) ∧
    -Real.log (7829 / 10240) ≤ (16779177 / 62500000) := by
  have h := checkLog_sound (w := (2411 / 18069)) (n := 12)
    (lo := (268466831 / 1000000000)) (hi := (16779177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7829) = 1/(7829 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16779177 / 62500000) (-268466831 / 1000000000) (Real.log (7829 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38627167 / 100000000) ≤ -Real.log (2560 / 3767) ∧
    -Real.log (2560 / 3767) ≤ (386271671 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 6327)) (n := 12)
    (lo := (38627167 / 100000000)) (hi := (386271671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3767 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3767 / 2560) = 1/(2560 / 3767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38627167 / 100000000) (386271671 / 1000000000) (Real.log (3767 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3767 / 2560) = -Real.log (2560 / 3767) := by
    rw [show ((3767 / 2560) : ℝ) = ((2560 / 3767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (637682909 / 1000000000) ≤ -Real.log (1353 / 2560) ∧
    -Real.log (1353 / 2560) ≤ (63768291 / 100000000) := by
  have h := checkLog_sound (w := (1207 / 3913)) (n := 12)
    (lo := (637682909 / 1000000000)) (hi := (63768291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1353) = 1/(1353 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63768291 / 100000000) (-637682909 / 1000000000) (Real.log (1353 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96468349 / 250000000) ≤ -Real.log (5120 / 7531) ∧
    -Real.log (5120 / 7531) ≤ (385873397 / 1000000000) := by
  have h := checkLog_sound (w := (2411 / 12651)) (n := 12)
    (lo := (96468349 / 250000000)) (hi := (385873397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7531 / 5120) = 1/(5120 / 7531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96468349 / 250000000) (385873397 / 1000000000) (Real.log (7531 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7531 / 5120) = -Real.log (5120 / 7531) := by
    rw [show ((7531 / 5120) : ℝ) = ((5120 / 7531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5092599 / 8000000) ≤ -Real.log (2709 / 5120) ∧
    -Real.log (2709 / 5120) ≤ (159143719 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 7829)) (n := 12)
    (lo := (5092599 / 8000000)) (hi := (159143719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2709) = 1/(2709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159143719 / 250000000) (-5092599 / 8000000) (Real.log (2709 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289959227 / 1000000000) ≤ -Real.log (1000000 / 1336373) ∧
    -Real.log (1000000 / 1336373) ≤ (72489807 / 250000000) := by
  have h := checkLog_sound (w := (336373 / 2336373)) (n := 12)
    (lo := (289959227 / 1000000000)) (hi := (72489807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336373 / 1000000) = 1/(1000000 / 1336373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289959227 / 1000000000) (72489807 / 250000000) (Real.log (1336373 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1336373 / 1000000) = -Real.log (1000000 / 1336373) := by
    rw [show ((1336373 / 1000000) : ℝ) = ((1000000 / 1336373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205017517 / 500000000) ≤ -Real.log (663627 / 1000000) ∧
    -Real.log (663627 / 1000000) ≤ (82007007 / 200000000) := by
  have h := checkLog_sound (w := (336373 / 1663627)) (n := 12)
    (lo := (205017517 / 500000000)) (hi := (82007007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663627) = 1/(663627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82007007 / 200000000) (-205017517 / 500000000) (Real.log (663627 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145140097 / 500000000) ≤ -Real.log (500000 / 668401) ∧
    -Real.log (500000 / 668401) ≤ (58056039 / 200000000) := by
  have h := checkLog_sound (w := (168401 / 1168401)) (n := 12)
    (lo := (145140097 / 500000000)) (hi := (58056039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668401 / 500000) = 1/(500000 / 668401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145140097 / 500000000) (58056039 / 200000000) (Real.log (668401 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668401 / 500000) = -Real.log (500000 / 668401) := by
    rw [show ((668401 / 500000) : ℝ) = ((500000 / 668401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41068169 / 100000000) ≤ -Real.log (331599 / 500000) ∧
    -Real.log (331599 / 500000) ≤ (410681691 / 1000000000) := by
  have h := checkLog_sound (w := (168401 / 831599)) (n := 12)
    (lo := (41068169 / 100000000)) (hi := (410681691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331599) = 1/(331599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-410681691 / 1000000000) (-41068169 / 100000000) (Real.log (331599 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21956917 / 100000000) ≤ -Real.log (50000 / 62277) ∧
    -Real.log (50000 / 62277) ≤ (219569171 / 1000000000) := by
  have h := checkLog_sound (w := (12277 / 112277)) (n := 12)
    (lo := (21956917 / 100000000)) (hi := (219569171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62277 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62277 / 50000) = 1/(50000 / 62277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21956917 / 100000000) (219569171 / 1000000000) (Real.log (62277 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (62277 / 50000) = -Real.log (50000 / 62277) := by
    rw [show ((62277 / 50000) : ℝ) = ((50000 / 62277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (281753017 / 1000000000) ≤ -Real.log (37723 / 50000) ∧
    -Real.log (37723 / 50000) ≤ (140876509 / 500000000) := by
  have h := checkLog_sound (w := (12277 / 87723)) (n := 12)
    (lo := (281753017 / 1000000000)) (hi := (140876509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37723) = 1/(37723 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-140876509 / 500000000) (-281753017 / 1000000000) (Real.log (37723 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219837291 / 1000000000) ≤ -Real.log (500000 / 622937) ∧
    -Real.log (500000 / 622937) ≤ (54959323 / 250000000) := by
  have h := checkLog_sound (w := (122937 / 1122937)) (n := 12)
    (lo := (219837291 / 1000000000)) (hi := (54959323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622937 / 500000) = 1/(500000 / 622937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219837291 / 1000000000) (54959323 / 250000000) (Real.log (622937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (622937 / 500000) = -Real.log (500000 / 622937) := by
    rw [show ((622937 / 500000) : ℝ) = ((500000 / 622937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (35274477 / 125000000) ≤ -Real.log (377063 / 500000) ∧
    -Real.log (377063 / 500000) ≤ (282195817 / 1000000000) := by
  have h := checkLog_sound (w := (122937 / 877063)) (n := 12)
    (lo := (35274477 / 125000000)) (hi := (282195817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 377063) = 1/(377063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-282195817 / 1000000000) (-35274477 / 125000000) (Real.log (377063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (699994261 / 1000000000) ≤ -Real.log (500000000000 / 1006870576393) ∧
    -Real.log (500000000000 / 1006870576393) ≤ (699994263 / 1000000000) := by
  have h := checkLog_sound (w := (6870576393 / 2006870576393)) (n := 12)
    (lo := (6847081 / 1000000000)) (hi := (3423541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006870576393 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006870576393 / 1000000000000) = 1/(500000000000 / 1006870576393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (699994261 / 1000000000) (699994263 / 1000000000) (Real.log (1006870576393 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1006870576393 / 500000000000) = -Real.log (500000000000 / 1006870576393) := by
    rw [show ((1006870576393 / 500000000000) : ℝ) = ((500000000000 / 1006870576393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175240471 / 250000000) ≤ -Real.log (125000000000 / 251961329799) ∧
    -Real.log (125000000000 / 251961329799) ≤ (350480943 / 500000000) := by
  have h := checkLog_sound (w := (1961329799 / 501961329799)) (n := 12)
    (lo := (488419 / 62500000)) (hi := (1562941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251961329799 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(251961329799 / 250000000000) = 1/(125000000000 / 251961329799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175240471 / 250000000) (350480943 / 500000000) (Real.log (251961329799 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (251961329799 / 125000000000) = -Real.log (125000000000 / 251961329799) := by
    rw [show ((251961329799 / 125000000000) : ℝ) = ((125000000000 / 251961329799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (125330547 / 250000000) ≤ -Real.log (500000000000 / 825451316173) ∧
    -Real.log (500000000000 / 825451316173) ≤ (501322189 / 1000000000) := by
  have h := checkLog_sound (w := (325451316173 / 1325451316173)) (n := 12)
    (lo := (125330547 / 250000000)) (hi := (501322189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825451316173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825451316173 / 500000000000) = 1/(500000000000 / 825451316173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (125330547 / 250000000) (501322189 / 1000000000) (Real.log (825451316173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (825451316173 / 500000000000) = -Real.log (500000000000 / 825451316173) := by
    rw [show ((825451316173 / 500000000000) : ℝ) = ((500000000000 / 825451316173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (502033107 / 1000000000) ≤ -Real.log (250000000000 / 413019177167) ∧
    -Real.log (250000000000 / 413019177167) ≤ (125508277 / 250000000) := by
  have h := checkLog_sound (w := (163019177167 / 663019177167)) (n := 12)
    (lo := (502033107 / 1000000000)) (hi := (125508277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413019177167 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413019177167 / 250000000000) = 1/(250000000000 / 413019177167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (502033107 / 1000000000) (125508277 / 250000000) (Real.log (413019177167 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (413019177167 / 250000000000) = -Real.log (250000000000 / 413019177167) := by
    rw [show ((413019177167 / 250000000000) : ℝ) = ((250000000000 / 413019177167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0352
