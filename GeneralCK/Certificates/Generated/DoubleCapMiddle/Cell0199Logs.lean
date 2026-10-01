import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0199
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

theorem reflection_log_1_neg : (266113237 / 1000000000) ≤ -Real.log (5120 / 6681) ∧
    -Real.log (5120 / 6681) ≤ (133056619 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 11801)) (n := 12)
    (lo := (266113237 / 1000000000)) (hi := (133056619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6681 / 5120) = 1/(5120 / 6681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266113237 / 1000000000) (133056619 / 500000000) (Real.log (6681 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6681 / 5120) = -Real.log (5120 / 6681) := by
    rw [show ((6681 / 5120) : ℝ) = ((5120 / 6681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22729677 / 62500000) ≤ -Real.log (3559 / 5120) ∧
    -Real.log (3559 / 5120) ≤ (363674833 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 8679)) (n := 12)
    (lo := (22729677 / 62500000)) (hi := (363674833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3559) = 1/(3559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-363674833 / 1000000000) (-22729677 / 62500000) (Real.log (3559 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132832051 / 500000000) ≤ -Real.log (2560 / 3339) ∧
    -Real.log (2560 / 3339) ≤ (265664103 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 5899)) (n := 12)
    (lo := (132832051 / 500000000)) (hi := (265664103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3339 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3339 / 2560) = 1/(2560 / 3339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132832051 / 500000000) (265664103 / 1000000000) (Real.log (3339 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3339 / 2560) = -Real.log (2560 / 3339) := by
    rw [show ((3339 / 2560) : ℝ) = ((2560 / 3339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (181416127 / 500000000) ≤ -Real.log (1781 / 2560) ∧
    -Real.log (1781 / 2560) ≤ (72566451 / 200000000) := by
  have h := checkLog_sound (w := (779 / 4341)) (n := 12)
    (lo := (181416127 / 500000000)) (hi := (72566451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1781) = 1/(1781 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72566451 / 200000000) (-181416127 / 500000000) (Real.log (1781 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (476088593 / 1000000000) ≤ -Real.log (2560 / 4121) ∧
    -Real.log (2560 / 4121) ≤ (238044297 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 6681)) (n := 12)
    (lo := (476088593 / 1000000000)) (hi := (238044297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4121 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4121 / 2560) = 1/(2560 / 4121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (476088593 / 1000000000) (238044297 / 500000000) (Real.log (4121 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4121 / 2560) = -Real.log (2560 / 4121) := by
    rw [show ((4121 / 2560) : ℝ) = ((2560 / 4121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (470503879 / 500000000) ≤ -Real.log (999 / 2560) ∧
    -Real.log (999 / 2560) ≤ (11762597 / 12500000) := by
  have h := checkLog_sound (w := (281 / 2279)) (n := 12)
    (lo := (123930289 / 500000000)) (hi := (247860579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 999) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 999) = 1/(999 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11762597 / 12500000) (-470503879 / 500000000) (Real.log (999 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9507207 / 20000000) ≤ -Real.log (1280 / 2059) ∧
    -Real.log (1280 / 2059) ≤ (475360351 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3339)) (n := 12)
    (lo := (9507207 / 20000000)) (hi := (475360351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2059 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2059 / 1280) = 1/(1280 / 2059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9507207 / 20000000) (475360351 / 1000000000) (Real.log (2059 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2059 / 1280) = -Real.log (1280 / 2059) := by
    rw [show ((2059 / 1280) : ℝ) = ((1280 / 2059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (187601851 / 200000000) ≤ -Real.log (501 / 1280) ∧
    -Real.log (501 / 1280) ≤ (938009257 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 1141)) (n := 12)
    (lo := (9794483 / 40000000)) (hi := (61215519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 501) = 1/(501 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-938009257 / 1000000000) (-187601851 / 200000000) (Real.log (501 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (363442393 / 1000000000) ≤ -Real.log (15625 / 22473) ∧
    -Real.log (15625 / 22473) ≤ (181721197 / 500000000) := by
  have h := checkLog_sound (w := (3424 / 19049)) (n := 12)
    (lo := (363442393 / 1000000000)) (hi := (181721197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22473 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22473 / 15625) = 1/(15625 / 22473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (363442393 / 1000000000) (181721197 / 500000000) (Real.log (22473 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (22473 / 15625) = -Real.log (15625 / 22473) := by
    rw [show ((22473 / 15625) : ℝ) = ((15625 / 22473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (144184383 / 250000000) ≤ -Real.log (8777 / 15625) ∧
    -Real.log (8777 / 15625) ≤ (576737533 / 1000000000) := by
  have h := checkLog_sound (w := (3424 / 12201)) (n := 12)
    (lo := (144184383 / 250000000)) (hi := (576737533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 8777) = 1/(8777 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-576737533 / 1000000000) (-144184383 / 250000000) (Real.log (8777 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4550693 / 12500000) ≤ -Real.log (500000 / 719577) ∧
    -Real.log (500000 / 719577) ≤ (364055441 / 1000000000) := by
  have h := checkLog_sound (w := (219577 / 1219577)) (n := 12)
    (lo := (4550693 / 12500000)) (hi := (364055441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719577 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719577 / 500000) = 1/(500000 / 719577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4550693 / 12500000) (364055441 / 1000000000) (Real.log (719577 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (719577 / 500000) = -Real.log (500000 / 719577) := by
    rw [show ((719577 / 500000) : ℝ) = ((500000 / 719577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14457723 / 25000000) ≤ -Real.log (280423 / 500000) ∧
    -Real.log (280423 / 500000) ≤ (578308921 / 1000000000) := by
  have h := checkLog_sound (w := (219577 / 780423)) (n := 12)
    (lo := (14457723 / 25000000)) (hi := (578308921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280423) = 1/(280423 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-578308921 / 1000000000) (-14457723 / 25000000) (Real.log (280423 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (283124201 / 1000000000) ≤ -Real.log (100000 / 132727) ∧
    -Real.log (100000 / 132727) ≤ (141562101 / 500000000) := by
  have h := checkLog_sound (w := (32727 / 232727)) (n := 12)
    (lo := (283124201 / 1000000000)) (hi := (141562101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132727 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132727 / 100000) = 1/(100000 / 132727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (283124201 / 1000000000) (141562101 / 500000000) (Real.log (132727 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (132727 / 100000) = -Real.log (100000 / 132727) := by
    rw [show ((132727 / 100000) : ℝ) = ((100000 / 132727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (198205609 / 500000000) ≤ -Real.log (67273 / 100000) ∧
    -Real.log (67273 / 100000) ≤ (396411219 / 1000000000) := by
  have h := checkLog_sound (w := (32727 / 167273)) (n := 12)
    (lo := (198205609 / 500000000)) (hi := (396411219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67273) = 1/(67273 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-396411219 / 1000000000) (-198205609 / 500000000) (Real.log (67273 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (283675557 / 1000000000) ≤ -Real.log (500000 / 664001) ∧
    -Real.log (500000 / 664001) ≤ (141837779 / 500000000) := by
  have h := checkLog_sound (w := (164001 / 1164001)) (n := 12)
    (lo := (283675557 / 1000000000)) (hi := (141837779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664001 / 500000) = 1/(500000 / 664001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (283675557 / 1000000000) (141837779 / 500000000) (Real.log (664001 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (664001 / 500000) = -Real.log (500000 / 664001) := by
    rw [show ((664001 / 500000) : ℝ) = ((500000 / 664001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (198749957 / 500000000) ≤ -Real.log (335999 / 500000) ∧
    -Real.log (335999 / 500000) ≤ (79499983 / 200000000) := by
  have h := checkLog_sound (w := (164001 / 835999)) (n := 12)
    (lo := (198749957 / 500000000)) (hi := (79499983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335999) = 1/(335999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-79499983 / 200000000) (-198749957 / 500000000) (Real.log (335999 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (235044981 / 250000000) ≤ -Real.log (500000000000 / 1280221032243) ∧
    -Real.log (500000000000 / 1280221032243) ≤ (470089963 / 500000000) := by
  have h := checkLog_sound (w := (280221032243 / 2280221032243)) (n := 12)
    (lo := (30879093 / 125000000)) (hi := (49406549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280221032243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280221032243 / 1000000000000) = 1/(500000000000 / 1280221032243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (235044981 / 250000000) (470089963 / 500000000) (Real.log (1280221032243 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1280221032243 / 500000000000) = -Real.log (500000000000 / 1280221032243) := by
    rw [show ((1280221032243 / 500000000000) : ℝ) = ((500000000000 / 1280221032243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (942364361 / 1000000000) ≤ -Real.log (250000000000 / 641510325473) ∧
    -Real.log (250000000000 / 641510325473) ≤ (942364363 / 1000000000) := by
  have h := checkLog_sound (w := (141510325473 / 1141510325473)) (n := 12)
    (lo := (249217181 / 1000000000)) (hi := (124608591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641510325473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(641510325473 / 500000000000) = 1/(250000000000 / 641510325473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (942364361 / 1000000000) (942364363 / 1000000000) (Real.log (641510325473 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (641510325473 / 250000000000) = -Real.log (250000000000 / 641510325473) := by
    rw [show ((641510325473 / 250000000000) : ℝ) = ((250000000000 / 641510325473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (679535419 / 1000000000) ≤ -Real.log (250000000000 / 493240230107) ∧
    -Real.log (250000000000 / 493240230107) ≤ (33976771 / 50000000) := by
  have h := checkLog_sound (w := (243240230107 / 743240230107)) (n := 12)
    (lo := (679535419 / 1000000000)) (hi := (33976771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493240230107 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493240230107 / 250000000000) = 1/(250000000000 / 493240230107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (679535419 / 1000000000) (33976771 / 50000000) (Real.log (493240230107 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (493240230107 / 250000000000) = -Real.log (250000000000 / 493240230107) := by
    rw [show ((493240230107 / 250000000000) : ℝ) = ((250000000000 / 493240230107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (681175471 / 1000000000) ≤ -Real.log (125000000000 / 247024916741) ∧
    -Real.log (125000000000 / 247024916741) ≤ (42573467 / 62500000) := by
  have h := checkLog_sound (w := (122024916741 / 372024916741)) (n := 12)
    (lo := (681175471 / 1000000000)) (hi := (42573467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247024916741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247024916741 / 125000000000) = 1/(125000000000 / 247024916741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (681175471 / 1000000000) (42573467 / 62500000) (Real.log (247024916741 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (247024916741 / 125000000000) = -Real.log (125000000000 / 247024916741) := by
    rw [show ((247024916741 / 125000000000) : ℝ) = ((125000000000 / 247024916741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0199
