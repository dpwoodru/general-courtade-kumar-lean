import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0172
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

theorem reflection_log_1_neg : (55632853 / 200000000) ≤ -Real.log (2560 / 3381) ∧
    -Real.log (2560 / 3381) ≤ (139082133 / 500000000) := by
  have h := checkLog_sound (w := (821 / 5941)) (n := 12)
    (lo := (55632853 / 200000000)) (hi := (139082133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3381 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3381 / 2560) = 1/(2560 / 3381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55632853 / 200000000) (139082133 / 500000000) (Real.log (3381 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3381 / 2560) = -Real.log (2560 / 3381) := by
    rw [show ((3381 / 2560) : ℝ) = ((2560 / 3381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (386697023 / 1000000000) ≤ -Real.log (1739 / 2560) ∧
    -Real.log (1739 / 2560) ≤ (6042141 / 15625000) := by
  have h := checkLog_sound (w := (821 / 4299)) (n := 12)
    (lo := (386697023 / 1000000000)) (hi := (6042141 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1739) = 1/(1739 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6042141 / 15625000) (-386697023 / 1000000000) (Real.log (1739 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277720511 / 1000000000) ≤ -Real.log (5120 / 6759) ∧
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


theorem reflection_log_3 : Bounds (277720511 / 1000000000) (4339383 / 15625000) (Real.log (6759 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6759 / 5120) = -Real.log (5120 / 6759) := by
    rw [show ((6759 / 5120) : ℝ) = ((5120 / 6759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38583483 / 100000000) ≤ -Real.log (3481 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-385834831 / 1000000000) (-38583483 / 100000000) (Real.log (3481 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (495553343 / 1000000000) ≤ -Real.log (1280 / 2101) ∧
    -Real.log (1280 / 2101) ≤ (7743021 / 15625000) := by
  have h := checkLog_sound (w := (821 / 3381)) (n := 12)
    (lo := (495553343 / 1000000000)) (hi := (7743021 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2101 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2101 / 1280) = 1/(1280 / 2101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (495553343 / 1000000000) (7743021 / 15625000) (Real.log (2101 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2101 / 1280) = -Real.log (1280 / 2101) := by
    rw [show ((2101 / 1280) : ℝ) = ((1280 / 2101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (512782573 / 500000000) ≤ -Real.log (459 / 1280) ∧
    -Real.log (459 / 1280) ≤ (256391287 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 459) = 1/(459 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-256391287 / 250000000) (-512782573 / 500000000) (Real.log (459 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (494839143 / 1000000000) ≤ -Real.log (2560 / 4199) ∧
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


theorem reflection_log_7 : Bounds (494839143 / 1000000000) (61854893 / 125000000) (Real.log (4199 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4199 / 2560) = -Real.log (2560 / 4199) := by
    rw [show ((4199 / 2560) : ℝ) = ((2560 / 4199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (408921 / 400000) ≤ -Real.log (921 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-511151251 / 500000000) (-408921 / 400000) (Real.log (921 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (189957397 / 500000000) ≤ -Real.log (12500 / 18277) ∧
    -Real.log (12500 / 18277) ≤ (75982959 / 200000000) := by
  have h := checkLog_sound (w := (5777 / 30777)) (n := 12)
    (lo := (189957397 / 500000000)) (hi := (75982959 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18277 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18277 / 12500) = 1/(12500 / 18277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (189957397 / 500000000) (75982959 / 200000000) (Real.log (18277 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18277 / 12500) = -Real.log (12500 / 18277) := by
    rw [show ((18277 / 12500) : ℝ) = ((12500 / 18277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (7752427 / 12500000) ≤ -Real.log (6723 / 12500) ∧
    -Real.log (6723 / 12500) ≤ (620194161 / 1000000000) := by
  have h := checkLog_sound (w := (5777 / 19223)) (n := 12)
    (lo := (7752427 / 12500000)) (hi := (620194161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 6723) = 1/(6723 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-620194161 / 1000000000) (-7752427 / 12500000) (Real.log (6723 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (380523297 / 1000000000) ≤ -Real.log (20000 / 29261) ∧
    -Real.log (20000 / 29261) ≤ (190261649 / 500000000) := by
  have h := checkLog_sound (w := (9261 / 49261)) (n := 12)
    (lo := (380523297 / 1000000000)) (hi := (190261649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29261 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29261 / 20000) = 1/(20000 / 29261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (380523297 / 1000000000) (190261649 / 500000000) (Real.log (29261 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (29261 / 20000) = -Real.log (20000 / 29261) := by
    rw [show ((29261 / 20000) : ℝ) = ((20000 / 29261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (310925149 / 500000000) ≤ -Real.log (10739 / 20000) ∧
    -Real.log (10739 / 20000) ≤ (621850299 / 1000000000) := by
  have h := checkLog_sound (w := (9261 / 30739)) (n := 12)
    (lo := (310925149 / 500000000)) (hi := (621850299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 10739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 10739) = 1/(10739 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-621850299 / 1000000000) (-310925149 / 500000000) (Real.log (10739 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (298084033 / 1000000000) ≤ -Real.log (40000 / 53891) ∧
    -Real.log (40000 / 53891) ≤ (149042017 / 500000000) := by
  have h := checkLog_sound (w := (13891 / 93891)) (n := 12)
    (lo := (298084033 / 1000000000)) (hi := (149042017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53891 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53891 / 40000) = 1/(40000 / 53891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (298084033 / 1000000000) (149042017 / 500000000) (Real.log (53891 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53891 / 40000) = -Real.log (40000 / 53891) := by
    rw [show ((53891 / 40000) : ℝ) = ((40000 / 53891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (426599371 / 1000000000) ≤ -Real.log (26109 / 40000) ∧
    -Real.log (26109 / 40000) ≤ (106649843 / 250000000) := by
  have h := checkLog_sound (w := (13891 / 66109)) (n := 12)
    (lo := (426599371 / 1000000000)) (hi := (106649843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26109) = 1/(26109 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106649843 / 250000000) (-426599371 / 1000000000) (Real.log (26109 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (298642041 / 1000000000) ≤ -Real.log (1000000 / 1348027) ∧
    -Real.log (1000000 / 1348027) ≤ (149321021 / 500000000) := by
  have h := checkLog_sound (w := (348027 / 2348027)) (n := 12)
    (lo := (298642041 / 1000000000)) (hi := (149321021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348027 / 1000000) = 1/(1000000 / 1348027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (298642041 / 1000000000) (149321021 / 500000000) (Real.log (1348027 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1348027 / 1000000) = -Real.log (1000000 / 1348027) := by
    rw [show ((1348027 / 1000000) : ℝ) = ((1000000 / 1348027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6683627 / 15625000) ≤ -Real.log (651973 / 1000000) ∧
    -Real.log (651973 / 1000000) ≤ (427752129 / 1000000000) := by
  have h := checkLog_sound (w := (348027 / 1651973)) (n := 12)
    (lo := (6683627 / 15625000)) (hi := (427752129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651973) = 1/(651973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-427752129 / 1000000000) (-6683627 / 15625000) (Real.log (651973 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (500054477 / 500000000) ≤ -Real.log (500000000000 / 1359289007883) ∧
    -Real.log (500000000000 / 1359289007883) ≤ (250027239 / 250000000) := by
  have h := checkLog_sound (w := (359289007883 / 2359289007883)) (n := 12)
    (lo := (153480887 / 500000000)) (hi := (12278471 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359289007883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1359289007883 / 1000000000000) = 1/(500000000000 / 1359289007883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (500054477 / 500000000) (250027239 / 250000000) (Real.log (1359289007883 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1359289007883 / 500000000000) = -Real.log (500000000000 / 1359289007883) := by
    rw [show ((1359289007883 / 500000000000) : ℝ) = ((500000000000 / 1359289007883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200474719 / 200000000) ≤ -Real.log (250000000000 / 681185399013) ∧
    -Real.log (250000000000 / 681185399013) ≤ (1002373597 / 1000000000) := by
  have h := checkLog_sound (w := (181185399013 / 1181185399013)) (n := 12)
    (lo := (61845283 / 200000000)) (hi := (19326651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681185399013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(681185399013 / 500000000000) = 1/(250000000000 / 681185399013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200474719 / 200000000) (1002373597 / 1000000000) (Real.log (681185399013 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (681185399013 / 250000000000) = -Real.log (250000000000 / 681185399013) := by
    rw [show ((681185399013 / 250000000000) : ℝ) = ((250000000000 / 681185399013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (144936681 / 200000000) ≤ -Real.log (25000000000 / 51601938029) ∧
    -Real.log (25000000000 / 51601938029) ≤ (724683407 / 1000000000) := by
  have h := checkLog_sound (w := (1601938029 / 101601938029)) (n := 12)
    (lo := (1261449 / 40000000)) (hi := (15768113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51601938029 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51601938029 / 50000000000) = 1/(25000000000 / 51601938029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (144936681 / 200000000) (724683407 / 1000000000) (Real.log (51601938029 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51601938029 / 25000000000) = -Real.log (25000000000 / 51601938029) := by
    rw [show ((51601938029 / 25000000000) : ℝ) = ((25000000000 / 51601938029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (72639417 / 100000000) ≤ -Real.log (500000000000 / 1033805847789) ∧
    -Real.log (500000000000 / 1033805847789) ≤ (181598543 / 250000000) := by
  have h := checkLog_sound (w := (33805847789 / 2033805847789)) (n := 12)
    (lo := (3324699 / 100000000)) (hi := (33246991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033805847789 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033805847789 / 1000000000000) = 1/(500000000000 / 1033805847789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (72639417 / 100000000) (181598543 / 250000000) (Real.log (1033805847789 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1033805847789 / 500000000000) = -Real.log (500000000000 / 1033805847789) := by
    rw [show ((1033805847789 / 500000000000) : ℝ) = ((500000000000 / 1033805847789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0172
