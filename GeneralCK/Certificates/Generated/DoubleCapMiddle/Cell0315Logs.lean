import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0315
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

theorem reflection_log_1_neg : (220405431 / 1000000000) ≤ -Real.log (2048 / 2553) ∧
    -Real.log (2048 / 2553) ≤ (27550679 / 125000000) := by
  have h := checkLog_sound (w := (505 / 4601)) (n := 12)
    (lo := (220405431 / 1000000000)) (hi := (27550679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2553 / 2048) = 1/(2048 / 2553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (220405431 / 1000000000) (27550679 / 125000000) (Real.log (2553 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2553 / 2048) = -Real.log (2048 / 2553) := by
    rw [show ((2553 / 2048) : ℝ) = ((2048 / 2553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (283135133 / 1000000000) ≤ -Real.log (1543 / 2048) ∧
    -Real.log (1543 / 2048) ≤ (141567567 / 500000000) := by
  have h := checkLog_sound (w := (505 / 3591)) (n := 12)
    (lo := (283135133 / 1000000000)) (hi := (141567567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1543) = 1/(1543 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-141567567 / 500000000) (-283135133 / 1000000000) (Real.log (1543 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44034077 / 200000000) ≤ -Real.log (5120 / 6381) ∧
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


theorem reflection_log_3 : Bounds (44034077 / 200000000) (110085193 / 500000000) (Real.log (6381 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6381 / 5120) = -Real.log (5120 / 6381) := by
    rw [show ((6381 / 5120) : ℝ) = ((5120 / 6381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (70686589 / 250000000) ≤ -Real.log (3859 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-282746357 / 1000000000) (-70686589 / 250000000) (Real.log (3859 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2004487 / 5000000) ≤ -Real.log (1024 / 1529) ∧
    -Real.log (1024 / 1529) ≤ (400897401 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 2553)) (n := 12)
    (lo := (2004487 / 5000000)) (hi := (400897401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1529 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1529 / 1024) = 1/(1024 / 1529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2004487 / 5000000) (400897401 / 1000000000) (Real.log (1529 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1529 / 1024) = -Real.log (1024 / 1529) := by
    rw [show ((1529 / 1024) : ℝ) = ((1024 / 1529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (339783961 / 500000000) ≤ -Real.log (519 / 1024) ∧
    -Real.log (519 / 1024) ≤ (679567923 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 1543)) (n := 12)
    (lo := (339783961 / 500000000)) (hi := (679567923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 519) = 1/(519 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-679567923 / 1000000000) (-339783961 / 500000000) (Real.log (519 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (400504909 / 1000000000) ≤ -Real.log (2560 / 3821) ∧
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


theorem reflection_log_7 : Bounds (400504909 / 1000000000) (40050491 / 100000000) (Real.log (3821 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3821 / 2560) = -Real.log (2560 / 3821) := by
    rw [show ((3821 / 2560) : ℝ) = ((2560 / 3821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16960313 / 25000000) ≤ -Real.log (1299 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-678412521 / 1000000000) (-16960313 / 25000000) (Real.log (1299 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (301758779 / 1000000000) ≤ -Real.log (200000 / 270447) ∧
    -Real.log (200000 / 270447) ≤ (15087939 / 50000000) := by
  have h := checkLog_sound (w := (70447 / 470447)) (n := 12)
    (lo := (301758779 / 1000000000)) (hi := (15087939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270447 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270447 / 200000) = 1/(200000 / 270447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (301758779 / 1000000000) (15087939 / 50000000) (Real.log (270447 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (270447 / 200000) = -Real.log (200000 / 270447) := by
    rw [show ((270447 / 200000) : ℝ) = ((200000 / 270447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (217113651 / 500000000) ≤ -Real.log (129553 / 200000) ∧
    -Real.log (129553 / 200000) ≤ (434227303 / 1000000000) := by
  have h := checkLog_sound (w := (70447 / 329553)) (n := 12)
    (lo := (217113651 / 500000000)) (hi := (434227303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129553) = 1/(129553 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-434227303 / 1000000000) (-217113651 / 500000000) (Real.log (129553 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3775959 / 12500000) ≤ -Real.log (200000 / 270533) ∧
    -Real.log (200000 / 270533) ≤ (302076721 / 1000000000) := by
  have h := checkLog_sound (w := (70533 / 470533)) (n := 12)
    (lo := (3775959 / 12500000)) (hi := (302076721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270533 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270533 / 200000) = 1/(200000 / 270533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3775959 / 12500000) (302076721 / 1000000000) (Real.log (270533 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (270533 / 200000) = -Real.log (200000 / 270533) := by
    rw [show ((270533 / 200000) : ℝ) = ((200000 / 270533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27180709 / 62500000) ≤ -Real.log (129467 / 200000) ∧
    -Real.log (129467 / 200000) ≤ (86978269 / 200000000) := by
  have h := checkLog_sound (w := (70533 / 329467)) (n := 12)
    (lo := (27180709 / 62500000)) (hi := (86978269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129467) = 1/(129467 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86978269 / 200000000) (-27180709 / 62500000) (Real.log (129467 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (114730179 / 500000000) ≤ -Real.log (1000000 / 1257921) ∧
    -Real.log (1000000 / 1257921) ≤ (229460359 / 1000000000) := by
  have h := checkLog_sound (w := (257921 / 2257921)) (n := 12)
    (lo := (114730179 / 500000000)) (hi := (229460359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257921 / 1000000) = 1/(1000000 / 1257921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (114730179 / 500000000) (229460359 / 1000000000) (Real.log (1257921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1257921 / 1000000) = -Real.log (1000000 / 1257921) := by
    rw [show ((1257921 / 1000000) : ℝ) = ((1000000 / 1257921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74574893 / 250000000) ≤ -Real.log (742079 / 1000000) ∧
    -Real.log (742079 / 1000000) ≤ (298299573 / 1000000000) := by
  have h := checkLog_sound (w := (257921 / 1742079)) (n := 12)
    (lo := (74574893 / 250000000)) (hi := (298299573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742079) = 1/(742079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-298299573 / 1000000000) (-74574893 / 250000000) (Real.log (742079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229729019 / 1000000000) ≤ -Real.log (1000000 / 1258259) ∧
    -Real.log (1000000 / 1258259) ≤ (11486451 / 50000000) := by
  have h := checkLog_sound (w := (258259 / 2258259)) (n := 12)
    (lo := (229729019 / 1000000000)) (hi := (11486451 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258259 / 1000000) = 1/(1000000 / 1258259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229729019 / 1000000000) (11486451 / 50000000) (Real.log (1258259 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1258259 / 1000000) = -Real.log (1000000 / 1258259) := by
    rw [show ((1258259 / 1000000) : ℝ) = ((1000000 / 1258259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (298755153 / 1000000000) ≤ -Real.log (741741 / 1000000) ∧
    -Real.log (741741 / 1000000) ≤ (149377577 / 500000000) := by
  have h := checkLog_sound (w := (258259 / 1741741)) (n := 12)
    (lo := (298755153 / 1000000000)) (hi := (149377577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741741) = 1/(741741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-149377577 / 500000000) (-298755153 / 1000000000) (Real.log (741741 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (735986081 / 1000000000) ≤ -Real.log (250000000000 / 521884865653) ∧
    -Real.log (250000000000 / 521884865653) ≤ (735986083 / 1000000000) := by
  have h := checkLog_sound (w := (21884865653 / 1021884865653)) (n := 12)
    (lo := (42838901 / 1000000000)) (hi := (21419451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((521884865653 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(521884865653 / 500000000000) = 1/(250000000000 / 521884865653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (735986081 / 1000000000) (735986083 / 1000000000) (Real.log (521884865653 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (521884865653 / 250000000000) = -Real.log (250000000000 / 521884865653) := by
    rw [show ((521884865653 / 250000000000) : ℝ) = ((250000000000 / 521884865653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5757563 / 7812500) ≤ -Real.log (500000000000 / 1044795198777) ∧
    -Real.log (500000000000 / 1044795198777) ≤ (368484033 / 500000000) := by
  have h := checkLog_sound (w := (44795198777 / 2044795198777)) (n := 12)
    (lo := (10955221 / 250000000)) (hi := (8764177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1044795198777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1044795198777 / 1000000000000) = 1/(500000000000 / 1044795198777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5757563 / 7812500) (368484033 / 500000000) (Real.log (1044795198777 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1044795198777 / 500000000000) = -Real.log (500000000000 / 1044795198777) := by
    rw [show ((1044795198777 / 500000000000) : ℝ) = ((500000000000 / 1044795198777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52775993 / 100000000) ≤ -Real.log (125000000000 / 211891355233) ∧
    -Real.log (125000000000 / 211891355233) ≤ (527759931 / 1000000000) := by
  have h := checkLog_sound (w := (86891355233 / 336891355233)) (n := 12)
    (lo := (52775993 / 100000000)) (hi := (527759931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211891355233 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211891355233 / 125000000000) = 1/(125000000000 / 211891355233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52775993 / 100000000) (527759931 / 1000000000) (Real.log (211891355233 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (211891355233 / 125000000000) = -Real.log (125000000000 / 211891355233) := by
    rw [show ((211891355233 / 125000000000) : ℝ) = ((125000000000 / 211891355233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (132121043 / 250000000) ≤ -Real.log (62500000000 / 106022435729) ∧
    -Real.log (62500000000 / 106022435729) ≤ (528484173 / 1000000000) := by
  have h := checkLog_sound (w := (43522435729 / 168522435729)) (n := 12)
    (lo := (132121043 / 250000000)) (hi := (528484173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106022435729 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106022435729 / 62500000000) = 1/(62500000000 / 106022435729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (132121043 / 250000000) (528484173 / 1000000000) (Real.log (106022435729 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (106022435729 / 62500000000) = -Real.log (62500000000 / 106022435729) := by
    rw [show ((106022435729 / 62500000000) : ℝ) = ((62500000000 / 106022435729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0315
