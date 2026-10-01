import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0112
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

theorem reflection_log_1_neg : (323271651 / 1000000000) ≤ -Real.log (2560 / 3537) ∧
    -Real.log (2560 / 3537) ≤ (80817913 / 250000000) := by
  have h := checkLog_sound (w := (977 / 6097)) (n := 12)
    (lo := (323271651 / 1000000000)) (hi := (80817913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3537 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3537 / 2560) = 1/(2560 / 3537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (323271651 / 1000000000) (80817913 / 250000000) (Real.log (3537 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3537 / 2560) = -Real.log (2560 / 3537) := by
    rw [show ((3537 / 2560) : ℝ) = ((2560 / 3537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (480685477 / 1000000000) ≤ -Real.log (1583 / 2560) ∧
    -Real.log (1583 / 2560) ≤ (240342739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 4143)) (n := 12)
    (lo := (480685477 / 1000000000)) (hi := (240342739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1583) = 1/(1583 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240342739 / 500000000) (-480685477 / 1000000000) (Real.log (1583 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64484623 / 200000000) ≤ -Real.log (1280 / 1767) ∧
    -Real.log (1280 / 1767) ≤ (80605779 / 250000000) := by
  have h := checkLog_sound (w := (487 / 3047)) (n := 12)
    (lo := (64484623 / 200000000)) (hi := (80605779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1767 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1767 / 1280) = 1/(1280 / 1767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64484623 / 200000000) (80605779 / 250000000) (Real.log (1767 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1767 / 1280) = -Real.log (1280 / 1767) := by
    rw [show ((1767 / 1280) : ℝ) = ((1280 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95758427 / 200000000) ≤ -Real.log (793 / 1280) ∧
    -Real.log (793 / 1280) ≤ (59849017 / 125000000) := by
  have h := checkLog_sound (w := (487 / 2073)) (n := 12)
    (lo := (95758427 / 200000000)) (hi := (59849017 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 793) = 1/(793 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59849017 / 125000000) (-95758427 / 200000000) (Real.log (793 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (567176419 / 1000000000) ≤ -Real.log (1280 / 2257) ∧
    -Real.log (1280 / 2257) ≤ (28358821 / 50000000) := by
  have h := checkLog_sound (w := (977 / 3537)) (n := 12)
    (lo := (567176419 / 1000000000)) (hi := (28358821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2257 / 1280) = 1/(1280 / 2257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (567176419 / 1000000000) (28358821 / 50000000) (Real.log (2257 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2257 / 1280) = -Real.log (1280 / 2257) := by
    rw [show ((2257 / 1280) : ℝ) = ((1280 / 2257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28817651 / 20000000) ≤ -Real.log (303 / 1280) ∧
    -Real.log (303 / 1280) ≤ (1440882553 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 303) = 1/(303 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1440882553 / 1000000000) (-28817651 / 20000000) (Real.log (303 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (565846337 / 1000000000) ≤ -Real.log (640 / 1127) ∧
    -Real.log (640 / 1127) ≤ (282923169 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1767)) (n := 12)
    (lo := (565846337 / 1000000000)) (hi := (282923169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127 / 640) = 1/(640 / 1127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (565846337 / 1000000000) (282923169 / 500000000) (Real.log (1127 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1127 / 640) = -Real.log (640 / 1127) := by
    rw [show ((1127 / 640) : ℝ) = ((640 / 1127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1431030253 / 1000000000) ≤ -Real.log (153 / 640) ∧
    -Real.log (153 / 640) ≤ (89439391 / 62500000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 153) = 1/(153 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89439391 / 62500000) (-1431030253 / 1000000000) (Real.log (153 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (441973813 / 1000000000) ≤ -Real.log (40000 / 62231) ∧
    -Real.log (40000 / 62231) ≤ (220986907 / 500000000) := by
  have h := checkLog_sound (w := (22231 / 102231)) (n := 12)
    (lo := (441973813 / 1000000000)) (hi := (220986907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62231 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62231 / 40000) = 1/(40000 / 62231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (441973813 / 1000000000) (220986907 / 500000000) (Real.log (62231 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (62231 / 40000) = -Real.log (40000 / 62231) := by
    rw [show ((62231 / 40000) : ℝ) = ((40000 / 62231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (811424087 / 1000000000) ≤ -Real.log (17769 / 40000) ∧
    -Real.log (17769 / 40000) ≤ (811424089 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 37769)) (n := 12)
    (lo := (118276907 / 1000000000)) (hi := (29569227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 17769) = 1/(17769 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-811424089 / 1000000000) (-811424087 / 1000000000) (Real.log (17769 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (443174423 / 1000000000) ≤ -Real.log (250000 / 389411) ∧
    -Real.log (250000 / 389411) ≤ (55396803 / 125000000) := by
  have h := checkLog_sound (w := (139411 / 639411)) (n := 12)
    (lo := (443174423 / 1000000000)) (hi := (55396803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389411 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389411 / 250000) = 1/(250000 / 389411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (443174423 / 1000000000) (55396803 / 125000000) (Real.log (389411 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (389411 / 250000) = -Real.log (250000 / 389411) := by
    rw [show ((389411 / 250000) : ℝ) = ((250000 / 389411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81564029 / 100000000) ≤ -Real.log (110589 / 250000) ∧
    -Real.log (110589 / 250000) ≤ (203910073 / 250000000) := by
  have h := checkLog_sound (w := (14411 / 235589)) (n := 12)
    (lo := (12249311 / 100000000)) (hi := (122493111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110589) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 110589) = 1/(110589 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203910073 / 250000000) (-81564029 / 100000000) (Real.log (110589 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14293409 / 40000000) ≤ -Real.log (200000 / 285903) ∧
    -Real.log (200000 / 285903) ≤ (178667613 / 500000000) := by
  have h := checkLog_sound (w := (85903 / 485903)) (n := 12)
    (lo := (14293409 / 40000000)) (hi := (178667613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285903 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285903 / 200000) = 1/(200000 / 285903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14293409 / 40000000) (178667613 / 500000000) (Real.log (285903 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (285903 / 200000) = -Real.log (200000 / 285903) := by
    rw [show ((285903 / 200000) : ℝ) = ((200000 / 285903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (280634201 / 500000000) ≤ -Real.log (114097 / 200000) ∧
    -Real.log (114097 / 200000) ≤ (561268403 / 1000000000) := by
  have h := checkLog_sound (w := (85903 / 314097)) (n := 12)
    (lo := (280634201 / 500000000)) (hi := (561268403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114097) = 1/(114097 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-561268403 / 1000000000) (-280634201 / 500000000) (Real.log (114097 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (179266059 / 500000000) ≤ -Real.log (1000000 / 1431227) ∧
    -Real.log (1000000 / 1431227) ≤ (358532119 / 1000000000) := by
  have h := checkLog_sound (w := (431227 / 2431227)) (n := 12)
    (lo := (179266059 / 500000000)) (hi := (358532119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1431227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1431227 / 1000000) = 1/(1000000 / 1431227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (179266059 / 500000000) (358532119 / 1000000000) (Real.log (1431227 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1431227 / 1000000) = -Real.log (1000000 / 1431227) := by
    rw [show ((1431227 / 1000000) : ℝ) = ((1000000 / 1431227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (564273869 / 1000000000) ≤ -Real.log (568773 / 1000000) ∧
    -Real.log (568773 / 1000000) ≤ (56427387 / 100000000) := by
  have h := checkLog_sound (w := (431227 / 1568773)) (n := 12)
    (lo := (564273869 / 1000000000)) (hi := (56427387 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 568773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 568773) = 1/(568773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-56427387 / 100000000) (-564273869 / 1000000000) (Real.log (568773 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1253397901 / 1000000000) ≤ -Real.log (62500000000 / 218888935787) ∧
    -Real.log (62500000000 / 218888935787) ≤ (1253397903 / 1000000000) := by
  have h := checkLog_sound (w := (93888935787 / 343888935787)) (n := 12)
    (lo := (560250721 / 1000000000)) (hi := (280125361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218888935787 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218888935787 / 125000000000) = 1/(62500000000 / 218888935787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1253397901 / 1000000000) (1253397903 / 1000000000) (Real.log (218888935787 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (218888935787 / 62500000000) = -Real.log (62500000000 / 218888935787) := by
    rw [show ((218888935787 / 62500000000) : ℝ) = ((62500000000 / 218888935787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1258814713 / 1000000000) ≤ -Real.log (125000000000 / 440155666477) ∧
    -Real.log (125000000000 / 440155666477) ≤ (251762943 / 200000000) := by
  have h := checkLog_sound (w := (190155666477 / 690155666477)) (n := 12)
    (lo := (565667533 / 1000000000)) (hi := (282833767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((440155666477 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(440155666477 / 250000000000) = 1/(125000000000 / 440155666477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1258814713 / 1000000000) (251762943 / 200000000) (Real.log (440155666477 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (440155666477 / 125000000000) = -Real.log (125000000000 / 440155666477) := by
    rw [show ((440155666477 / 125000000000) : ℝ) = ((125000000000 / 440155666477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229650907 / 250000000) ≤ -Real.log (125000000000 / 313223616747) ∧
    -Real.log (125000000000 / 313223616747) ≤ (91860363 / 100000000) := by
  have h := checkLog_sound (w := (63223616747 / 563223616747)) (n := 12)
    (lo := (3522757 / 15625000)) (hi := (225456449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313223616747 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(313223616747 / 250000000000) = 1/(125000000000 / 313223616747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229650907 / 250000000) (91860363 / 100000000) (Real.log (313223616747 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (313223616747 / 125000000000) = -Real.log (125000000000 / 313223616747) := by
    rw [show ((313223616747 / 125000000000) : ℝ) = ((125000000000 / 313223616747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (922805987 / 1000000000) ≤ -Real.log (250000000000 / 629085329297) ∧
    -Real.log (250000000000 / 629085329297) ≤ (922805989 / 1000000000) := by
  have h := checkLog_sound (w := (129085329297 / 1129085329297)) (n := 12)
    (lo := (229658807 / 1000000000)) (hi := (28707351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629085329297 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629085329297 / 500000000000) = 1/(250000000000 / 629085329297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (922805987 / 1000000000) (922805989 / 1000000000) (Real.log (629085329297 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (629085329297 / 250000000000) = -Real.log (250000000000 / 629085329297) := by
    rw [show ((629085329297 / 250000000000) : ℝ) = ((250000000000 / 629085329297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0112
