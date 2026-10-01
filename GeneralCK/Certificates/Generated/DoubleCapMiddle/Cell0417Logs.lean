import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0417
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

theorem reflection_log_1_neg : (196141633 / 1000000000) ≤ -Real.log (10240 / 12459) ∧
    -Real.log (10240 / 12459) ≤ (98070817 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 22699)) (n := 12)
    (lo := (196141633 / 1000000000)) (hi := (98070817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12459 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12459 / 10240) = 1/(10240 / 12459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (196141633 / 1000000000) (98070817 / 500000000) (Real.log (12459 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12459 / 10240) = -Real.log (10240 / 12459) := by
    rw [show ((12459 / 10240) : ℝ) = ((10240 / 12459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244238517 / 1000000000) ≤ -Real.log (8021 / 10240) ∧
    -Real.log (8021 / 10240) ≤ (122119259 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 18261)) (n := 12)
    (lo := (244238517 / 1000000000)) (hi := (122119259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8021) = 1/(8021 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122119259 / 500000000) (-244238517 / 1000000000) (Real.log (8021 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97950407 / 500000000) ≤ -Real.log (1280 / 1557) ∧
    -Real.log (1280 / 1557) ≤ (39180163 / 200000000) := by
  have h := checkLog_sound (w := (277 / 2837)) (n := 12)
    (lo := (97950407 / 500000000)) (hi := (39180163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1280) = 1/(1280 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97950407 / 500000000) (39180163 / 200000000) (Real.log (1557 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1557 / 1280) = -Real.log (1280 / 1557) := by
    rw [show ((1557 / 1280) : ℝ) = ((1280 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30483071 / 125000000) ≤ -Real.log (1003 / 1280) ∧
    -Real.log (1003 / 1280) ≤ (243864569 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2283)) (n := 12)
    (lo := (30483071 / 125000000)) (hi := (243864569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1003) = 1/(1003 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-243864569 / 1000000000) (-30483071 / 125000000) (Real.log (1003 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180024077 / 500000000) ≤ -Real.log (5120 / 7339) ∧
    -Real.log (5120 / 7339) ≤ (72009631 / 200000000) := by
  have h := checkLog_sound (w := (2219 / 12459)) (n := 12)
    (lo := (180024077 / 500000000)) (hi := (72009631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7339 / 5120) = 1/(5120 / 7339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180024077 / 500000000) (72009631 / 200000000) (Real.log (7339 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7339 / 5120) = -Real.log (5120 / 7339) := by
    rw [show ((7339 / 5120) : ℝ) = ((5120 / 7339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (568098933 / 1000000000) ≤ -Real.log (2901 / 5120) ∧
    -Real.log (2901 / 5120) ≤ (284049467 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 8021)) (n := 12)
    (lo := (568098933 / 1000000000)) (hi := (284049467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2901) = 1/(2901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284049467 / 500000000) (-568098933 / 1000000000) (Real.log (2901 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71927859 / 200000000) ≤ -Real.log (640 / 917) ∧
    -Real.log (640 / 917) ≤ (1404841 / 3906250) := by
  have h := checkLog_sound (w := (277 / 1557)) (n := 12)
    (lo := (71927859 / 200000000)) (hi := (1404841 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917 / 640) = 1/(640 / 917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71927859 / 200000000) (1404841 / 3906250) (Real.log (917 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (917 / 640) = -Real.log (640 / 917) := by
    rw [show ((917 / 640) : ℝ) = ((640 / 917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283532671 / 500000000) ≤ -Real.log (363 / 640) ∧
    -Real.log (363 / 640) ≤ (567065343 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 363) = 1/(363 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567065343 / 1000000000) (-283532671 / 500000000) (Real.log (363 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (53797533 / 200000000) ≤ -Real.log (1000000 / 1308639) ∧
    -Real.log (1000000 / 1308639) ≤ (134493833 / 500000000) := by
  have h := checkLog_sound (w := (308639 / 2308639)) (n := 12)
    (lo := (53797533 / 200000000)) (hi := (134493833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308639 / 1000000) = 1/(1000000 / 1308639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (53797533 / 200000000) (134493833 / 500000000) (Real.log (1308639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1308639 / 1000000) = -Real.log (1000000 / 1308639) := by
    rw [show ((1308639 / 1000000) : ℝ) = ((1000000 / 1308639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9227329 / 25000000) ≤ -Real.log (691361 / 1000000) ∧
    -Real.log (691361 / 1000000) ≤ (369093161 / 1000000000) := by
  have h := checkLog_sound (w := (308639 / 1691361)) (n := 12)
    (lo := (9227329 / 25000000)) (hi := (369093161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691361) = 1/(691361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369093161 / 1000000000) (-9227329 / 25000000) (Real.log (691361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (53862781 / 200000000) ≤ -Real.log (500000 / 654533) ∧
    -Real.log (500000 / 654533) ≤ (134656953 / 500000000) := by
  have h := checkLog_sound (w := (154533 / 1154533)) (n := 12)
    (lo := (53862781 / 200000000)) (hi := (134656953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654533 / 500000) = 1/(500000 / 654533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (53862781 / 200000000) (134656953 / 500000000) (Real.log (654533 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (654533 / 500000) = -Real.log (500000 / 654533) := by
    rw [show ((654533 / 500000) : ℝ) = ((500000 / 654533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (369710973 / 1000000000) ≤ -Real.log (345467 / 500000) ∧
    -Real.log (345467 / 500000) ≤ (184855487 / 500000000) := by
  have h := checkLog_sound (w := (154533 / 845467)) (n := 12)
    (lo := (369710973 / 1000000000)) (hi := (184855487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345467) = 1/(345467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184855487 / 500000000) (-369710973 / 1000000000) (Real.log (345467 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202248359 / 1000000000) ≤ -Real.log (125000 / 153019) ∧
    -Real.log (125000 / 153019) ≤ (5056209 / 25000000) := by
  have h := checkLog_sound (w := (28019 / 278019)) (n := 12)
    (lo := (202248359 / 1000000000)) (hi := (5056209 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153019 / 125000) = 1/(125000 / 153019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202248359 / 1000000000) (5056209 / 25000000) (Real.log (153019 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (153019 / 125000) = -Real.log (125000 / 153019) := by
    rw [show ((153019 / 125000) : ℝ) = ((125000 / 153019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126899327 / 500000000) ≤ -Real.log (96981 / 125000) ∧
    -Real.log (96981 / 125000) ≤ (50759731 / 200000000) := by
  have h := checkLog_sound (w := (28019 / 221981)) (n := 12)
    (lo := (126899327 / 500000000)) (hi := (50759731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96981) = 1/(96981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-50759731 / 200000000) (-126899327 / 500000000) (Real.log (96981 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202515447 / 1000000000) ≤ -Real.log (1000000 / 1224479) ∧
    -Real.log (1000000 / 1224479) ≤ (25314431 / 125000000) := by
  have h := checkLog_sound (w := (224479 / 2224479)) (n := 12)
    (lo := (202515447 / 1000000000)) (hi := (25314431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224479 / 1000000) = 1/(1000000 / 1224479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202515447 / 1000000000) (25314431 / 125000000) (Real.log (1224479 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1224479 / 1000000) = -Real.log (1000000 / 1224479) := by
    rw [show ((1224479 / 1000000) : ℝ) = ((1000000 / 1224479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (254220217 / 1000000000) ≤ -Real.log (775521 / 1000000) ∧
    -Real.log (775521 / 1000000) ≤ (127110109 / 500000000) := by
  have h := checkLog_sound (w := (224479 / 1775521)) (n := 12)
    (lo := (254220217 / 1000000000)) (hi := (127110109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775521) = 1/(775521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-127110109 / 500000000) (-254220217 / 1000000000) (Real.log (775521 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (319040413 / 500000000) ≤ -Real.log (250000000000 / 473211173323) ∧
    -Real.log (250000000000 / 473211173323) ≤ (638080827 / 1000000000) := by
  have h := checkLog_sound (w := (223211173323 / 723211173323)) (n := 12)
    (lo := (319040413 / 500000000)) (hi := (638080827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473211173323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473211173323 / 250000000000) = 1/(250000000000 / 473211173323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (319040413 / 500000000) (638080827 / 1000000000) (Real.log (473211173323 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (473211173323 / 250000000000) = -Real.log (250000000000 / 473211173323) := by
    rw [show ((473211173323 / 250000000000) : ℝ) = ((250000000000 / 473211173323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (639024879 / 1000000000) ≤ -Real.log (250000000000 / 473658120747) ∧
    -Real.log (250000000000 / 473658120747) ≤ (7987811 / 12500000) := by
  have h := checkLog_sound (w := (223658120747 / 723658120747)) (n := 12)
    (lo := (639024879 / 1000000000)) (hi := (7987811 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473658120747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473658120747 / 250000000000) = 1/(250000000000 / 473658120747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (639024879 / 1000000000) (7987811 / 12500000) (Real.log (473658120747 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (473658120747 / 250000000000) = -Real.log (250000000000 / 473658120747) := by
    rw [show ((473658120747 / 250000000000) : ℝ) = ((250000000000 / 473658120747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (456047013 / 1000000000) ≤ -Real.log (125000000000 / 197228065291) ∧
    -Real.log (125000000000 / 197228065291) ≤ (228023507 / 500000000) := by
  have h := checkLog_sound (w := (72228065291 / 322228065291)) (n := 12)
    (lo := (456047013 / 1000000000)) (hi := (228023507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197228065291 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197228065291 / 125000000000) = 1/(125000000000 / 197228065291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (456047013 / 1000000000) (228023507 / 500000000) (Real.log (197228065291 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (197228065291 / 125000000000) = -Real.log (125000000000 / 197228065291) := by
    rw [show ((197228065291 / 125000000000) : ℝ) = ((125000000000 / 197228065291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (28545979 / 62500000) ≤ -Real.log (50000000000 / 78945573363) ∧
    -Real.log (50000000000 / 78945573363) ≤ (91347133 / 200000000) := by
  have h := checkLog_sound (w := (28945573363 / 128945573363)) (n := 12)
    (lo := (28545979 / 62500000)) (hi := (91347133 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78945573363 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78945573363 / 50000000000) = 1/(50000000000 / 78945573363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (28545979 / 62500000) (91347133 / 200000000) (Real.log (78945573363 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (78945573363 / 50000000000) = -Real.log (50000000000 / 78945573363) := by
    rw [show ((78945573363 / 50000000000) : ℝ) = ((50000000000 / 78945573363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0417
