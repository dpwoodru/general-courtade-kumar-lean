import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0113
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

theorem reflection_log_1_neg : (64484623 / 200000000) ≤ -Real.log (1280 / 1767) ∧
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


theorem reflection_log_1 : Bounds (64484623 / 200000000) (80605779 / 250000000) (Real.log (1767 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1767 / 1280) = -Real.log (1280 / 1767) := by
    rw [show ((1767 / 1280) : ℝ) = ((1280 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95758427 / 200000000) ≤ -Real.log (793 / 1280) ∧
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


theorem reflection_log_2 : Bounds (-59849017 / 125000000) (-95758427 / 200000000) (Real.log (793 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (160786929 / 500000000) ≤ -Real.log (2560 / 3531) ∧
    -Real.log (2560 / 3531) ≤ (321573859 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 6091)) (n := 12)
    (lo := (160786929 / 500000000)) (hi := (321573859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3531 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3531 / 2560) = 1/(2560 / 3531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (160786929 / 500000000) (321573859 / 1000000000) (Real.log (3531 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3531 / 2560) = -Real.log (2560 / 3531) := by
    rw [show ((3531 / 2560) : ℝ) = ((2560 / 3531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47690237 / 100000000) ≤ -Real.log (1589 / 2560) ∧
    -Real.log (1589 / 2560) ≤ (476902371 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 4149)) (n := 12)
    (lo := (47690237 / 100000000)) (hi := (476902371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1589) = 1/(1589 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-476902371 / 1000000000) (-47690237 / 100000000) (Real.log (1589 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (565846337 / 1000000000) ≤ -Real.log (640 / 1127) ∧
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


theorem reflection_log_5 : Bounds (565846337 / 1000000000) (282923169 / 500000000) (Real.log (1127 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1127 / 640) = -Real.log (640 / 1127) := by
    rw [show ((1127 / 640) : ℝ) = ((640 / 1127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1431030253 / 1000000000) ≤ -Real.log (153 / 640) ∧
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


theorem reflection_log_6 : Bounds (-89439391 / 62500000) (-1431030253 / 1000000000) (Real.log (153 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (564514483 / 1000000000) ≤ -Real.log (1280 / 2251) ∧
    -Real.log (1280 / 2251) ≤ (141128621 / 250000000) := by
  have h := checkLog_sound (w := (971 / 3531)) (n := 12)
    (lo := (564514483 / 1000000000)) (hi := (141128621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2251 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2251 / 1280) = 1/(1280 / 2251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (564514483 / 1000000000) (141128621 / 250000000) (Real.log (2251 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2251 / 1280) = -Real.log (1280 / 2251) := by
    rw [show ((2251 / 1280) : ℝ) = ((1280 / 2251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (710637039 / 500000000) ≤ -Real.log (309 / 1280) ∧
    -Real.log (309 / 1280) ≤ (1421274081 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 309) = 1/(309 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1421274081 / 1000000000) (-710637039 / 500000000) (Real.log (309 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (440773691 / 1000000000) ≤ -Real.log (1000000 / 1553909) ∧
    -Real.log (1000000 / 1553909) ≤ (110193423 / 250000000) := by
  have h := checkLog_sound (w := (553909 / 2553909)) (n := 12)
    (lo := (440773691 / 1000000000)) (hi := (110193423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1553909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1553909 / 1000000) = 1/(1000000 / 1553909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (440773691 / 1000000000) (110193423 / 250000000) (Real.log (1553909 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1553909 / 1000000) = -Real.log (1000000 / 1553909) := by
    rw [show ((1553909 / 1000000) : ℝ) = ((1000000 / 1553909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (807232311 / 1000000000) ≤ -Real.log (446091 / 1000000) ∧
    -Real.log (446091 / 1000000) ≤ (807232313 / 1000000000) := by
  have h := checkLog_sound (w := (53909 / 946091)) (n := 12)
    (lo := (114085131 / 1000000000)) (hi := (28521283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 446091) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 446091) = 1/(446091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-807232313 / 1000000000) (-807232311 / 1000000000) (Real.log (446091 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55246807 / 125000000) ≤ -Real.log (15625 / 24309) ∧
    -Real.log (15625 / 24309) ≤ (441974457 / 1000000000) := by
  have h := checkLog_sound (w := (4342 / 19967)) (n := 12)
    (lo := (55246807 / 125000000)) (hi := (441974457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 15625) = 1/(15625 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55246807 / 125000000) (441974457 / 1000000000) (Real.log (24309 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24309 / 15625) = -Real.log (15625 / 24309) := by
    rw [show ((24309 / 15625) : ℝ) = ((15625 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (405713169 / 500000000) ≤ -Real.log (6941 / 15625) ∧
    -Real.log (6941 / 15625) ≤ (40571317 / 50000000) := by
  have h := checkLog_sound (w := (1743 / 29507)) (n := 12)
    (lo := (59139579 / 500000000)) (hi := (118279159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13882) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 13882) = 1/(6941 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-40571317 / 50000000) (-405713169 / 500000000) (Real.log (6941 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (356141801 / 1000000000) ≤ -Real.log (100000 / 142781) ∧
    -Real.log (100000 / 142781) ≤ (178070901 / 500000000) := by
  have h := checkLog_sound (w := (42781 / 242781)) (n := 12)
    (lo := (356141801 / 1000000000)) (hi := (178070901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142781 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142781 / 100000) = 1/(100000 / 142781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (356141801 / 1000000000) (178070901 / 500000000) (Real.log (142781 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (142781 / 100000) = -Real.log (100000 / 142781) := by
    rw [show ((142781 / 100000) : ℝ) = ((100000 / 142781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (279142087 / 500000000) ≤ -Real.log (57219 / 100000) ∧
    -Real.log (57219 / 100000) ≤ (22331367 / 40000000) := by
  have h := checkLog_sound (w := (42781 / 157219)) (n := 12)
    (lo := (279142087 / 500000000)) (hi := (22331367 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57219) = 1/(57219 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-22331367 / 40000000) (-279142087 / 500000000) (Real.log (57219 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14293437 / 40000000) ≤ -Real.log (250000 / 357379) ∧
    -Real.log (250000 / 357379) ≤ (178667963 / 500000000) := by
  have h := checkLog_sound (w := (107379 / 607379)) (n := 12)
    (lo := (14293437 / 40000000)) (hi := (178667963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357379 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357379 / 250000) = 1/(250000 / 357379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14293437 / 40000000) (178667963 / 500000000) (Real.log (357379 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (357379 / 250000) = -Real.log (250000 / 357379) := by
    rw [show ((357379 / 250000) : ℝ) = ((250000 / 357379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (112254031 / 200000000) ≤ -Real.log (142621 / 250000) ∧
    -Real.log (142621 / 250000) ≤ (140317539 / 250000000) := by
  have h := checkLog_sound (w := (107379 / 392621)) (n := 12)
    (lo := (112254031 / 200000000)) (hi := (140317539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142621) = 1/(142621 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-140317539 / 250000000) (-112254031 / 200000000) (Real.log (142621 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1248006003 / 1000000000) ≤ -Real.log (500000000000 / 1741695080151) ∧
    -Real.log (500000000000 / 1741695080151) ≤ (249601201 / 200000000) := by
  have h := checkLog_sound (w := (741695080151 / 2741695080151)) (n := 12)
    (lo := (554858823 / 1000000000)) (hi := (69357353 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741695080151 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1741695080151 / 1000000000000) = 1/(500000000000 / 1741695080151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1248006003 / 1000000000) (249601201 / 200000000) (Real.log (1741695080151 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1741695080151 / 500000000000) = -Real.log (500000000000 / 1741695080151) := by
    rw [show ((1741695080151 / 500000000000) : ℝ) = ((500000000000 / 1741695080151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (250680159 / 200000000) ≤ -Real.log (500000000000 / 1751116553811) ∧
    -Real.log (500000000000 / 1751116553811) ≤ (1253400797 / 1000000000) := by
  have h := checkLog_sound (w := (751116553811 / 2751116553811)) (n := 12)
    (lo := (112050723 / 200000000)) (hi := (35015851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1751116553811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1751116553811 / 1000000000000) = 1/(500000000000 / 1751116553811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (250680159 / 200000000) (1253400797 / 1000000000) (Real.log (1751116553811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1751116553811 / 500000000000) = -Real.log (500000000000 / 1751116553811) := by
    rw [show ((1751116553811 / 500000000000) : ℝ) = ((500000000000 / 1751116553811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (114303247 / 125000000) ≤ -Real.log (62500000000 / 155958903511) ∧
    -Real.log (62500000000 / 155958903511) ≤ (457212989 / 500000000) := by
  have h := checkLog_sound (w := (30958903511 / 280958903511)) (n := 12)
    (lo := (55319699 / 250000000)) (hi := (221278797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155958903511 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(155958903511 / 125000000000) = 1/(62500000000 / 155958903511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (114303247 / 125000000) (457212989 / 500000000) (Real.log (155958903511 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (155958903511 / 62500000000) = -Real.log (62500000000 / 155958903511) := by
    rw [show ((155958903511 / 62500000000) : ℝ) = ((62500000000 / 155958903511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (717661 / 781250) ≤ -Real.log (250000000000 / 626448769817) ∧
    -Real.log (250000000000 / 626448769817) ≤ (459303041 / 500000000) := by
  have h := checkLog_sound (w := (126448769817 / 1126448769817)) (n := 12)
    (lo := (2254589 / 10000000)) (hi := (225458901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626448769817 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(626448769817 / 500000000000) = 1/(250000000000 / 626448769817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (717661 / 781250) (459303041 / 500000000) (Real.log (626448769817 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (626448769817 / 250000000000) = -Real.log (250000000000 / 626448769817) := by
    rw [show ((626448769817 / 250000000000) : ℝ) = ((250000000000 / 626448769817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0113
