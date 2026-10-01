import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0378
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

theorem reflection_log_1_neg : (25686077 / 125000000) ≤ -Real.log (320 / 393) ∧
    -Real.log (320 / 393) ≤ (205488617 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 713)) (n := 12)
    (lo := (25686077 / 125000000)) (hi := (205488617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 320) = 1/(320 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25686077 / 125000000) (205488617 / 1000000000) (Real.log (393 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (393 / 320) = -Real.log (320 / 393) := by
    rw [show ((393 / 320) : ℝ) = ((320 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (258932659 / 1000000000) ≤ -Real.log (247 / 320) ∧
    -Real.log (247 / 320) ≤ (12946633 / 50000000) := by
  have h := checkLog_sound (w := (73 / 567)) (n := 12)
    (lo := (258932659 / 1000000000)) (hi := (12946633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 247) = 1/(247 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12946633 / 50000000) (-258932659 / 1000000000) (Real.log (247 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205250037 / 1000000000) ≤ -Real.log (10240 / 12573) ∧
    -Real.log (10240 / 12573) ≤ (102625019 / 500000000) := by
  have h := checkLog_sound (w := (2333 / 22813)) (n := 12)
    (lo := (205250037 / 1000000000)) (hi := (102625019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12573 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12573 / 10240) = 1/(10240 / 12573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205250037 / 1000000000) (102625019 / 500000000) (Real.log (12573 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12573 / 10240) = -Real.log (10240 / 12573) := by
    rw [show ((12573 / 10240) : ℝ) = ((10240 / 12573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32319147 / 125000000) ≤ -Real.log (7907 / 10240) ∧
    -Real.log (7907 / 10240) ≤ (258553177 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 18147)) (n := 12)
    (lo := (32319147 / 125000000)) (hi := (258553177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7907) = 1/(7907 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-258553177 / 1000000000) (-32319147 / 125000000) (Real.log (7907 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (187932319 / 500000000) ≤ -Real.log (160 / 233) ∧
    -Real.log (160 / 233) ≤ (375864639 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 393)) (n := 12)
    (lo := (187932319 / 500000000)) (hi := (375864639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233 / 160) = 1/(160 / 233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (187932319 / 500000000) (375864639 / 1000000000) (Real.log (233 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (233 / 160) = -Real.log (160 / 233) := by
    rw [show ((233 / 160) : ℝ) = ((160 / 233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (19039553 / 31250000) ≤ -Real.log (87 / 160) ∧
    -Real.log (87 / 160) ≤ (609265697 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 87) = 1/(87 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609265697 / 1000000000) (-19039553 / 31250000) (Real.log (87 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93865549 / 250000000) ≤ -Real.log (5120 / 7453) ∧
    -Real.log (5120 / 7453) ≤ (375462197 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 12573)) (n := 12)
    (lo := (93865549 / 250000000)) (hi := (375462197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7453 / 5120) = 1/(5120 / 7453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93865549 / 250000000) (375462197 / 1000000000) (Real.log (7453 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7453 / 5120) = -Real.log (5120 / 7453) := by
    rw [show ((7453 / 5120) : ℝ) = ((5120 / 7453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60818869 / 100000000) ≤ -Real.log (2787 / 5120) ∧
    -Real.log (2787 / 5120) ≤ (608188691 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 7907)) (n := 12)
    (lo := (60818869 / 100000000)) (hi := (608188691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2787) = 1/(2787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-608188691 / 1000000000) (-60818869 / 100000000) (Real.log (2787 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281609421 / 1000000000) ≤ -Real.log (1000000 / 1325261) ∧
    -Real.log (1000000 / 1325261) ≤ (140804711 / 500000000) := by
  have h := checkLog_sound (w := (325261 / 2325261)) (n := 12)
    (lo := (281609421 / 1000000000)) (hi := (140804711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325261 / 1000000) = 1/(1000000 / 1325261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281609421 / 1000000000) (140804711 / 500000000) (Real.log (1325261 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1325261 / 1000000) = -Real.log (1000000 / 1325261) := by
    rw [show ((1325261 / 1000000) : ℝ) = ((1000000 / 1325261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (393429329 / 1000000000) ≤ -Real.log (674739 / 1000000) ∧
    -Real.log (674739 / 1000000) ≤ (39342933 / 100000000) := by
  have h := checkLog_sound (w := (325261 / 1674739)) (n := 12)
    (lo := (393429329 / 1000000000)) (hi := (39342933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674739) = 1/(674739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39342933 / 100000000) (-393429329 / 1000000000) (Real.log (674739 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (70483081 / 250000000) ≤ -Real.log (1000000 / 1325689) ∧
    -Real.log (1000000 / 1325689) ≤ (11277293 / 40000000) := by
  have h := checkLog_sound (w := (325689 / 2325689)) (n := 12)
    (lo := (70483081 / 250000000)) (hi := (11277293 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325689 / 1000000) = 1/(1000000 / 1325689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (70483081 / 250000000) (11277293 / 40000000) (Real.log (1325689 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1325689 / 1000000) = -Real.log (1000000 / 1325689) := by
    rw [show ((1325689 / 1000000) : ℝ) = ((1000000 / 1325689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7881277 / 20000000) ≤ -Real.log (674311 / 1000000) ∧
    -Real.log (674311 / 1000000) ≤ (394063851 / 1000000000) := by
  have h := checkLog_sound (w := (325689 / 1674311)) (n := 12)
    (lo := (7881277 / 20000000)) (hi := (394063851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674311) = 1/(674311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-394063851 / 1000000000) (-7881277 / 20000000) (Real.log (674311 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5315853 / 25000000) ≤ -Real.log (250000 / 309233) ∧
    -Real.log (250000 / 309233) ≤ (212634121 / 1000000000) := by
  have h := checkLog_sound (w := (59233 / 559233)) (n := 12)
    (lo := (5315853 / 25000000)) (hi := (212634121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309233 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309233 / 250000) = 1/(250000 / 309233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5315853 / 25000000) (212634121 / 1000000000) (Real.log (309233 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (309233 / 250000) = -Real.log (250000 / 309233) := by
    rw [show ((309233 / 250000) : ℝ) = ((250000 / 309233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (270408129 / 1000000000) ≤ -Real.log (190767 / 250000) ∧
    -Real.log (190767 / 250000) ≤ (27040813 / 100000000) := by
  have h := checkLog_sound (w := (59233 / 440767)) (n := 12)
    (lo := (270408129 / 1000000000)) (hi := (27040813 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190767) = 1/(190767 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-27040813 / 100000000) (-270408129 / 1000000000) (Real.log (190767 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (212901681 / 1000000000) ≤ -Real.log (1000000 / 1237263) ∧
    -Real.log (1000000 / 1237263) ≤ (106450841 / 500000000) := by
  have h := checkLog_sound (w := (237263 / 2237263)) (n := 12)
    (lo := (212901681 / 1000000000)) (hi := (106450841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237263 / 1000000) = 1/(1000000 / 1237263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212901681 / 1000000000) (106450841 / 500000000) (Real.log (1237263 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1237263 / 1000000) = -Real.log (1000000 / 1237263) := by
    rw [show ((1237263 / 1000000) : ℝ) = ((1000000 / 1237263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (270841999 / 1000000000) ≤ -Real.log (762737 / 1000000) ∧
    -Real.log (762737 / 1000000) ≤ (135421 / 500000) := by
  have h := checkLog_sound (w := (237263 / 1762737)) (n := 12)
    (lo := (270841999 / 1000000000)) (hi := (135421 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762737) = 1/(762737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-135421 / 500000) (-270841999 / 1000000000) (Real.log (762737 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (540031 / 800000) ≤ -Real.log (500000000000 / 982054542571) ∧
    -Real.log (500000000000 / 982054542571) ≤ (675038751 / 1000000000) := by
  have h := checkLog_sound (w := (482054542571 / 1482054542571)) (n := 12)
    (lo := (540031 / 800000)) (hi := (675038751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982054542571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982054542571 / 500000000000) = 1/(500000000000 / 982054542571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (540031 / 800000) (675038751 / 1000000000) (Real.log (982054542571 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (982054542571 / 500000000000) = -Real.log (500000000000 / 982054542571) := by
    rw [show ((982054542571 / 500000000000) : ℝ) = ((500000000000 / 982054542571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (337998087 / 500000000) ≤ -Real.log (500000000000 / 982995235137) ∧
    -Real.log (500000000000 / 982995235137) ≤ (27039847 / 40000000) := by
  have h := checkLog_sound (w := (482995235137 / 1482995235137)) (n := 12)
    (lo := (337998087 / 500000000)) (hi := (27039847 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982995235137 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982995235137 / 500000000000) = 1/(500000000000 / 982995235137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (337998087 / 500000000) (27039847 / 40000000) (Real.log (982995235137 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (982995235137 / 500000000000) = -Real.log (500000000000 / 982995235137) := by
    rw [show ((982995235137 / 500000000000) : ℝ) = ((500000000000 / 982995235137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (483042249 / 1000000000) ≤ -Real.log (500000000000 / 810499195353) ∧
    -Real.log (500000000000 / 810499195353) ≤ (1932169 / 4000000) := by
  have h := checkLog_sound (w := (310499195353 / 1310499195353)) (n := 12)
    (lo := (483042249 / 1000000000)) (hi := (1932169 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810499195353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810499195353 / 500000000000) = 1/(500000000000 / 810499195353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (483042249 / 1000000000) (1932169 / 4000000) (Real.log (810499195353 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (810499195353 / 500000000000) = -Real.log (500000000000 / 810499195353) := by
    rw [show ((810499195353 / 500000000000) : ℝ) = ((500000000000 / 810499195353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (483743681 / 1000000000) ≤ -Real.log (25000000000 / 40553395207) ∧
    -Real.log (25000000000 / 40553395207) ≤ (241871841 / 500000000) := by
  have h := checkLog_sound (w := (15553395207 / 65553395207)) (n := 12)
    (lo := (483743681 / 1000000000)) (hi := (241871841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40553395207 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40553395207 / 25000000000) = 1/(25000000000 / 40553395207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (483743681 / 1000000000) (241871841 / 500000000) (Real.log (40553395207 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (40553395207 / 25000000000) = -Real.log (25000000000 / 40553395207) := by
    rw [show ((40553395207 / 25000000000) : ℝ) = ((25000000000 / 40553395207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0378
