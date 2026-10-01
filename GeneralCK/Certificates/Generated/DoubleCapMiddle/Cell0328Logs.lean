import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0328
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

theorem reflection_log_1_neg : (8693821 / 40000000) ≤ -Real.log (5120 / 6363) ∧
    -Real.log (5120 / 6363) ≤ (108672763 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 11483)) (n := 12)
    (lo := (8693821 / 40000000)) (hi := (108672763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6363 / 5120) = 1/(5120 / 6363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8693821 / 40000000) (108672763 / 500000000) (Real.log (6363 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6363 / 5120) = -Real.log (5120 / 6363) := by
    rw [show ((6363 / 5120) : ℝ) = ((5120 / 6363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13904639 / 50000000) ≤ -Real.log (3877 / 5120) ∧
    -Real.log (3877 / 5120) ≤ (278092781 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 8997)) (n := 12)
    (lo := (13904639 / 50000000)) (hi := (278092781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3877) = 1/(3877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-278092781 / 1000000000) (-13904639 / 50000000) (Real.log (3877 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (217109759 / 1000000000) ≤ -Real.log (10240 / 12723) ∧
    -Real.log (10240 / 12723) ≤ (169617 / 781250) := by
  have h := checkLog_sound (w := (2483 / 22963)) (n := 12)
    (lo := (217109759 / 1000000000)) (hi := (169617 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12723 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12723 / 10240) = 1/(10240 / 12723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (217109759 / 1000000000) (169617 / 781250) (Real.log (12723 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12723 / 10240) = -Real.log (10240 / 12723) := by
    rw [show ((12723 / 10240) : ℝ) = ((10240 / 12723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138852979 / 500000000) ≤ -Real.log (7757 / 10240) ∧
    -Real.log (7757 / 10240) ≤ (277705959 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 17997)) (n := 12)
    (lo := (138852979 / 500000000)) (hi := (277705959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7757) = 1/(7757 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-277705959 / 1000000000) (-138852979 / 500000000) (Real.log (7757 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39578297 / 100000000) ≤ -Real.log (2560 / 3803) ∧
    -Real.log (2560 / 3803) ≤ (395782971 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 6363)) (n := 12)
    (lo := (39578297 / 100000000)) (hi := (395782971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3803 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3803 / 2560) = 1/(2560 / 3803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (39578297 / 100000000) (395782971 / 1000000000) (Real.log (3803 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3803 / 2560) = -Real.log (2560 / 3803) := by
    rw [show ((3803 / 2560) : ℝ) = ((2560 / 3803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (132930167 / 200000000) ≤ -Real.log (1317 / 2560) ∧
    -Real.log (1317 / 2560) ≤ (166162709 / 250000000) := by
  have h := checkLog_sound (w := (1243 / 3877)) (n := 12)
    (lo := (132930167 / 200000000)) (hi := (166162709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1317) = 1/(1317 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166162709 / 250000000) (-132930167 / 200000000) (Real.log (1317 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (395388467 / 1000000000) ≤ -Real.log (5120 / 7603) ∧
    -Real.log (5120 / 7603) ≤ (98847117 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 12723)) (n := 12)
    (lo := (395388467 / 1000000000)) (hi := (98847117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7603 / 5120) = 1/(5120 / 7603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (395388467 / 1000000000) (98847117 / 250000000) (Real.log (7603 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7603 / 5120) = -Real.log (5120 / 7603) := by
    rw [show ((7603 / 5120) : ℝ) = ((5120 / 7603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (663512531 / 1000000000) ≤ -Real.log (2637 / 5120) ∧
    -Real.log (2637 / 5120) ≤ (165878133 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7757)) (n := 12)
    (lo := (663512531 / 1000000000)) (hi := (165878133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2637) = 1/(2637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165878133 / 250000000) (-663512531 / 1000000000) (Real.log (2637 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (297623739 / 1000000000) ≤ -Real.log (200000 / 269331) ∧
    -Real.log (200000 / 269331) ≤ (14881187 / 50000000) := by
  have h := checkLog_sound (w := (69331 / 469331)) (n := 12)
    (lo := (297623739 / 1000000000)) (hi := (14881187 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269331 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269331 / 200000) = 1/(200000 / 269331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (297623739 / 1000000000) (14881187 / 50000000) (Real.log (269331 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (269331 / 200000) = -Real.log (200000 / 269331) := by
    rw [show ((269331 / 200000) : ℝ) = ((200000 / 269331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212824979 / 500000000) ≤ -Real.log (130669 / 200000) ∧
    -Real.log (130669 / 200000) ≤ (425649959 / 1000000000) := by
  have h := checkLog_sound (w := (69331 / 330669)) (n := 12)
    (lo := (212824979 / 500000000)) (hi := (425649959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130669) = 1/(130669 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-425649959 / 1000000000) (-212824979 / 500000000) (Real.log (130669 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148971499 / 500000000) ≤ -Real.log (200000 / 269417) ∧
    -Real.log (200000 / 269417) ≤ (297942999 / 1000000000) := by
  have h := checkLog_sound (w := (69417 / 469417)) (n := 12)
    (lo := (148971499 / 500000000)) (hi := (297942999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269417 / 200000) = 1/(200000 / 269417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148971499 / 500000000) (297942999 / 1000000000) (Real.log (269417 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (269417 / 200000) = -Real.log (200000 / 269417) := by
    rw [show ((269417 / 200000) : ℝ) = ((200000 / 269417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (213154163 / 500000000) ≤ -Real.log (130583 / 200000) ∧
    -Real.log (130583 / 200000) ≤ (426308327 / 1000000000) := by
  have h := checkLog_sound (w := (69417 / 330583)) (n := 12)
    (lo := (213154163 / 500000000)) (hi := (426308327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130583) = 1/(130583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-426308327 / 1000000000) (-213154163 / 500000000) (Real.log (130583 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225981919 / 1000000000) ≤ -Real.log (1000000 / 1253553) ∧
    -Real.log (1000000 / 1253553) ≤ (1412387 / 6250000) := by
  have h := checkLog_sound (w := (253553 / 2253553)) (n := 12)
    (lo := (225981919 / 1000000000)) (hi := (1412387 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253553 / 1000000) = 1/(1000000 / 1253553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225981919 / 1000000000) (1412387 / 6250000) (Real.log (1253553 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1253553 / 1000000) = -Real.log (1000000 / 1253553) := by
    rw [show ((1253553 / 1000000) : ℝ) = ((1000000 / 1253553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (146215331 / 500000000) ≤ -Real.log (746447 / 1000000) ∧
    -Real.log (746447 / 1000000) ≤ (292430663 / 1000000000) := by
  have h := checkLog_sound (w := (253553 / 1746447)) (n := 12)
    (lo := (146215331 / 500000000)) (hi := (292430663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746447) = 1/(746447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-292430663 / 1000000000) (-146215331 / 500000000) (Real.log (746447 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (226250719 / 1000000000) ≤ -Real.log (100000 / 125389) ∧
    -Real.log (100000 / 125389) ≤ (1414067 / 6250000) := by
  have h := checkLog_sound (w := (25389 / 225389)) (n := 12)
    (lo := (226250719 / 1000000000)) (hi := (1414067 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125389 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125389 / 100000) = 1/(100000 / 125389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (226250719 / 1000000000) (1414067 / 6250000) (Real.log (125389 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125389 / 100000) = -Real.log (100000 / 125389) := by
    rw [show ((125389 / 100000) : ℝ) = ((100000 / 125389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73220559 / 250000000) ≤ -Real.log (74611 / 100000) ∧
    -Real.log (74611 / 100000) ≤ (292882237 / 1000000000) := by
  have h := checkLog_sound (w := (25389 / 174611)) (n := 12)
    (lo := (73220559 / 250000000)) (hi := (292882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74611) = 1/(74611 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-292882237 / 1000000000) (-73220559 / 250000000) (Real.log (74611 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (723273697 / 1000000000) ≤ -Real.log (3906250000 / 8051444633) ∧
    -Real.log (3906250000 / 8051444633) ≤ (723273699 / 1000000000) := by
  have h := checkLog_sound (w := (238944633 / 15863944633)) (n := 12)
    (lo := (30126517 / 1000000000)) (hi := (15063259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8051444633 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8051444633 / 7812500000) = 1/(3906250000 / 8051444633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (723273697 / 1000000000) (723273699 / 1000000000) (Real.log (8051444633 / 3906250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8051444633 / 3906250000) = -Real.log (3906250000 / 8051444633) := by
    rw [show ((8051444633 / 3906250000) : ℝ) = ((3906250000 / 8051444633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (181062831 / 250000000) ≤ -Real.log (500000000000 / 1031592933231) ∧
    -Real.log (500000000000 / 1031592933231) ≤ (362125663 / 500000000) := by
  have h := checkLog_sound (w := (31592933231 / 2031592933231)) (n := 12)
    (lo := (1944009 / 62500000)) (hi := (6220829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031592933231 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1031592933231 / 1000000000000) = 1/(500000000000 / 1031592933231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (181062831 / 250000000) (362125663 / 500000000) (Real.log (1031592933231 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1031592933231 / 500000000000) = -Real.log (500000000000 / 1031592933231) := by
    rw [show ((1031592933231 / 500000000000) : ℝ) = ((500000000000 / 1031592933231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (518412581 / 1000000000) ≤ -Real.log (500000000000 / 839679843311) ∧
    -Real.log (500000000000 / 839679843311) ≤ (259206291 / 500000000) := by
  have h := checkLog_sound (w := (339679843311 / 1339679843311)) (n := 12)
    (lo := (518412581 / 1000000000)) (hi := (259206291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839679843311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839679843311 / 500000000000) = 1/(500000000000 / 839679843311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (518412581 / 1000000000) (259206291 / 500000000) (Real.log (839679843311 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (839679843311 / 500000000000) = -Real.log (500000000000 / 839679843311) := by
    rw [show ((839679843311 / 500000000000) : ℝ) = ((500000000000 / 839679843311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (103826591 / 200000000) ≤ -Real.log (25000000000 / 42014247229) ∧
    -Real.log (25000000000 / 42014247229) ≤ (129783239 / 250000000) := by
  have h := checkLog_sound (w := (17014247229 / 67014247229)) (n := 12)
    (lo := (103826591 / 200000000)) (hi := (129783239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42014247229 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42014247229 / 25000000000) = 1/(25000000000 / 42014247229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (103826591 / 200000000) (129783239 / 250000000) (Real.log (42014247229 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42014247229 / 25000000000) = -Real.log (25000000000 / 42014247229) := by
    rw [show ((42014247229 / 25000000000) : ℝ) = ((25000000000 / 42014247229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0328
