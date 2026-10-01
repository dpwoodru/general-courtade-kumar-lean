import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0052
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

theorem reflection_log_1_neg : (5826713 / 15625000) ≤ -Real.log (2560 / 3717) ∧
    -Real.log (2560 / 3717) ≤ (372909633 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 6277)) (n := 12)
    (lo := (5826713 / 15625000)) (hi := (372909633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3717 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3717 / 2560) = 1/(2560 / 3717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5826713 / 15625000) (372909633 / 1000000000) (Real.log (3717 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3717 / 2560) = -Real.log (2560 / 3717) := by
    rw [show ((3717 / 2560) : ℝ) = ((2560 / 3717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (601394457 / 1000000000) ≤ -Real.log (1403 / 2560) ∧
    -Real.log (1403 / 2560) ≤ (300697229 / 500000000) := by
  have h := checkLog_sound (w := (1157 / 3963)) (n := 12)
    (lo := (601394457 / 1000000000)) (hi := (300697229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1403) = 1/(1403 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-300697229 / 500000000) (-601394457 / 1000000000) (Real.log (1403 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (93025551 / 250000000) ≤ -Real.log (1280 / 1857) ∧
    -Real.log (1280 / 1857) ≤ (74420441 / 200000000) := by
  have h := checkLog_sound (w := (577 / 3137)) (n := 12)
    (lo := (93025551 / 250000000)) (hi := (74420441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1280) = 1/(1280 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (93025551 / 250000000) (74420441 / 200000000) (Real.log (1857 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1857 / 1280) = -Real.log (1280 / 1857) := by
    rw [show ((1857 / 1280) : ℝ) = ((1280 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (119851693 / 200000000) ≤ -Real.log (703 / 1280) ∧
    -Real.log (703 / 1280) ≤ (299629233 / 500000000) := by
  have h := checkLog_sound (w := (577 / 1983)) (n := 12)
    (lo := (119851693 / 200000000)) (hi := (299629233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 703) = 1/(703 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299629233 / 500000000) (-119851693 / 200000000) (Real.log (703 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40244231 / 62500000) ≤ -Real.log (1280 / 2437) ∧
    -Real.log (1280 / 2437) ≤ (643907697 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 3717)) (n := 12)
    (lo := (40244231 / 62500000)) (hi := (643907697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2437 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2437 / 1280) = 1/(1280 / 2437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40244231 / 62500000) (643907697 / 1000000000) (Real.log (2437 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2437 / 1280) = -Real.log (1280 / 2437) := by
    rw [show ((2437 / 1280) : ℝ) = ((1280 / 2437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2342430999 / 1000000000) ≤ -Real.log (123 / 1280) ∧
    -Real.log (123 / 1280) ≤ (2342431003 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 123) = 1/(123 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2342431003 / 1000000000) (-2342430999 / 1000000000) (Real.log (123 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (160668979 / 250000000) ≤ -Real.log (640 / 1217) ∧
    -Real.log (640 / 1217) ≤ (642675917 / 1000000000) := by
  have h := checkLog_sound (w := (577 / 1857)) (n := 12)
    (lo := (160668979 / 250000000)) (hi := (642675917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217 / 640) = 1/(640 / 1217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (160668979 / 250000000) (642675917 / 1000000000) (Real.log (1217 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217 / 640) = -Real.log (640 / 1217) := by
    rw [show ((1217 / 640) : ℝ) = ((640 / 1217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (289791681 / 125000000) ≤ -Real.log (63 / 640) ∧
    -Real.log (63 / 640) ≤ (579583363 / 250000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 63) = 1/(63 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-579583363 / 250000000) (-289791681 / 125000000) (Real.log (63 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (257583493 / 500000000) ≤ -Real.log (500000 / 836959) ∧
    -Real.log (500000 / 836959) ≤ (515166987 / 1000000000) := by
  have h := checkLog_sound (w := (336959 / 1336959)) (n := 12)
    (lo := (257583493 / 500000000)) (hi := (515166987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836959 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836959 / 500000) = 1/(500000 / 836959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (257583493 / 500000000) (515166987 / 1000000000) (Real.log (836959 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (836959 / 500000) = -Real.log (500000 / 836959) := by
    rw [show ((836959 / 500000) : ℝ) = ((500000 / 836959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (560303197 / 500000000) ≤ -Real.log (163041 / 500000) ∧
    -Real.log (163041 / 500000) ≤ (280151599 / 250000000) := by
  have h := checkLog_sound (w := (86959 / 413041)) (n := 12)
    (lo := (213729607 / 500000000)) (hi := (85491843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 163041) = 1/(163041 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-280151599 / 250000000) (-560303197 / 500000000) (Real.log (163041 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258218127 / 500000000) ≤ -Real.log (250000 / 419011) ∧
    -Real.log (250000 / 419011) ≤ (103287251 / 200000000) := by
  have h := checkLog_sound (w := (169011 / 669011)) (n := 12)
    (lo := (258218127 / 500000000)) (hi := (103287251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419011 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419011 / 250000) = 1/(250000 / 419011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258218127 / 500000000) (103287251 / 200000000) (Real.log (419011 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (419011 / 250000) = -Real.log (250000 / 419011) := by
    rw [show ((419011 / 250000) : ℝ) = ((250000 / 419011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (563573787 / 500000000) ≤ -Real.log (80989 / 250000) ∧
    -Real.log (80989 / 250000) ≤ (140893447 / 125000000) := by
  have h := checkLog_sound (w := (44011 / 205989)) (n := 12)
    (lo := (217000197 / 500000000)) (hi := (86800079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80989) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 80989) = 1/(80989 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140893447 / 125000000) (-563573787 / 500000000) (Real.log (80989 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86892647 / 200000000) ≤ -Real.log (500000 / 772067) ∧
    -Real.log (500000 / 772067) ≤ (108615809 / 250000000) := by
  have h := checkLog_sound (w := (272067 / 1272067)) (n := 12)
    (lo := (86892647 / 200000000)) (hi := (108615809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772067 / 500000) = 1/(500000 / 772067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86892647 / 200000000) (108615809 / 250000000) (Real.log (772067 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (772067 / 500000) = -Real.log (500000 / 772067) := by
    rw [show ((772067 / 500000) : ℝ) = ((500000 / 772067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (785556371 / 1000000000) ≤ -Real.log (227933 / 500000) ∧
    -Real.log (227933 / 500000) ≤ (785556373 / 1000000000) := by
  have h := checkLog_sound (w := (22067 / 477933)) (n := 12)
    (lo := (92409191 / 1000000000)) (hi := (11551149 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 227933) = 1/(227933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-785556373 / 1000000000) (-785556371 / 1000000000) (Real.log (227933 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (435882441 / 1000000000) ≤ -Real.log (1000000 / 1546327) ∧
    -Real.log (1000000 / 1546327) ≤ (217941221 / 500000000) := by
  have h := checkLog_sound (w := (546327 / 2546327)) (n := 12)
    (lo := (435882441 / 1000000000)) (hi := (217941221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1546327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1546327 / 1000000) = 1/(1000000 / 1546327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (435882441 / 1000000000) (217941221 / 500000000) (Real.log (1546327 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1546327 / 1000000) = -Real.log (1000000 / 1546327) := by
    rw [show ((1546327 / 1000000) : ℝ) = ((1000000 / 1546327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197594651 / 250000000) ≤ -Real.log (453673 / 1000000) ∧
    -Real.log (453673 / 1000000) ≤ (395189303 / 500000000) := by
  have h := checkLog_sound (w := (46327 / 953673)) (n := 12)
    (lo := (1519241 / 15625000)) (hi := (3889257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453673) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 453673) = 1/(453673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-395189303 / 500000000) (-197594651 / 250000000) (Real.log (453673 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (81788669 / 50000000) ≤ -Real.log (125000000000 / 641678320177) ∧
    -Real.log (125000000000 / 641678320177) ≤ (1635773383 / 1000000000) := by
  have h := checkLog_sound (w := (141678320177 / 1141678320177)) (n := 12)
    (lo := (12473951 / 50000000)) (hi := (249479021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641678320177 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(641678320177 / 500000000000) = 1/(125000000000 / 641678320177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81788669 / 50000000) (1635773383 / 1000000000) (Real.log (641678320177 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (641678320177 / 125000000000) = -Real.log (125000000000 / 641678320177) := by
    rw [show ((641678320177 / 125000000000) : ℝ) = ((125000000000 / 641678320177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410895957 / 250000000) ≤ -Real.log (500000000000 / 2586838953439) ∧
    -Real.log (500000000000 / 2586838953439) ≤ (1643583831 / 1000000000) := by
  have h := checkLog_sound (w := (586838953439 / 4586838953439)) (n := 12)
    (lo := (64322367 / 250000000)) (hi := (257289469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2586838953439 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2586838953439 / 2000000000000) = 1/(500000000000 / 2586838953439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410895957 / 250000000) (1643583831 / 1000000000) (Real.log (2586838953439 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2586838953439 / 500000000000) = -Real.log (500000000000 / 2586838953439) := by
    rw [show ((2586838953439 / 500000000000) : ℝ) = ((500000000000 / 2586838953439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1220019607 / 1000000000) ≤ -Real.log (250000000000 / 846813537311) ∧
    -Real.log (250000000000 / 846813537311) ≤ (1220019609 / 1000000000) := by
  have h := checkLog_sound (w := (346813537311 / 1346813537311)) (n := 12)
    (lo := (526872427 / 1000000000)) (hi := (131718107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846813537311 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(846813537311 / 500000000000) = 1/(250000000000 / 846813537311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1220019607 / 1000000000) (1220019609 / 1000000000) (Real.log (846813537311 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (846813537311 / 250000000000) = -Real.log (250000000000 / 846813537311) := by
    rw [show ((846813537311 / 250000000000) : ℝ) = ((250000000000 / 846813537311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (245252209 / 200000000) ≤ -Real.log (500000000000 / 1704230800599) ∧
    -Real.log (500000000000 / 1704230800599) ≤ (1226261047 / 1000000000) := by
  have h := checkLog_sound (w := (704230800599 / 2704230800599)) (n := 12)
    (lo := (106622773 / 200000000)) (hi := (266556933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704230800599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704230800599 / 1000000000000) = 1/(500000000000 / 1704230800599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (245252209 / 200000000) (1226261047 / 1000000000) (Real.log (1704230800599 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1704230800599 / 500000000000) = -Real.log (500000000000 / 1704230800599) := by
    rw [show ((1704230800599 / 500000000000) : ℝ) = ((500000000000 / 1704230800599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0052
