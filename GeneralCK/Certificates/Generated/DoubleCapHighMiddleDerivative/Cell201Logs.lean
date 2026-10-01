import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell201
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (62722497 / 200000000) ≤ -Real.log (2560 / 3503) ∧
    -Real.log (2560 / 3503) ≤ (156806243 / 500000000) := by
  have h := checkLog_sound (w := (943 / 6063)) (n := 12)
    (lo := (62722497 / 200000000)) (hi := (156806243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3503 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3503 / 2560) = 1/(2560 / 3503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62722497 / 200000000) (156806243 / 500000000) (Real.log (3503 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3503 / 2560) = -Real.log (2560 / 3503) := by
    rw [show ((3503 / 2560) : ℝ) = ((2560 / 3503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (459434677 / 1000000000) ≤ -Real.log (1617 / 2560) ∧
    -Real.log (1617 / 2560) ≤ (229717339 / 500000000) := by
  have h := checkLog_sound (w := (943 / 4177)) (n := 12)
    (lo := (459434677 / 1000000000)) (hi := (229717339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1617) = 1/(1617 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229717339 / 500000000) (-459434677 / 1000000000) (Real.log (1617 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (313184189 / 1000000000) ≤ -Real.log (5120 / 7003) ∧
    -Real.log (5120 / 7003) ≤ (31318419 / 100000000) := by
  have h := checkLog_sound (w := (1883 / 12123)) (n := 12)
    (lo := (313184189 / 1000000000)) (hi := (31318419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7003 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7003 / 5120) = 1/(5120 / 7003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (313184189 / 1000000000) (31318419 / 100000000) (Real.log (7003 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7003 / 5120) = -Real.log (5120 / 7003) := by
    rw [show ((7003 / 5120) : ℝ) = ((5120 / 7003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57313433 / 125000000) ≤ -Real.log (3237 / 5120) ∧
    -Real.log (3237 / 5120) ≤ (91701493 / 200000000) := by
  have h := checkLog_sound (w := (1883 / 8357)) (n := 12)
    (lo := (57313433 / 125000000)) (hi := (91701493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3237) = 1/(3237 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91701493 / 200000000) (-57313433 / 125000000) (Real.log (3237 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23238789 / 100000000) ≤ -Real.log (1000000 / 1261609) ∧
    -Real.log (1000000 / 1261609) ≤ (232387891 / 1000000000) := by
  have h := checkLog_sound (w := (261609 / 2261609)) (n := 12)
    (lo := (23238789 / 100000000)) (hi := (232387891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261609 / 1000000) = 1/(1000000 / 1261609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23238789 / 100000000) (232387891 / 1000000000) (Real.log (1261609 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1261609 / 1000000) = -Real.log (1000000 / 1261609) := by
    rw [show ((1261609 / 1000000) : ℝ) = ((1000000 / 1261609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (37910223 / 125000000) ≤ -Real.log (738391 / 1000000) ∧
    -Real.log (738391 / 1000000) ≤ (60656357 / 200000000) := by
  have h := checkLog_sound (w := (261609 / 1738391)) (n := 12)
    (lo := (37910223 / 125000000)) (hi := (60656357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738391) = 1/(738391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60656357 / 200000000) (-37910223 / 125000000) (Real.log (738391 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2909039 / 12500000) ≤ -Real.log (62500 / 78877) ∧
    -Real.log (62500 / 78877) ≤ (232723121 / 1000000000) := by
  have h := checkLog_sound (w := (16377 / 141377)) (n := 12)
    (lo := (2909039 / 12500000)) (hi := (232723121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78877 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78877 / 62500) = 1/(62500 / 78877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2909039 / 12500000) (232723121 / 1000000000) (Real.log (78877 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78877 / 62500) = -Real.log (62500 / 78877) := by
    rw [show ((78877 / 62500) : ℝ) = ((62500 / 78877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60770963 / 200000000) ≤ -Real.log (46123 / 62500) ∧
    -Real.log (46123 / 62500) ≤ (9495463 / 31250000) := by
  have h := checkLog_sound (w := (16377 / 108623)) (n := 12)
    (lo := (60770963 / 200000000)) (hi := (9495463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46123) = 1/(46123 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9495463 / 31250000) (-60770963 / 200000000) (Real.log (46123 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17274249 / 100000000) ≤ -Real.log (12500 / 14857) ∧
    -Real.log (12500 / 14857) ≤ (172742491 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 27357)) (n := 12)
    (lo := (17274249 / 100000000)) (hi := (172742491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14857 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14857 / 12500) = 1/(12500 / 14857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17274249 / 100000000) (172742491 / 1000000000) (Real.log (14857 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (14857 / 12500) = -Real.log (12500 / 14857) := by
    rw [show ((14857 / 12500) : ℝ) = ((12500 / 14857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208944831 / 1000000000) ≤ -Real.log (10143 / 12500) ∧
    -Real.log (10143 / 12500) ≤ (3264763 / 15625000) := by
  have h := checkLog_sound (w := (2357 / 22643)) (n := 12)
    (lo := (208944831 / 1000000000)) (hi := (3264763 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10143) = 1/(10143 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3264763 / 15625000) (-208944831 / 1000000000) (Real.log (10143 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43252291 / 250000000) ≤ -Real.log (1000000 / 1188877) ∧
    -Real.log (1000000 / 1188877) ≤ (34601833 / 200000000) := by
  have h := checkLog_sound (w := (188877 / 2188877)) (n := 12)
    (lo := (43252291 / 250000000)) (hi := (34601833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188877 / 1000000) = 1/(1000000 / 1188877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43252291 / 250000000) (34601833 / 200000000) (Real.log (1188877 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1188877 / 1000000) = -Real.log (1000000 / 1188877) := by
    rw [show ((1188877 / 1000000) : ℝ) = ((1000000 / 1188877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209335571 / 1000000000) ≤ -Real.log (811123 / 1000000) ∧
    -Real.log (811123 / 1000000) ≤ (52333893 / 250000000) := by
  have h := checkLog_sound (w := (188877 / 1811123)) (n := 12)
    (lo := (209335571 / 1000000000)) (hi := (52333893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811123) = 1/(811123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-52333893 / 250000000) (-209335571 / 1000000000) (Real.log (811123 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (771691653 / 1000000000) ≤ -Real.log (500000000000 / 1081711461229) ∧
    -Real.log (500000000000 / 1081711461229) ≤ (154338331 / 200000000) := by
  have h := checkLog_sound (w := (81711461229 / 2081711461229)) (n := 12)
    (lo := (78544473 / 1000000000)) (hi := (39272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081711461229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1081711461229 / 1000000000000) = 1/(500000000000 / 1081711461229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (771691653 / 1000000000) (154338331 / 200000000) (Real.log (1081711461229 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1081711461229 / 500000000000) = -Real.log (500000000000 / 1081711461229) := by
    rw [show ((1081711461229 / 500000000000) : ℝ) = ((500000000000 / 1081711461229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (773047163 / 1000000000) ≤ -Real.log (125000000000 / 270794681509) ∧
    -Real.log (125000000000 / 270794681509) ≤ (154609433 / 200000000) := by
  have h := checkLog_sound (w := (20794681509 / 520794681509)) (n := 12)
    (lo := (79899983 / 1000000000)) (hi := (4993749 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270794681509 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270794681509 / 250000000000) = 1/(125000000000 / 270794681509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (773047163 / 1000000000) (154609433 / 200000000) (Real.log (270794681509 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (270794681509 / 125000000000) = -Real.log (125000000000 / 270794681509) := by
    rw [show ((270794681509 / 125000000000) : ℝ) = ((125000000000 / 270794681509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (267834837 / 500000000) ≤ -Real.log (62500000000 / 106787003769) ∧
    -Real.log (62500000000 / 106787003769) ≤ (21426787 / 40000000) := by
  have h := checkLog_sound (w := (44287003769 / 169287003769)) (n := 12)
    (lo := (267834837 / 500000000)) (hi := (21426787 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106787003769 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106787003769 / 62500000000) = 1/(62500000000 / 106787003769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (267834837 / 500000000) (21426787 / 40000000) (Real.log (106787003769 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (106787003769 / 62500000000) = -Real.log (62500000000 / 106787003769) := by
    rw [show ((106787003769 / 62500000000) : ℝ) = ((62500000000 / 106787003769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33536121 / 62500000) ≤ -Real.log (500000000000 / 855072306659) ∧
    -Real.log (500000000000 / 855072306659) ≤ (536577937 / 1000000000) := by
  have h := checkLog_sound (w := (355072306659 / 1355072306659)) (n := 12)
    (lo := (33536121 / 62500000)) (hi := (536577937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855072306659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855072306659 / 500000000000) = 1/(500000000000 / 855072306659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (33536121 / 62500000) (536577937 / 1000000000) (Real.log (855072306659 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (855072306659 / 500000000000) = -Real.log (500000000000 / 855072306659) := by
    rw [show ((855072306659 / 500000000000) : ℝ) = ((500000000000 / 855072306659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (190843661 / 500000000) ≤ -Real.log (250000000000 / 366188504387) ∧
    -Real.log (250000000000 / 366188504387) ≤ (381687323 / 1000000000) := by
  have h := checkLog_sound (w := (116188504387 / 616188504387)) (n := 12)
    (lo := (190843661 / 500000000)) (hi := (381687323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366188504387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366188504387 / 250000000000) = 1/(250000000000 / 366188504387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190843661 / 500000000) (381687323 / 1000000000) (Real.log (366188504387 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (366188504387 / 250000000000) = -Real.log (250000000000 / 366188504387) := by
    rw [show ((366188504387 / 250000000000) : ℝ) = ((250000000000 / 366188504387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76468947 / 200000000) ≤ -Real.log (250000000000 / 366429320831) ∧
    -Real.log (250000000000 / 366429320831) ≤ (11948273 / 31250000) := by
  have h := checkLog_sound (w := (116429320831 / 616429320831)) (n := 12)
    (lo := (76468947 / 200000000)) (hi := (11948273 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366429320831 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366429320831 / 250000000000) = 1/(250000000000 / 366429320831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76468947 / 200000000) (11948273 / 31250000) (Real.log (366429320831 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (366429320831 / 250000000000) = -Real.log (250000000000 / 366429320831) := by
    rw [show ((366429320831 / 250000000000) : ℝ) = ((250000000000 / 366429320831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36326407 / 1000000000) ≤ -Real.log (964325478871 / 1000000000000) ∧
    -Real.log (964325478871 / 1000000000000) ≤ (4540801 / 125000000) := by
  have h := checkLog_sound (w := (35674521129 / 1964325478871)) (n := 12)
    (lo := (36326407 / 1000000000)) (hi := (4540801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964325478871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964325478871) = 1/(964325478871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4540801 / 125000000) (-36326407 / 1000000000) (Real.log (964325478871 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36202341 / 1000000000) ≤ -Real.log (150694551 / 156250000) ∧
    -Real.log (150694551 / 156250000) ≤ (18101171 / 500000000) := by
  have h := checkLog_sound (w := (5555449 / 306944551)) (n := 12)
    (lo := (36202341 / 1000000000)) (hi := (18101171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 150694551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 150694551) = 1/(150694551 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18101171 / 500000000) (-36202341 / 1000000000) (Real.log (150694551 / 156250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell201
