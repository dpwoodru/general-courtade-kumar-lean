import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0445
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

theorem reflection_log_1_neg : (11836043 / 62500000) ≤ -Real.log (2048 / 2475) ∧
    -Real.log (2048 / 2475) ≤ (189376689 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4523)) (n := 12)
    (lo := (11836043 / 62500000)) (hi := (189376689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2475 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2475 / 2048) = 1/(2048 / 2475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11836043 / 62500000) (189376689 / 1000000000) (Real.log (2475 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2475 / 2048) = -Real.log (2048 / 2475) := by
    rw [show ((2475 / 2048) : ℝ) = ((2048 / 2475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14613779 / 62500000) ≤ -Real.log (1621 / 2048) ∧
    -Real.log (1621 / 2048) ≤ (46764093 / 200000000) := by
  have h := checkLog_sound (w := (427 / 3669)) (n := 12)
    (lo := (14613779 / 62500000)) (hi := (46764093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1621) = 1/(1621 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46764093 / 200000000) (-14613779 / 62500000) (Real.log (1621 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37826847 / 200000000) ≤ -Real.log (2560 / 3093) ∧
    -Real.log (2560 / 3093) ≤ (47283559 / 250000000) := by
  have h := checkLog_sound (w := (533 / 5653)) (n := 12)
    (lo := (37826847 / 200000000)) (hi := (47283559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3093 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3093 / 2560) = 1/(2560 / 3093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37826847 / 200000000) (47283559 / 250000000) (Real.log (3093 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3093 / 2560) = -Real.log (2560 / 3093) := by
    rw [show ((3093 / 2560) : ℝ) = ((2560 / 3093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (233450391 / 1000000000) ≤ -Real.log (2027 / 2560) ∧
    -Real.log (2027 / 2560) ≤ (29181299 / 125000000) := by
  have h := checkLog_sound (w := (533 / 4587)) (n := 12)
    (lo := (233450391 / 1000000000)) (hi := (29181299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2027) = 1/(2027 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-29181299 / 125000000) (-233450391 / 1000000000) (Real.log (2027 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348536447 / 1000000000) ≤ -Real.log (1024 / 1451) ∧
    -Real.log (1024 / 1451) ≤ (2722941 / 7812500) := by
  have h := checkLog_sound (w := (427 / 2475)) (n := 12)
    (lo := (348536447 / 1000000000)) (hi := (2722941 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1024) = 1/(1024 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348536447 / 1000000000) (2722941 / 7812500) (Real.log (1451 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1451 / 1024) = -Real.log (1024 / 1451) := by
    rw [show ((1451 / 1024) : ℝ) = ((1024 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (134888673 / 250000000) ≤ -Real.log (597 / 1024) ∧
    -Real.log (597 / 1024) ≤ (539554693 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1621)) (n := 12)
    (lo := (134888673 / 250000000)) (hi := (539554693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 597) = 1/(597 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-539554693 / 1000000000) (-134888673 / 250000000) (Real.log (597 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348122853 / 1000000000) ≤ -Real.log (1280 / 1813) ∧
    -Real.log (1280 / 1813) ≤ (174061427 / 500000000) := by
  have h := checkLog_sound (w := (533 / 3093)) (n := 12)
    (lo := (348122853 / 1000000000)) (hi := (174061427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1280) = 1/(1280 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348122853 / 1000000000) (174061427 / 500000000) (Real.log (1813 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1813 / 1280) = -Real.log (1280 / 1813) := by
    rw [show ((1813 / 1280) : ℝ) = ((1280 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (538550171 / 1000000000) ≤ -Real.log (747 / 1280) ∧
    -Real.log (747 / 1280) ≤ (134637543 / 250000000) := by
  have h := checkLog_sound (w := (533 / 2027)) (n := 12)
    (lo := (538550171 / 1000000000)) (hi := (134637543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 747) = 1/(747 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-134637543 / 250000000) (-538550171 / 1000000000) (Real.log (747 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259852651 / 1000000000) ≤ -Real.log (1000000 / 1296739) ∧
    -Real.log (1000000 / 1296739) ≤ (64963163 / 250000000) := by
  have h := checkLog_sound (w := (296739 / 2296739)) (n := 12)
    (lo := (259852651 / 1000000000)) (hi := (64963163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296739 / 1000000) = 1/(1000000 / 1296739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259852651 / 1000000000) (64963163 / 250000000) (Real.log (1296739 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1296739 / 1000000) = -Real.log (1000000 / 1296739) := by
    rw [show ((1296739 / 1000000) : ℝ) = ((1000000 / 1296739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35202719 / 100000000) ≤ -Real.log (703261 / 1000000) ∧
    -Real.log (703261 / 1000000) ≤ (352027191 / 1000000000) := by
  have h := checkLog_sound (w := (296739 / 1703261)) (n := 12)
    (lo := (35202719 / 100000000)) (hi := (352027191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 703261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 703261) = 1/(703261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-352027191 / 1000000000) (-35202719 / 100000000) (Real.log (703261 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (260181113 / 1000000000) ≤ -Real.log (200000 / 259433) ∧
    -Real.log (200000 / 259433) ≤ (130090557 / 500000000) := by
  have h := checkLog_sound (w := (59433 / 459433)) (n := 12)
    (lo := (260181113 / 1000000000)) (hi := (130090557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259433 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259433 / 200000) = 1/(200000 / 259433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (260181113 / 1000000000) (130090557 / 500000000) (Real.log (259433 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (259433 / 200000) = -Real.log (200000 / 259433) := by
    rw [show ((259433 / 200000) : ℝ) = ((200000 / 259433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (352633123 / 1000000000) ≤ -Real.log (140567 / 200000) ∧
    -Real.log (140567 / 200000) ≤ (88158281 / 250000000) := by
  have h := checkLog_sound (w := (59433 / 340567)) (n := 12)
    (lo := (352633123 / 1000000000)) (hi := (88158281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140567) = 1/(140567 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88158281 / 250000000) (-352633123 / 1000000000) (Real.log (140567 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24350211 / 125000000) ≤ -Real.log (100000 / 121507) ∧
    -Real.log (100000 / 121507) ≤ (194801689 / 1000000000) := by
  have h := checkLog_sound (w := (21507 / 221507)) (n := 12)
    (lo := (24350211 / 125000000)) (hi := (194801689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121507 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121507 / 100000) = 1/(100000 / 121507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24350211 / 125000000) (194801689 / 1000000000) (Real.log (121507 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121507 / 100000) = -Real.log (100000 / 121507) := by
    rw [show ((121507 / 100000) : ℝ) = ((100000 / 121507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242160737 / 1000000000) ≤ -Real.log (78493 / 100000) ∧
    -Real.log (78493 / 100000) ≤ (121080369 / 500000000) := by
  have h := checkLog_sound (w := (21507 / 178493)) (n := 12)
    (lo := (242160737 / 1000000000)) (hi := (121080369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78493) = 1/(78493 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121080369 / 500000000) (-242160737 / 1000000000) (Real.log (78493 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12191769 / 62500000) ≤ -Real.log (500000 / 607697) ∧
    -Real.log (500000 / 607697) ≤ (39013661 / 200000000) := by
  have h := checkLog_sound (w := (107697 / 1107697)) (n := 12)
    (lo := (12191769 / 62500000)) (hi := (39013661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607697 / 500000) = 1/(500000 / 607697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12191769 / 62500000) (39013661 / 200000000) (Real.log (607697 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (607697 / 500000) = -Real.log (500000 / 607697) := by
    rw [show ((607697 / 500000) : ℝ) = ((500000 / 607697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121286799 / 500000000) ≤ -Real.log (392303 / 500000) ∧
    -Real.log (392303 / 500000) ≤ (242573599 / 1000000000) := by
  have h := checkLog_sound (w := (107697 / 892303)) (n := 12)
    (lo := (121286799 / 500000000)) (hi := (242573599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392303) = 1/(392303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-242573599 / 1000000000) (-121286799 / 500000000) (Real.log (392303 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (611879841 / 1000000000) ≤ -Real.log (500000000000 / 921947186037) ∧
    -Real.log (500000000000 / 921947186037) ≤ (305939921 / 500000000) := by
  have h := checkLog_sound (w := (421947186037 / 1421947186037)) (n := 12)
    (lo := (611879841 / 1000000000)) (hi := (305939921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921947186037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921947186037 / 500000000000) = 1/(500000000000 / 921947186037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (611879841 / 1000000000) (305939921 / 500000000) (Real.log (921947186037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (921947186037 / 500000000000) = -Real.log (500000000000 / 921947186037) := by
    rw [show ((921947186037 / 500000000000) : ℝ) = ((500000000000 / 921947186037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (612814237 / 1000000000) ≤ -Real.log (62500000000 / 115351131489) ∧
    -Real.log (62500000000 / 115351131489) ≤ (306407119 / 500000000) := by
  have h := checkLog_sound (w := (52851131489 / 177851131489)) (n := 12)
    (lo := (612814237 / 1000000000)) (hi := (306407119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115351131489 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115351131489 / 62500000000) = 1/(62500000000 / 115351131489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (612814237 / 1000000000) (306407119 / 500000000) (Real.log (115351131489 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (115351131489 / 62500000000) = -Real.log (62500000000 / 115351131489) := by
    rw [show ((115351131489 / 62500000000) : ℝ) = ((62500000000 / 115351131489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17478497 / 40000000) ≤ -Real.log (12500000000 / 19349973883) ∧
    -Real.log (12500000000 / 19349973883) ≤ (218481213 / 500000000) := by
  have h := checkLog_sound (w := (6849973883 / 31849973883)) (n := 12)
    (lo := (17478497 / 40000000)) (hi := (218481213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19349973883 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19349973883 / 12500000000) = 1/(12500000000 / 19349973883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17478497 / 40000000) (218481213 / 500000000) (Real.log (19349973883 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19349973883 / 12500000000) = -Real.log (12500000000 / 19349973883) := by
    rw [show ((19349973883 / 12500000000) : ℝ) = ((12500000000 / 19349973883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (218820951 / 500000000) ≤ -Real.log (500000000000 / 774525048241) ∧
    -Real.log (500000000000 / 774525048241) ≤ (437641903 / 1000000000) := by
  have h := checkLog_sound (w := (274525048241 / 1274525048241)) (n := 12)
    (lo := (218820951 / 500000000)) (hi := (437641903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774525048241 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774525048241 / 500000000000) = 1/(500000000000 / 774525048241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (218820951 / 500000000) (437641903 / 1000000000) (Real.log (774525048241 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (774525048241 / 500000000000) = -Real.log (500000000000 / 774525048241) := by
    rw [show ((774525048241 / 500000000000) : ℝ) = ((500000000000 / 774525048241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0445
