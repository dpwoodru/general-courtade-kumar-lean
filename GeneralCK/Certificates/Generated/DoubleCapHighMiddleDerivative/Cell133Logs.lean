import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell133
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

theorem reflection_log_1_neg : (284062247 / 1000000000) ≤ -Real.log (2560 / 3401) ∧
    -Real.log (2560 / 3401) ≤ (35507781 / 125000000) := by
  have h := checkLog_sound (w := (841 / 5961)) (n := 12)
    (lo := (284062247 / 1000000000)) (hi := (35507781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3401 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3401 / 2560) = 1/(2560 / 3401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (284062247 / 1000000000) (35507781 / 125000000) (Real.log (3401 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3401 / 2560) = -Real.log (2560 / 3401) := by
    rw [show ((3401 / 2560) : ℝ) = ((2560 / 3401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99566133 / 250000000) ≤ -Real.log (1719 / 2560) ∧
    -Real.log (1719 / 2560) ≤ (398264533 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 4279)) (n := 12)
    (lo := (99566133 / 250000000)) (hi := (398264533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1719) = 1/(1719 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-398264533 / 1000000000) (-99566133 / 250000000) (Real.log (1719 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (283621103 / 1000000000) ≤ -Real.log (5120 / 6799) ∧
    -Real.log (5120 / 6799) ≤ (17726319 / 62500000) := by
  have h := checkLog_sound (w := (1679 / 11919)) (n := 12)
    (lo := (283621103 / 1000000000)) (hi := (17726319 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6799 / 5120) = 1/(5120 / 6799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (283621103 / 1000000000) (17726319 / 62500000) (Real.log (6799 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6799 / 5120) = -Real.log (5120 / 6799) := by
    rw [show ((6799 / 5120) : ℝ) = ((5120 / 6799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (49674039 / 125000000) ≤ -Real.log (3441 / 5120) ∧
    -Real.log (3441 / 5120) ≤ (397392313 / 1000000000) := by
  have h := checkLog_sound (w := (1679 / 8561)) (n := 12)
    (lo := (49674039 / 125000000)) (hi := (397392313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3441) = 1/(3441 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-397392313 / 1000000000) (-49674039 / 125000000) (Real.log (3441 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (209425081 / 1000000000) ≤ -Real.log (1000000 / 1232969) ∧
    -Real.log (1000000 / 1232969) ≤ (104712541 / 500000000) := by
  have h := checkLog_sound (w := (232969 / 2232969)) (n := 12)
    (lo := (209425081 / 1000000000)) (hi := (104712541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232969 / 1000000) = 1/(1000000 / 1232969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (209425081 / 1000000000) (104712541 / 500000000) (Real.log (1232969 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1232969 / 1000000) = -Real.log (1000000 / 1232969) := by
    rw [show ((1232969 / 1000000) : ℝ) = ((1000000 / 1232969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (265228061 / 1000000000) ≤ -Real.log (767031 / 1000000) ∧
    -Real.log (767031 / 1000000) ≤ (132614031 / 500000000) := by
  have h := checkLog_sound (w := (232969 / 1767031)) (n := 12)
    (lo := (265228061 / 1000000000)) (hi := (132614031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767031) = 1/(767031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132614031 / 500000000) (-265228061 / 1000000000) (Real.log (767031 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8390659 / 40000000) ≤ -Real.log (100000 / 123339) ∧
    -Real.log (100000 / 123339) ≤ (52441619 / 250000000) := by
  have h := checkLog_sound (w := (23339 / 223339)) (n := 12)
    (lo := (8390659 / 40000000)) (hi := (52441619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123339 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123339 / 100000) = 1/(100000 / 123339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8390659 / 40000000) (52441619 / 250000000) (Real.log (123339 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (123339 / 100000) = -Real.log (100000 / 123339) := by
    rw [show ((123339 / 100000) : ℝ) = ((100000 / 123339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (265777081 / 1000000000) ≤ -Real.log (76661 / 100000) ∧
    -Real.log (76661 / 100000) ≤ (132888541 / 500000000) := by
  have h := checkLog_sound (w := (23339 / 176661)) (n := 12)
    (lo := (265777081 / 1000000000)) (hi := (132888541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76661) = 1/(76661 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-132888541 / 500000000) (-265777081 / 1000000000) (Real.log (76661 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77324849 / 500000000) ≤ -Real.log (1000000 / 1167249) ∧
    -Real.log (1000000 / 1167249) ≤ (154649699 / 1000000000) := by
  have h := checkLog_sound (w := (167249 / 2167249)) (n := 12)
    (lo := (77324849 / 500000000)) (hi := (154649699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167249 / 1000000) = 1/(1000000 / 1167249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77324849 / 500000000) (154649699 / 1000000000) (Real.log (1167249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1167249 / 1000000) = -Real.log (1000000 / 1167249) := by
    rw [show ((1167249 / 1000000) : ℝ) = ((1000000 / 1167249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183020601 / 1000000000) ≤ -Real.log (832751 / 1000000) ∧
    -Real.log (832751 / 1000000) ≤ (91510301 / 500000000) := by
  have h := checkLog_sound (w := (167249 / 1832751)) (n := 12)
    (lo := (183020601 / 1000000000)) (hi := (91510301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832751) = 1/(832751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91510301 / 500000000) (-183020601 / 1000000000) (Real.log (832751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154916957 / 1000000000) ≤ -Real.log (1000000 / 1167561) ∧
    -Real.log (1000000 / 1167561) ≤ (77458479 / 500000000) := by
  have h := checkLog_sound (w := (167561 / 2167561)) (n := 12)
    (lo := (154916957 / 1000000000)) (hi := (77458479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167561 / 1000000) = 1/(1000000 / 1167561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154916957 / 1000000000) (77458479 / 500000000) (Real.log (1167561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1167561 / 1000000) = -Real.log (1000000 / 1167561) := by
    rw [show ((1167561 / 1000000) : ℝ) = ((1000000 / 1167561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183395333 / 1000000000) ≤ -Real.log (832439 / 1000000) ∧
    -Real.log (832439 / 1000000) ≤ (91697667 / 500000000) := by
  have h := checkLog_sound (w := (167561 / 1832439)) (n := 12)
    (lo := (183395333 / 1000000000)) (hi := (91697667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832439) = 1/(832439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91697667 / 500000000) (-183395333 / 1000000000) (Real.log (832439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136202683 / 200000000) ≤ -Real.log (100000000000 / 197587910491) ∧
    -Real.log (100000000000 / 197587910491) ≤ (85126677 / 125000000) := by
  have h := checkLog_sound (w := (97587910491 / 297587910491)) (n := 12)
    (lo := (136202683 / 200000000)) (hi := (85126677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197587910491 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197587910491 / 100000000000) = 1/(100000000000 / 197587910491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136202683 / 200000000) (85126677 / 125000000) (Real.log (197587910491 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (197587910491 / 100000000000) = -Real.log (100000000000 / 197587910491) := by
    rw [show ((197587910491 / 100000000000) : ℝ) = ((100000000000 / 197587910491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (682326779 / 1000000000) ≤ -Real.log (500000000000 / 989237929029) ∧
    -Real.log (500000000000 / 989237929029) ≤ (34116339 / 50000000) := by
  have h := checkLog_sound (w := (489237929029 / 1489237929029)) (n := 12)
    (lo := (682326779 / 1000000000)) (hi := (34116339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989237929029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989237929029 / 500000000000) = 1/(500000000000 / 989237929029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (682326779 / 1000000000) (34116339 / 50000000) (Real.log (989237929029 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (989237929029 / 500000000000) = -Real.log (500000000000 / 989237929029) := by
    rw [show ((989237929029 / 500000000000) : ℝ) = ((500000000000 / 989237929029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (474653143 / 1000000000) ≤ -Real.log (250000000000 / 401864135869) ∧
    -Real.log (250000000000 / 401864135869) ≤ (59331643 / 125000000) := by
  have h := checkLog_sound (w := (151864135869 / 651864135869)) (n := 12)
    (lo := (474653143 / 1000000000)) (hi := (59331643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401864135869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401864135869 / 250000000000) = 1/(250000000000 / 401864135869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (474653143 / 1000000000) (59331643 / 125000000) (Real.log (401864135869 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (401864135869 / 250000000000) = -Real.log (250000000000 / 401864135869) := by
    rw [show ((401864135869 / 250000000000) : ℝ) = ((250000000000 / 401864135869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (475543557 / 1000000000) ≤ -Real.log (500000000000 / 804444241531) ∧
    -Real.log (500000000000 / 804444241531) ≤ (237771779 / 500000000) := by
  have h := checkLog_sound (w := (304444241531 / 1304444241531)) (n := 12)
    (lo := (475543557 / 1000000000)) (hi := (237771779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804444241531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804444241531 / 500000000000) = 1/(500000000000 / 804444241531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (475543557 / 1000000000) (237771779 / 500000000) (Real.log (804444241531 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (804444241531 / 500000000000) = -Real.log (500000000000 / 804444241531) := by
    rw [show ((804444241531 / 500000000000) : ℝ) = ((500000000000 / 804444241531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (337670299 / 1000000000) ≤ -Real.log (100000000000 / 140167829279) ∧
    -Real.log (100000000000 / 140167829279) ≤ (3376703 / 10000000) := by
  have h := checkLog_sound (w := (40167829279 / 240167829279)) (n := 12)
    (lo := (337670299 / 1000000000)) (hi := (3376703 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140167829279 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140167829279 / 100000000000) = 1/(100000000000 / 140167829279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (337670299 / 1000000000) (3376703 / 10000000) (Real.log (140167829279 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140167829279 / 100000000000) = -Real.log (100000000000 / 140167829279) := by
    rw [show ((140167829279 / 100000000000) : ℝ) = ((100000000000 / 140167829279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33831229 / 100000000) ≤ -Real.log (100000000000 / 140257844719) ∧
    -Real.log (100000000000 / 140257844719) ≤ (338312291 / 1000000000) := by
  have h := checkLog_sound (w := (40257844719 / 240257844719)) (n := 12)
    (lo := (33831229 / 100000000)) (hi := (338312291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140257844719 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140257844719 / 100000000000) = 1/(100000000000 / 140257844719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33831229 / 100000000) (338312291 / 1000000000) (Real.log (140257844719 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (140257844719 / 100000000000) = -Real.log (100000000000 / 140257844719) := by
    rw [show ((140257844719 / 100000000000) : ℝ) = ((100000000000 / 140257844719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (227827 / 8000000) ≤ -Real.log (971923311279 / 1000000000000) ∧
    -Real.log (971923311279 / 1000000000000) ≤ (3559797 / 125000000) := by
  have h := checkLog_sound (w := (28076688721 / 1971923311279)) (n := 12)
    (lo := (227827 / 8000000)) (hi := (3559797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971923311279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971923311279) = 1/(971923311279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3559797 / 125000000) (-227827 / 8000000) (Real.log (971923311279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14185451 / 500000000) ≤ -Real.log (972027771999 / 1000000000000) ∧
    -Real.log (972027771999 / 1000000000000) ≤ (28370903 / 1000000000) := by
  have h := checkLog_sound (w := (27972228001 / 1972027771999)) (n := 12)
    (lo := (14185451 / 500000000)) (hi := (28370903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972027771999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972027771999) = 1/(972027771999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28370903 / 1000000000) (-14185451 / 500000000) (Real.log (972027771999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell133
