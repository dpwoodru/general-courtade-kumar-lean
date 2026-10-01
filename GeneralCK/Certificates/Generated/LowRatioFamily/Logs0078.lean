import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4992_neg : (187327889 / 1000000000) ≤ -Real.log (100000000000 / 120602266247) ∧
    -Real.log (100000000000 / 120602266247) ≤ (18732789 / 100000000) := by
  have h := checkLog_sound (w := (20602266247 / 220602266247)) (n := 12)
    (lo := (187327889 / 1000000000)) (hi := (18732789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120602266247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120602266247 / 100000000000) = 1/(100000000000 / 120602266247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4992 : Bounds (187327889 / 1000000000) (18732789 / 100000000) (Real.log (120602266247 / 100000000000)) := by
  have h := reflection_log_4992_neg
  have he : Real.log (120602266247 / 100000000000) = -Real.log (100000000000 / 120602266247) := by
    rw [show ((120602266247 / 100000000000) : ℝ) = ((100000000000 / 120602266247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4993_neg : (18780607 / 100000000) ≤ -Real.log (500000000000 / 603299748889) ∧
    -Real.log (500000000000 / 603299748889) ≤ (187806071 / 1000000000) := by
  have h := checkLog_sound (w := (103299748889 / 1103299748889)) (n := 12)
    (lo := (18780607 / 100000000)) (hi := (187806071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603299748889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603299748889 / 500000000000) = 1/(500000000000 / 603299748889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4993 : Bounds (18780607 / 100000000) (187806071 / 1000000000) (Real.log (603299748889 / 500000000000)) := by
  have h := reflection_log_4993_neg
  have he : Real.log (603299748889 / 500000000000) = -Real.log (500000000000 / 603299748889) := by
    rw [show ((603299748889 / 500000000000) : ℝ) = ((500000000000 / 603299748889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4994_neg : (75193379 / 200000000) ≤ -Real.log (62500000000 / 91024932449) ∧
    -Real.log (62500000000 / 91024932449) ≤ (23497931 / 62500000) := by
  have h := checkLog_sound (w := (28524932449 / 153524932449)) (n := 12)
    (lo := (75193379 / 200000000)) (hi := (23497931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91024932449 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91024932449 / 62500000000) = 1/(62500000000 / 91024932449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4994 : Bounds (75193379 / 200000000) (23497931 / 62500000) (Real.log (91024932449 / 62500000000)) := by
  have h := reflection_log_4994_neg
  have he : Real.log (91024932449 / 62500000000) = -Real.log (62500000000 / 91024932449) := by
    rw [show ((91024932449 / 62500000000) : ℝ) = ((62500000000 / 91024932449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4995_neg : (7523481 / 20000000) ≤ -Real.log (500000000000 / 728350325513) ∧
    -Real.log (500000000000 / 728350325513) ≤ (376174051 / 1000000000) := by
  have h := checkLog_sound (w := (228350325513 / 1228350325513)) (n := 12)
    (lo := (7523481 / 20000000)) (hi := (376174051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728350325513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728350325513 / 500000000000) = 1/(500000000000 / 728350325513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4995 : Bounds (7523481 / 20000000) (376174051 / 1000000000) (Real.log (728350325513 / 500000000000)) := by
  have h := reflection_log_4995_neg
  have he : Real.log (728350325513 / 500000000000) = -Real.log (500000000000 / 728350325513) := by
    rw [show ((728350325513 / 500000000000) : ℝ) = ((500000000000 / 728350325513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4996_neg : (1705863 / 10000000) ≤ -Real.log (500 / 593) ∧
    -Real.log (500 / 593) ≤ (170586301 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 1093)) (n := 12)
    (lo := (1705863 / 10000000)) (hi := (170586301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 500) = 1/(500 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4996 : Bounds (1705863 / 10000000) (170586301 / 1000000000) (Real.log (593 / 500)) := by
  have h := reflection_log_4996_neg
  have he : Real.log (593 / 500) = -Real.log (500 / 593) := by
    rw [show ((593 / 500) : ℝ) = ((500 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4997_neg : (6431091 / 31250000) ≤ -Real.log (407 / 500) ∧
    -Real.log (407 / 500) ≤ (205794913 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 907)) (n := 12)
    (lo := (6431091 / 31250000)) (hi := (205794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 407) = 1/(407 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4997 : Bounds (-205794913 / 1000000000) (-6431091 / 31250000) (Real.log (407 / 500)) := by
  have h := reflection_log_4997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4998_neg : (92991 / 500000000) ≤ -Real.log (500000 / 500093) ∧
    -Real.log (500000 / 500093) ≤ (185983 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 1000093)) (n := 12)
    (lo := (92991 / 500000000)) (hi := (185983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500093 / 500000) = 1/(500000 / 500093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4998 : Bounds (92991 / 500000000) (185983 / 1000000000) (Real.log (500093 / 500000)) := by
  have h := reflection_log_4998_neg
  have he : Real.log (500093 / 500000) = -Real.log (500000 / 500093) := by
    rw [show ((500093 / 500000) : ℝ) = ((500000 / 500093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4999_neg : (186017 / 1000000000) ≤ -Real.log (499907 / 500000) ∧
    -Real.log (499907 / 500000) ≤ (93009 / 500000000) := by
  have h := checkLog_sound (w := (93 / 999907)) (n := 12)
    (lo := (186017 / 1000000000)) (hi := (93009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499907) = 1/(499907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4999 : Bounds (-93009 / 500000000) (-186017 / 1000000000) (Real.log (499907 / 500000)) := by
  have h := reflection_log_4999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5000_neg : (89330519 / 1000000000) ≤ -Real.log (500000 / 546721) ∧
    -Real.log (500000 / 546721) ≤ (2233263 / 25000000) := by
  have h := checkLog_sound (w := (46721 / 1046721)) (n := 12)
    (lo := (89330519 / 1000000000)) (hi := (2233263 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546721 / 500000) = 1/(500000 / 546721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5000 : Bounds (89330519 / 1000000000) (2233263 / 25000000) (Real.log (546721 / 500000)) := by
  have h := reflection_log_5000_neg
  have he : Real.log (546721 / 500000) = -Real.log (500000 / 546721) := by
    rw [show ((546721 / 500000) : ℝ) = ((500000 / 546721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5001_neg : (24525067 / 250000000) ≤ -Real.log (453279 / 500000) ∧
    -Real.log (453279 / 500000) ≤ (98100269 / 1000000000) := by
  have h := checkLog_sound (w := (46721 / 953279)) (n := 12)
    (lo := (24525067 / 250000000)) (hi := (98100269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453279) = 1/(453279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5001 : Bounds (-98100269 / 1000000000) (-24525067 / 250000000) (Real.log (453279 / 500000)) := by
  have h := reflection_log_5001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5002_neg : (44773621 / 500000000) ≤ -Real.log (1000000 / 1093679) ∧
    -Real.log (1000000 / 1093679) ≤ (89547243 / 1000000000) := by
  have h := checkLog_sound (w := (93679 / 2093679)) (n := 12)
    (lo := (44773621 / 500000000)) (hi := (89547243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093679 / 1000000) = 1/(1000000 / 1093679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5002 : Bounds (44773621 / 500000000) (89547243 / 1000000000) (Real.log (1093679 / 1000000)) := by
  have h := reflection_log_5002_neg
  have he : Real.log (1093679 / 1000000) = -Real.log (1000000 / 1093679) := by
    rw [show ((1093679 / 1000000) : ℝ) = ((1000000 / 1093679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5003_neg : (98361731 / 1000000000) ≤ -Real.log (906321 / 1000000) ∧
    -Real.log (906321 / 1000000) ≤ (24590433 / 250000000) := by
  have h := checkLog_sound (w := (93679 / 1906321)) (n := 12)
    (lo := (98361731 / 1000000000)) (hi := (24590433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906321) = 1/(906321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5003 : Bounds (-24590433 / 250000000) (-98361731 / 1000000000) (Real.log (906321 / 1000000)) := by
  have h := reflection_log_5003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5004_neg : (1101811 / 125000000) ≤ -Real.log (991224244959 / 1000000000000) ∧
    -Real.log (991224244959 / 1000000000000) ≤ (8814489 / 1000000000) := by
  have h := checkLog_sound (w := (8775755041 / 1991224244959)) (n := 12)
    (lo := (1101811 / 125000000)) (hi := (8814489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991224244959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991224244959) = 1/(991224244959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5004 : Bounds (-8814489 / 1000000000) (-1101811 / 125000000) (Real.log (991224244959 / 1000000000000)) := by
  have h := reflection_log_5004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5005_neg : (8769749 / 1000000000) ≤ -Real.log (247817148159 / 250000000000) ∧
    -Real.log (247817148159 / 250000000000) ≤ (35079 / 4000000) := by
  have h := checkLog_sound (w := (2182851841 / 497817148159)) (n := 12)
    (lo := (8769749 / 1000000000)) (hi := (35079 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247817148159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247817148159) = 1/(247817148159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5005 : Bounds (-35079 / 4000000) (-8769749 / 1000000000) (Real.log (247817148159 / 250000000000)) := by
  have h := reflection_log_5005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5006_neg : (187430787 / 1000000000) ≤ -Real.log (500000000000 / 603073383059) ∧
    -Real.log (500000000000 / 603073383059) ≤ (46857697 / 250000000) := by
  have h := checkLog_sound (w := (103073383059 / 1103073383059)) (n := 12)
    (lo := (187430787 / 1000000000)) (hi := (46857697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603073383059 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603073383059 / 500000000000) = 1/(500000000000 / 603073383059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5006 : Bounds (187430787 / 1000000000) (46857697 / 250000000) (Real.log (603073383059 / 500000000000)) := by
  have h := reflection_log_5006_neg
  have he : Real.log (603073383059 / 500000000000) = -Real.log (500000000000 / 603073383059) := by
    rw [show ((603073383059 / 500000000000) : ℝ) = ((500000000000 / 603073383059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5007_neg : (187908973 / 1000000000) ≤ -Real.log (50000000000 / 60336183317) ∧
    -Real.log (50000000000 / 60336183317) ≤ (93954487 / 500000000) := by
  have h := checkLog_sound (w := (10336183317 / 110336183317)) (n := 12)
    (lo := (187908973 / 1000000000)) (hi := (93954487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60336183317 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60336183317 / 50000000000) = 1/(50000000000 / 60336183317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5007 : Bounds (187908973 / 1000000000) (93954487 / 500000000) (Real.log (60336183317 / 50000000000)) := by
  have h := reflection_log_5007_neg
  have he : Real.log (60336183317 / 50000000000) = -Real.log (50000000000 / 60336183317) := by
    rw [show ((60336183317 / 50000000000) : ℝ) = ((50000000000 / 60336183317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5008_neg : (7523481 / 20000000) ≤ -Real.log (62500000000 / 91043790689) ∧
    -Real.log (62500000000 / 91043790689) ≤ (376174051 / 1000000000) := by
  have h := checkLog_sound (w := (28543790689 / 153543790689)) (n := 12)
    (lo := (7523481 / 20000000)) (hi := (376174051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91043790689 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91043790689 / 62500000000) = 1/(62500000000 / 91043790689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5008 : Bounds (7523481 / 20000000) (376174051 / 1000000000) (Real.log (91043790689 / 62500000000)) := by
  have h := reflection_log_5008_neg
  have he : Real.log (91043790689 / 62500000000) = -Real.log (62500000000 / 91043790689) := by
    rw [show ((91043790689 / 62500000000) : ℝ) = ((62500000000 / 91043790689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5009_neg : (376381213 / 1000000000) ≤ -Real.log (250000000000 / 364250614251) ∧
    -Real.log (250000000000 / 364250614251) ≤ (188190607 / 500000000) := by
  have h := checkLog_sound (w := (114250614251 / 614250614251)) (n := 12)
    (lo := (376381213 / 1000000000)) (hi := (188190607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364250614251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364250614251 / 250000000000) = 1/(250000000000 / 364250614251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5009 : Bounds (376381213 / 1000000000) (188190607 / 500000000) (Real.log (364250614251 / 250000000000)) := by
  have h := reflection_log_5009_neg
  have he : Real.log (364250614251 / 250000000000) = -Real.log (250000000000 / 364250614251) := by
    rw [show ((364250614251 / 250000000000) : ℝ) = ((250000000000 / 364250614251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5010_neg : (85335307 / 500000000) ≤ -Real.log (10000 / 11861) ∧
    -Real.log (10000 / 11861) ≤ (34134123 / 200000000) := by
  have h := checkLog_sound (w := (1861 / 21861)) (n := 12)
    (lo := (85335307 / 500000000)) (hi := (34134123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11861 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11861 / 10000) = 1/(10000 / 11861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5010 : Bounds (85335307 / 500000000) (34134123 / 200000000) (Real.log (11861 / 10000)) := by
  have h := reflection_log_5010_neg
  have he : Real.log (11861 / 10000) = -Real.log (10000 / 11861) := by
    rw [show ((11861 / 10000) : ℝ) = ((10000 / 11861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5011_neg : (20591777 / 100000000) ≤ -Real.log (8139 / 10000) ∧
    -Real.log (8139 / 10000) ≤ (205917771 / 1000000000) := by
  have h := checkLog_sound (w := (1861 / 18139)) (n := 12)
    (lo := (20591777 / 100000000)) (hi := (205917771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8139) = 1/(8139 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5011 : Bounds (-205917771 / 1000000000) (-20591777 / 100000000) (Real.log (8139 / 10000)) := by
  have h := reflection_log_5011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5012_neg : (93041 / 500000000) ≤ -Real.log (10000000 / 10001861) ∧
    -Real.log (10000000 / 10001861) ≤ (186083 / 1000000000) := by
  have h := checkLog_sound (w := (1861 / 20001861)) (n := 12)
    (lo := (93041 / 500000000)) (hi := (186083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001861 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001861 / 10000000) = 1/(10000000 / 10001861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5012 : Bounds (93041 / 500000000) (186083 / 1000000000) (Real.log (10001861 / 10000000)) := by
  have h := reflection_log_5012_neg
  have he : Real.log (10001861 / 10000000) = -Real.log (10000000 / 10001861) := by
    rw [show ((10001861 / 10000000) : ℝ) = ((10000000 / 10001861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5013_neg : (186117 / 1000000000) ≤ -Real.log (9998139 / 10000000) ∧
    -Real.log (9998139 / 10000000) ≤ (93059 / 500000000) := by
  have h := checkLog_sound (w := (1861 / 19998139)) (n := 12)
    (lo := (186117 / 1000000000)) (hi := (93059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998139) = 1/(9998139 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5013 : Bounds (-93059 / 500000000) (-186117 / 1000000000) (Real.log (9998139 / 10000000)) := by
  have h := reflection_log_5013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5014_neg : (89377159 / 1000000000) ≤ -Real.log (1000000 / 1093493) ∧
    -Real.log (1000000 / 1093493) ≤ (2234429 / 25000000) := by
  have h := checkLog_sound (w := (93493 / 2093493)) (n := 12)
    (lo := (89377159 / 1000000000)) (hi := (2234429 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093493 / 1000000) = 1/(1000000 / 1093493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5014 : Bounds (89377159 / 1000000000) (2234429 / 25000000) (Real.log (1093493 / 1000000)) := by
  have h := reflection_log_5014_neg
  have he : Real.log (1093493 / 1000000) = -Real.log (1000000 / 1093493) := by
    rw [show ((1093493 / 1000000) : ℝ) = ((1000000 / 1093493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5015_neg : (49078263 / 500000000) ≤ -Real.log (906507 / 1000000) ∧
    -Real.log (906507 / 1000000) ≤ (98156527 / 1000000000) := by
  have h := checkLog_sound (w := (93493 / 1906507)) (n := 12)
    (lo := (49078263 / 500000000)) (hi := (98156527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906507) = 1/(906507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5015 : Bounds (-98156527 / 1000000000) (-49078263 / 500000000) (Real.log (906507 / 1000000)) := by
  have h := reflection_log_5015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5016_neg : (5599617 / 62500000) ≤ -Real.log (100000 / 109373) ∧
    -Real.log (100000 / 109373) ≤ (89593873 / 1000000000) := by
  have h := checkLog_sound (w := (9373 / 209373)) (n := 12)
    (lo := (5599617 / 62500000)) (hi := (89593873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109373 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109373 / 100000) = 1/(100000 / 109373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5016 : Bounds (5599617 / 62500000) (89593873 / 1000000000) (Real.log (109373 / 100000)) := by
  have h := reflection_log_5016_neg
  have he : Real.log (109373 / 100000) = -Real.log (100000 / 109373) := by
    rw [show ((109373 / 100000) : ℝ) = ((100000 / 109373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5017_neg : (24604501 / 250000000) ≤ -Real.log (90627 / 100000) ∧
    -Real.log (90627 / 100000) ≤ (19683601 / 200000000) := by
  have h := checkLog_sound (w := (9373 / 190627)) (n := 12)
    (lo := (24604501 / 250000000)) (hi := (19683601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90627) = 1/(90627 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5017 : Bounds (-19683601 / 200000000) (-24604501 / 250000000) (Real.log (90627 / 100000)) := by
  have h := reflection_log_5017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5018_neg : (8824131 / 1000000000) ≤ -Real.log (9912146871 / 10000000000) ∧
    -Real.log (9912146871 / 10000000000) ≤ (2206033 / 250000000) := by
  have h := checkLog_sound (w := (87853129 / 19912146871)) (n := 12)
    (lo := (8824131 / 1000000000)) (hi := (2206033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9912146871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9912146871) = 1/(9912146871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5018 : Bounds (-2206033 / 250000000) (-8824131 / 1000000000) (Real.log (9912146871 / 10000000000)) := by
  have h := reflection_log_5018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5019_neg : (8779367 / 1000000000) ≤ -Real.log (991259058951 / 1000000000000) ∧
    -Real.log (991259058951 / 1000000000000) ≤ (1097421 / 125000000) := by
  have h := checkLog_sound (w := (8740941049 / 1991259058951)) (n := 12)
    (lo := (8779367 / 1000000000)) (hi := (1097421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991259058951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991259058951) = 1/(991259058951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5019 : Bounds (-1097421 / 125000000) (-8779367 / 1000000000) (Real.log (991259058951 / 1000000000000)) := by
  have h := reflection_log_5019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5020_neg : (93766843 / 500000000) ≤ -Real.log (250000000000 / 301567720933) ∧
    -Real.log (250000000000 / 301567720933) ≤ (187533687 / 1000000000) := by
  have h := checkLog_sound (w := (51567720933 / 551567720933)) (n := 12)
    (lo := (93766843 / 500000000)) (hi := (187533687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301567720933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301567720933 / 250000000000) = 1/(250000000000 / 301567720933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5020 : Bounds (93766843 / 500000000) (187533687 / 1000000000) (Real.log (301567720933 / 250000000000)) := by
  have h := reflection_log_5020_neg
  have he : Real.log (301567720933 / 250000000000) = -Real.log (250000000000 / 301567720933) := by
    rw [show ((301567720933 / 250000000000) : ℝ) = ((250000000000 / 301567720933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5021_neg : (47002969 / 250000000) ≤ -Real.log (250000000000 / 301711962219) ∧
    -Real.log (250000000000 / 301711962219) ≤ (188011877 / 1000000000) := by
  have h := checkLog_sound (w := (51711962219 / 551711962219)) (n := 12)
    (lo := (47002969 / 250000000)) (hi := (188011877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301711962219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301711962219 / 250000000000) = 1/(250000000000 / 301711962219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5021 : Bounds (47002969 / 250000000) (188011877 / 1000000000) (Real.log (301711962219 / 250000000000)) := by
  have h := reflection_log_5021_neg
  have he : Real.log (301711962219 / 250000000000) = -Real.log (250000000000 / 301711962219) := by
    rw [show ((301711962219 / 250000000000) : ℝ) = ((250000000000 / 301711962219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5022_neg : (376381213 / 1000000000) ≤ -Real.log (500000000000 / 728501228501) ∧
    -Real.log (500000000000 / 728501228501) ≤ (188190607 / 500000000) := by
  have h := checkLog_sound (w := (228501228501 / 1228501228501)) (n := 12)
    (lo := (376381213 / 1000000000)) (hi := (188190607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728501228501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728501228501 / 500000000000) = 1/(500000000000 / 728501228501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5022 : Bounds (376381213 / 1000000000) (188190607 / 500000000) (Real.log (728501228501 / 500000000000)) := by
  have h := reflection_log_5022_neg
  have he : Real.log (728501228501 / 500000000000) = -Real.log (500000000000 / 728501228501) := by
    rw [show ((728501228501 / 500000000000) : ℝ) = ((500000000000 / 728501228501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5023_neg : (11768387 / 31250000) ≤ -Real.log (125000000000 / 182163042143) ∧
    -Real.log (125000000000 / 182163042143) ≤ (75317677 / 200000000) := by
  have h := checkLog_sound (w := (57163042143 / 307163042143)) (n := 12)
    (lo := (11768387 / 31250000)) (hi := (75317677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182163042143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182163042143 / 125000000000) = 1/(125000000000 / 182163042143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5023 : Bounds (11768387 / 31250000) (75317677 / 200000000) (Real.log (182163042143 / 125000000000)) := by
  have h := reflection_log_5023_neg
  have he : Real.log (182163042143 / 125000000000) = -Real.log (125000000000 / 182163042143) := by
    rw [show ((182163042143 / 125000000000) : ℝ) = ((125000000000 / 182163042143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5024_neg : (4268873 / 25000000) ≤ -Real.log (5000 / 5931) ∧
    -Real.log (5000 / 5931) ≤ (170754921 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 10931)) (n := 12)
    (lo := (4268873 / 25000000)) (hi := (170754921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5931 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5931 / 5000) = 1/(5000 / 5931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5024 : Bounds (4268873 / 25000000) (170754921 / 1000000000) (Real.log (5931 / 5000)) := by
  have h := reflection_log_5024_neg
  have he : Real.log (5931 / 5000) = -Real.log (5000 / 5931) := by
    rw [show ((5931 / 5000) : ℝ) = ((5000 / 5931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5025_neg : (206040643 / 1000000000) ≤ -Real.log (4069 / 5000) ∧
    -Real.log (4069 / 5000) ≤ (51510161 / 250000000) := by
  have h := checkLog_sound (w := (931 / 9069)) (n := 12)
    (lo := (206040643 / 1000000000)) (hi := (51510161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4069) = 1/(4069 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5025 : Bounds (-51510161 / 250000000) (-206040643 / 1000000000) (Real.log (4069 / 5000)) := by
  have h := reflection_log_5025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5026_neg : (93091 / 500000000) ≤ -Real.log (5000000 / 5000931) ∧
    -Real.log (5000000 / 5000931) ≤ (186183 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 10000931)) (n := 12)
    (lo := (93091 / 500000000)) (hi := (186183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000931 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000931 / 5000000) = 1/(5000000 / 5000931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5026 : Bounds (93091 / 500000000) (186183 / 1000000000) (Real.log (5000931 / 5000000)) := by
  have h := reflection_log_5026_neg
  have he : Real.log (5000931 / 5000000) = -Real.log (5000000 / 5000931) := by
    rw [show ((5000931 / 5000000) : ℝ) = ((5000000 / 5000931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5027_neg : (186217 / 1000000000) ≤ -Real.log (4999069 / 5000000) ∧
    -Real.log (4999069 / 5000000) ≤ (93109 / 500000000) := by
  have h := checkLog_sound (w := (931 / 9999069)) (n := 12)
    (lo := (186217 / 1000000000)) (hi := (93109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999069) = 1/(4999069 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5027 : Bounds (-93109 / 500000000) (-186217 / 1000000000) (Real.log (4999069 / 5000000)) := by
  have h := reflection_log_5027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5028_neg : (44711899 / 500000000) ≤ -Real.log (125000 / 136693) ∧
    -Real.log (125000 / 136693) ≤ (89423799 / 1000000000) := by
  have h := checkLog_sound (w := (11693 / 261693)) (n := 12)
    (lo := (44711899 / 500000000)) (hi := (89423799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136693 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136693 / 125000) = 1/(125000 / 136693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5028 : Bounds (44711899 / 500000000) (89423799 / 1000000000) (Real.log (136693 / 125000)) := by
  have h := reflection_log_5028_neg
  have he : Real.log (136693 / 125000) = -Real.log (125000 / 136693) := by
    rw [show ((136693 / 125000) : ℝ) = ((125000 / 136693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5029_neg : (24553197 / 250000000) ≤ -Real.log (113307 / 125000) ∧
    -Real.log (113307 / 125000) ≤ (98212789 / 1000000000) := by
  have h := checkLog_sound (w := (11693 / 238307)) (n := 12)
    (lo := (24553197 / 250000000)) (hi := (98212789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113307) = 1/(113307 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5029 : Bounds (-98212789 / 1000000000) (-24553197 / 250000000) (Real.log (113307 / 125000)) := by
  have h := reflection_log_5029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5030_neg : (89640501 / 1000000000) ≤ -Real.log (1000000 / 1093781) ∧
    -Real.log (1000000 / 1093781) ≤ (44820251 / 500000000) := by
  have h := checkLog_sound (w := (93781 / 2093781)) (n := 12)
    (lo := (89640501 / 1000000000)) (hi := (44820251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093781 / 1000000) = 1/(1000000 / 1093781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5030 : Bounds (89640501 / 1000000000) (44820251 / 500000000) (Real.log (1093781 / 1000000)) := by
  have h := reflection_log_5030_neg
  have he : Real.log (1093781 / 1000000) = -Real.log (1000000 / 1093781) := by
    rw [show ((1093781 / 1000000) : ℝ) = ((1000000 / 1093781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5031_neg : (2461857 / 25000000) ≤ -Real.log (906219 / 1000000) ∧
    -Real.log (906219 / 1000000) ≤ (98474281 / 1000000000) := by
  have h := checkLog_sound (w := (93781 / 1906219)) (n := 12)
    (lo := (2461857 / 25000000)) (hi := (98474281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906219) = 1/(906219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5031 : Bounds (-98474281 / 1000000000) (-2461857 / 25000000) (Real.log (906219 / 1000000)) := by
  have h := reflection_log_5031_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5032_neg : (8833779 / 1000000000) ≤ -Real.log (991205124039 / 1000000000000) ∧
    -Real.log (991205124039 / 1000000000000) ≤ (441689 / 50000000) := by
  have h := checkLog_sound (w := (8794875961 / 1991205124039)) (n := 12)
    (lo := (8833779 / 1000000000)) (hi := (441689 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991205124039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991205124039) = 1/(991205124039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5032 : Bounds (-441689 / 50000000) (-8833779 / 1000000000) (Real.log (991205124039 / 1000000000000)) := by
  have h := reflection_log_5032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5033_neg : (878899 / 100000000) ≤ -Real.log (15488273751 / 15625000000) ∧
    -Real.log (15488273751 / 15625000000) ≤ (8788991 / 1000000000) := by
  have h := checkLog_sound (w := (136726249 / 31113273751)) (n := 12)
    (lo := (878899 / 100000000)) (hi := (8788991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15488273751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15488273751) = 1/(15488273751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5033 : Bounds (-8788991 / 1000000000) (-878899 / 100000000) (Real.log (15488273751 / 15625000000)) := by
  have h := reflection_log_5033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5034_neg : (93818293 / 500000000) ≤ -Real.log (62500000000 / 75399688457) ∧
    -Real.log (62500000000 / 75399688457) ≤ (187636587 / 1000000000) := by
  have h := checkLog_sound (w := (12899688457 / 137899688457)) (n := 12)
    (lo := (93818293 / 500000000)) (hi := (187636587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75399688457 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75399688457 / 62500000000) = 1/(62500000000 / 75399688457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5034 : Bounds (93818293 / 500000000) (187636587 / 1000000000) (Real.log (75399688457 / 62500000000)) := by
  have h := reflection_log_5034_neg
  have he : Real.log (75399688457 / 62500000000) = -Real.log (62500000000 / 75399688457) := by
    rw [show ((75399688457 / 62500000000) : ℝ) = ((62500000000 / 75399688457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5035_neg : (188114781 / 1000000000) ≤ -Real.log (100000000000 / 120697204539) ∧
    -Real.log (100000000000 / 120697204539) ≤ (94057391 / 500000000) := by
  have h := checkLog_sound (w := (20697204539 / 220697204539)) (n := 12)
    (lo := (188114781 / 1000000000)) (hi := (94057391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120697204539 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120697204539 / 100000000000) = 1/(100000000000 / 120697204539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5035 : Bounds (188114781 / 1000000000) (94057391 / 500000000) (Real.log (120697204539 / 100000000000)) := by
  have h := reflection_log_5035_neg
  have he : Real.log (120697204539 / 100000000000) = -Real.log (100000000000 / 120697204539) := by
    rw [show ((120697204539 / 100000000000) : ℝ) = ((100000000000 / 120697204539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5036_neg : (11768387 / 31250000) ≤ -Real.log (500000000000 / 728652168571) ∧
    -Real.log (500000000000 / 728652168571) ≤ (75317677 / 200000000) := by
  have h := checkLog_sound (w := (228652168571 / 1228652168571)) (n := 12)
    (lo := (11768387 / 31250000)) (hi := (75317677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728652168571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728652168571 / 500000000000) = 1/(500000000000 / 728652168571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5036 : Bounds (11768387 / 31250000) (75317677 / 200000000) (Real.log (728652168571 / 500000000000)) := by
  have h := reflection_log_5036_neg
  have he : Real.log (728652168571 / 500000000000) = -Real.log (500000000000 / 728652168571) := by
    rw [show ((728652168571 / 500000000000) : ℝ) = ((500000000000 / 728652168571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5037_neg : (376795563 / 1000000000) ≤ -Real.log (500000000000 / 728803145737) ∧
    -Real.log (500000000000 / 728803145737) ≤ (94198891 / 250000000) := by
  have h := checkLog_sound (w := (228803145737 / 1228803145737)) (n := 12)
    (lo := (376795563 / 1000000000)) (hi := (94198891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728803145737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728803145737 / 500000000000) = 1/(500000000000 / 728803145737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5037 : Bounds (376795563 / 1000000000) (94198891 / 250000000) (Real.log (728803145737 / 500000000000)) := by
  have h := reflection_log_5037_neg
  have he : Real.log (728803145737 / 500000000000) = -Real.log (500000000000 / 728803145737) := by
    rw [show ((728803145737 / 500000000000) : ℝ) = ((500000000000 / 728803145737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5038_neg : (170839219 / 1000000000) ≤ -Real.log (10000 / 11863) ∧
    -Real.log (10000 / 11863) ≤ (8541961 / 50000000) := by
  have h := checkLog_sound (w := (1863 / 21863)) (n := 12)
    (lo := (170839219 / 1000000000)) (hi := (8541961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11863 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11863 / 10000) = 1/(10000 / 11863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5038 : Bounds (170839219 / 1000000000) (8541961 / 50000000) (Real.log (11863 / 10000)) := by
  have h := reflection_log_5038_neg
  have he : Real.log (11863 / 10000) = -Real.log (10000 / 11863) := by
    rw [show ((11863 / 10000) : ℝ) = ((10000 / 11863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5039_neg : (206163531 / 1000000000) ≤ -Real.log (8137 / 10000) ∧
    -Real.log (8137 / 10000) ≤ (51540883 / 250000000) := by
  have h := checkLog_sound (w := (1863 / 18137)) (n := 12)
    (lo := (206163531 / 1000000000)) (hi := (51540883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8137) = 1/(8137 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5039 : Bounds (-51540883 / 250000000) (-206163531 / 1000000000) (Real.log (8137 / 10000)) := by
  have h := reflection_log_5039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5040_neg : (93141 / 500000000) ≤ -Real.log (10000000 / 10001863) ∧
    -Real.log (10000000 / 10001863) ≤ (186283 / 1000000000) := by
  have h := checkLog_sound (w := (1863 / 20001863)) (n := 12)
    (lo := (93141 / 500000000)) (hi := (186283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001863 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001863 / 10000000) = 1/(10000000 / 10001863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5040 : Bounds (93141 / 500000000) (186283 / 1000000000) (Real.log (10001863 / 10000000)) := by
  have h := reflection_log_5040_neg
  have he : Real.log (10001863 / 10000000) = -Real.log (10000000 / 10001863) := by
    rw [show ((10001863 / 10000000) : ℝ) = ((10000000 / 10001863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5041_neg : (186317 / 1000000000) ≤ -Real.log (9998137 / 10000000) ∧
    -Real.log (9998137 / 10000000) ≤ (93159 / 500000000) := by
  have h := checkLog_sound (w := (1863 / 19998137)) (n := 12)
    (lo := (186317 / 1000000000)) (hi := (93159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998137) = 1/(9998137 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5041 : Bounds (-93159 / 500000000) (-186317 / 1000000000) (Real.log (9998137 / 10000000)) := by
  have h := reflection_log_5041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5042_neg : (44735217 / 500000000) ≤ -Real.log (200000 / 218719) ∧
    -Real.log (200000 / 218719) ≤ (17894087 / 200000000) := by
  have h := checkLog_sound (w := (18719 / 418719)) (n := 12)
    (lo := (44735217 / 500000000)) (hi := (17894087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218719 / 200000) = 1/(200000 / 218719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5042 : Bounds (44735217 / 500000000) (17894087 / 200000000) (Real.log (218719 / 200000)) := by
  have h := reflection_log_5042_neg
  have he : Real.log (218719 / 200000) = -Real.log (200000 / 218719) := by
    rw [show ((218719 / 200000) : ℝ) = ((200000 / 218719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5043_neg : (24567263 / 250000000) ≤ -Real.log (181281 / 200000) ∧
    -Real.log (181281 / 200000) ≤ (98269053 / 1000000000) := by
  have h := checkLog_sound (w := (18719 / 381281)) (n := 12)
    (lo := (24567263 / 250000000)) (hi := (98269053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181281) = 1/(181281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5043 : Bounds (-98269053 / 1000000000) (-24567263 / 250000000) (Real.log (181281 / 200000)) := by
  have h := reflection_log_5043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5044_neg : (89687127 / 1000000000) ≤ -Real.log (125000 / 136729) ∧
    -Real.log (125000 / 136729) ≤ (11210891 / 125000000) := by
  have h := checkLog_sound (w := (11729 / 261729)) (n := 12)
    (lo := (89687127 / 1000000000)) (hi := (11210891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136729 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136729 / 125000) = 1/(125000 / 136729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5044 : Bounds (89687127 / 1000000000) (11210891 / 125000000) (Real.log (136729 / 125000)) := by
  have h := reflection_log_5044_neg
  have he : Real.log (136729 / 125000) = -Real.log (125000 / 136729) := by
    rw [show ((136729 / 125000) : ℝ) = ((125000 / 136729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5045_neg : (98530559 / 1000000000) ≤ -Real.log (113271 / 125000) ∧
    -Real.log (113271 / 125000) ≤ (76977 / 781250) := by
  have h := checkLog_sound (w := (11729 / 238271)) (n := 12)
    (lo := (98530559 / 1000000000)) (hi := (76977 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113271) = 1/(113271 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5045 : Bounds (-76977 / 781250) (-98530559 / 1000000000) (Real.log (113271 / 125000)) := by
  have h := reflection_log_5045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5046_neg : (1105429 / 125000000) ≤ -Real.log (15487430559 / 15625000000) ∧
    -Real.log (15487430559 / 15625000000) ≤ (8843433 / 1000000000) := by
  have h := checkLog_sound (w := (137569441 / 31112430559)) (n := 12)
    (lo := (1105429 / 125000000)) (hi := (8843433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15487430559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15487430559) = 1/(15487430559 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5046 : Bounds (-8843433 / 1000000000) (-1105429 / 125000000) (Real.log (15487430559 / 15625000000)) := by
  have h := reflection_log_5046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5047_neg : (4399309 / 500000000) ≤ -Real.log (39649599039 / 40000000000) ∧
    -Real.log (39649599039 / 40000000000) ≤ (8798619 / 1000000000) := by
  have h := checkLog_sound (w := (350400961 / 79649599039)) (n := 12)
    (lo := (4399309 / 500000000)) (hi := (8798619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39649599039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39649599039) = 1/(39649599039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5047 : Bounds (-8798619 / 1000000000) (-4399309 / 500000000) (Real.log (39649599039 / 40000000000)) := by
  have h := reflection_log_5047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5048_neg : (187739487 / 1000000000) ≤ -Real.log (50000000000 / 60325958043) ∧
    -Real.log (50000000000 / 60325958043) ≤ (5866859 / 31250000) := by
  have h := checkLog_sound (w := (10325958043 / 110325958043)) (n := 12)
    (lo := (187739487 / 1000000000)) (hi := (5866859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60325958043 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60325958043 / 50000000000) = 1/(50000000000 / 60325958043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5048 : Bounds (187739487 / 1000000000) (5866859 / 31250000) (Real.log (60325958043 / 50000000000)) := by
  have h := reflection_log_5048_neg
  have he : Real.log (60325958043 / 50000000000) = -Real.log (50000000000 / 60325958043) := by
    rw [show ((60325958043 / 50000000000) : ℝ) = ((50000000000 / 60325958043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5049_neg : (94108843 / 500000000) ≤ -Real.log (500000000000 / 603548127941) ∧
    -Real.log (500000000000 / 603548127941) ≤ (188217687 / 1000000000) := by
  have h := checkLog_sound (w := (103548127941 / 1103548127941)) (n := 12)
    (lo := (94108843 / 500000000)) (hi := (188217687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603548127941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603548127941 / 500000000000) = 1/(500000000000 / 603548127941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5049 : Bounds (94108843 / 500000000) (188217687 / 1000000000) (Real.log (603548127941 / 500000000000)) := by
  have h := reflection_log_5049_neg
  have he : Real.log (603548127941 / 500000000000) = -Real.log (500000000000 / 603548127941) := by
    rw [show ((603548127941 / 500000000000) : ℝ) = ((500000000000 / 603548127941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5050_neg : (376795563 / 1000000000) ≤ -Real.log (62500000000 / 91100393217) ∧
    -Real.log (62500000000 / 91100393217) ≤ (94198891 / 250000000) := by
  have h := checkLog_sound (w := (28600393217 / 153600393217)) (n := 12)
    (lo := (376795563 / 1000000000)) (hi := (94198891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91100393217 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91100393217 / 62500000000) = 1/(62500000000 / 91100393217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5050 : Bounds (376795563 / 1000000000) (94198891 / 250000000) (Real.log (91100393217 / 62500000000)) := by
  have h := reflection_log_5050_neg
  have he : Real.log (91100393217 / 62500000000) = -Real.log (62500000000 / 91100393217) := by
    rw [show ((91100393217 / 62500000000) : ℝ) = ((62500000000 / 91100393217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5051_neg : (1508011 / 4000000) ≤ -Real.log (50000000000 / 72895416001) ∧
    -Real.log (50000000000 / 72895416001) ≤ (377002751 / 1000000000) := by
  have h := checkLog_sound (w := (22895416001 / 122895416001)) (n := 12)
    (lo := (1508011 / 4000000)) (hi := (377002751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72895416001 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72895416001 / 50000000000) = 1/(50000000000 / 72895416001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5051 : Bounds (1508011 / 4000000) (377002751 / 1000000000) (Real.log (72895416001 / 50000000000)) := by
  have h := reflection_log_5051_neg
  have he : Real.log (72895416001 / 50000000000) = -Real.log (50000000000 / 72895416001) := by
    rw [show ((72895416001 / 50000000000) : ℝ) = ((50000000000 / 72895416001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5052_neg : (170923511 / 1000000000) ≤ -Real.log (1250 / 1483) ∧
    -Real.log (1250 / 1483) ≤ (21365439 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2733)) (n := 12)
    (lo := (170923511 / 1000000000)) (hi := (21365439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483 / 1250) = 1/(1250 / 1483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5052 : Bounds (170923511 / 1000000000) (21365439 / 125000000) (Real.log (1483 / 1250)) := by
  have h := reflection_log_5052_neg
  have he : Real.log (1483 / 1250) = -Real.log (1250 / 1483) := by
    rw [show ((1483 / 1250) : ℝ) = ((1250 / 1483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5053_neg : (103143217 / 500000000) ≤ -Real.log (1017 / 1250) ∧
    -Real.log (1017 / 1250) ≤ (41257287 / 200000000) := by
  have h := checkLog_sound (w := (233 / 2267)) (n := 12)
    (lo := (103143217 / 500000000)) (hi := (41257287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1017) = 1/(1017 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5053 : Bounds (-41257287 / 200000000) (-103143217 / 500000000) (Real.log (1017 / 1250)) := by
  have h := reflection_log_5053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5054_neg : (93191 / 500000000) ≤ -Real.log (1250000 / 1250233) ∧
    -Real.log (1250000 / 1250233) ≤ (186383 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2500233)) (n := 12)
    (lo := (93191 / 500000000)) (hi := (186383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250233 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250233 / 1250000) = 1/(1250000 / 1250233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5054 : Bounds (93191 / 500000000) (186383 / 1000000000) (Real.log (1250233 / 1250000)) := by
  have h := reflection_log_5054_neg
  have he : Real.log (1250233 / 1250000) = -Real.log (1250000 / 1250233) := by
    rw [show ((1250233 / 1250000) : ℝ) = ((1250000 / 1250233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5055_neg : (186417 / 1000000000) ≤ -Real.log (1249767 / 1250000) ∧
    -Real.log (1249767 / 1250000) ≤ (93209 / 500000000) := by
  have h := checkLog_sound (w := (233 / 2499767)) (n := 12)
    (lo := (186417 / 1000000000)) (hi := (93209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249767) = 1/(1249767 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5055 : Bounds (-93209 / 500000000) (-186417 / 1000000000) (Real.log (1249767 / 1250000)) := by
  have h := reflection_log_5055_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
