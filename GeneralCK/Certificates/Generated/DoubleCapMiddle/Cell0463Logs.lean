import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0463
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

theorem reflection_log_1_neg : (11562719 / 62500000) ≤ -Real.log (10240 / 12321) ∧
    -Real.log (10240 / 12321) ≤ (37000701 / 200000000) := by
  have h := checkLog_sound (w := (2081 / 22561)) (n := 12)
    (lo := (11562719 / 62500000)) (hi := (37000701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12321 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12321 / 10240) = 1/(10240 / 12321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11562719 / 62500000) (37000701 / 200000000) (Real.log (12321 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12321 / 10240) = -Real.log (10240 / 12321) := by
    rw [show ((12321 / 10240) : ℝ) = ((10240 / 12321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227180007 / 1000000000) ≤ -Real.log (8159 / 10240) ∧
    -Real.log (8159 / 10240) ≤ (28397501 / 125000000) := by
  have h := checkLog_sound (w := (2081 / 18399)) (n := 12)
    (lo := (227180007 / 1000000000)) (hi := (28397501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8159) = 1/(8159 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28397501 / 125000000) (-227180007 / 1000000000) (Real.log (8159 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184759987 / 1000000000) ≤ -Real.log (5120 / 6159) ∧
    -Real.log (5120 / 6159) ≤ (46189997 / 250000000) := by
  have h := checkLog_sound (w := (1039 / 11279)) (n := 12)
    (lo := (184759987 / 1000000000)) (hi := (46189997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6159 / 5120) = 1/(5120 / 6159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184759987 / 1000000000) (46189997 / 250000000) (Real.log (6159 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6159 / 5120) = -Real.log (5120 / 6159) := by
    rw [show ((6159 / 5120) : ℝ) = ((5120 / 6159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113406191 / 500000000) ≤ -Real.log (4081 / 5120) ∧
    -Real.log (4081 / 5120) ≤ (226812383 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 9201)) (n := 12)
    (lo := (113406191 / 500000000)) (hi := (226812383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4081) = 1/(4081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-226812383 / 1000000000) (-113406191 / 500000000) (Real.log (4081 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (170532733 / 500000000) ≤ -Real.log (5120 / 7201) ∧
    -Real.log (5120 / 7201) ≤ (341065467 / 1000000000) := by
  have h := checkLog_sound (w := (2081 / 12321)) (n := 12)
    (lo := (170532733 / 500000000)) (hi := (341065467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7201 / 5120) = 1/(5120 / 7201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (170532733 / 500000000) (341065467 / 1000000000) (Real.log (7201 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7201 / 5120) = -Real.log (5120 / 7201) := by
    rw [show ((7201 / 5120) : ℝ) = ((5120 / 7201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (20865037 / 40000000) ≤ -Real.log (3039 / 5120) ∧
    -Real.log (3039 / 5120) ≤ (260812963 / 500000000) := by
  have h := checkLog_sound (w := (2081 / 8159)) (n := 12)
    (lo := (20865037 / 40000000)) (hi := (260812963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3039) = 1/(3039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260812963 / 500000000) (-20865037 / 40000000) (Real.log (3039 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34064877 / 100000000) ≤ -Real.log (2560 / 3599) ∧
    -Real.log (2560 / 3599) ≤ (340648771 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 6159)) (n := 12)
    (lo := (34064877 / 100000000)) (hi := (340648771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3599 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3599 / 2560) = 1/(2560 / 3599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34064877 / 100000000) (340648771 / 1000000000) (Real.log (3599 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3599 / 2560) = -Real.log (2560 / 3599) := by
    rw [show ((3599 / 2560) : ℝ) = ((2560 / 3599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104127849 / 200000000) ≤ -Real.log (1521 / 2560) ∧
    -Real.log (1521 / 2560) ≤ (260319623 / 500000000) := by
  have h := checkLog_sound (w := (1039 / 4081)) (n := 12)
    (lo := (104127849 / 200000000)) (hi := (260319623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1521) = 1/(1521 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260319623 / 500000000) (-104127849 / 200000000) (Real.log (1521 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253946627 / 1000000000) ≤ -Real.log (1000000 / 1289103) ∧
    -Real.log (1000000 / 1289103) ≤ (63486657 / 250000000) := by
  have h := checkLog_sound (w := (289103 / 2289103)) (n := 12)
    (lo := (253946627 / 1000000000)) (hi := (63486657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289103 / 1000000) = 1/(1000000 / 1289103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253946627 / 1000000000) (63486657 / 250000000) (Real.log (1289103 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289103 / 1000000) = -Real.log (1000000 / 1289103) := by
    rw [show ((1289103 / 1000000) : ℝ) = ((1000000 / 1289103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170613863 / 500000000) ≤ -Real.log (710897 / 1000000) ∧
    -Real.log (710897 / 1000000) ≤ (341227727 / 1000000000) := by
  have h := checkLog_sound (w := (289103 / 1710897)) (n := 12)
    (lo := (170613863 / 500000000)) (hi := (341227727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710897) = 1/(710897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-341227727 / 1000000000) (-170613863 / 500000000) (Real.log (710897 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (254276259 / 1000000000) ≤ -Real.log (125000 / 161191) ∧
    -Real.log (125000 / 161191) ≤ (12713813 / 50000000) := by
  have h := checkLog_sound (w := (36191 / 286191)) (n := 12)
    (lo := (254276259 / 1000000000)) (hi := (12713813 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161191 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161191 / 125000) = 1/(125000 / 161191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (254276259 / 1000000000) (12713813 / 50000000) (Real.log (161191 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161191 / 125000) = -Real.log (125000 / 161191) := by
    rw [show ((161191 / 125000) : ℝ) = ((125000 / 161191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (341825741 / 1000000000) ≤ -Real.log (88809 / 125000) ∧
    -Real.log (88809 / 125000) ≤ (170912871 / 500000000) := by
  have h := checkLog_sound (w := (36191 / 213809)) (n := 12)
    (lo := (341825741 / 1000000000)) (hi := (170912871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88809) = 1/(88809 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170912871 / 500000000) (-341825741 / 1000000000) (Real.log (88809 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190016871 / 1000000000) ≤ -Real.log (100000 / 120927) ∧
    -Real.log (100000 / 120927) ≤ (23752109 / 125000000) := by
  have h := checkLog_sound (w := (20927 / 220927)) (n := 12)
    (lo := (190016871 / 1000000000)) (hi := (23752109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120927 / 100000) = 1/(100000 / 120927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190016871 / 1000000000) (23752109 / 125000000) (Real.log (120927 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (120927 / 100000) = -Real.log (100000 / 120927) := by
    rw [show ((120927 / 100000) : ℝ) = ((100000 / 120927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (234798709 / 1000000000) ≤ -Real.log (79073 / 100000) ∧
    -Real.log (79073 / 100000) ≤ (23479871 / 100000000) := by
  have h := checkLog_sound (w := (20927 / 179073)) (n := 12)
    (lo := (234798709 / 1000000000)) (hi := (23479871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 79073) = 1/(79073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-23479871 / 100000000) (-234798709 / 1000000000) (Real.log (79073 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23785389 / 125000000) ≤ -Real.log (125000 / 151199) ∧
    -Real.log (125000 / 151199) ≤ (190283113 / 1000000000) := by
  have h := checkLog_sound (w := (26199 / 276199)) (n := 12)
    (lo := (23785389 / 125000000)) (hi := (190283113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151199 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151199 / 125000) = 1/(125000 / 151199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23785389 / 125000000) (190283113 / 1000000000) (Real.log (151199 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (151199 / 125000) = -Real.log (125000 / 151199) := by
    rw [show ((151199 / 125000) : ℝ) = ((125000 / 151199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (235206011 / 1000000000) ≤ -Real.log (98801 / 125000) ∧
    -Real.log (98801 / 125000) ≤ (58801503 / 250000000) := by
  have h := checkLog_sound (w := (26199 / 223801)) (n := 12)
    (lo := (235206011 / 1000000000)) (hi := (58801503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98801) = 1/(98801 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58801503 / 250000000) (-235206011 / 1000000000) (Real.log (98801 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (595174353 / 1000000000) ≤ -Real.log (500000000000 / 906673540611) ∧
    -Real.log (500000000000 / 906673540611) ≤ (297587177 / 500000000) := by
  have h := checkLog_sound (w := (406673540611 / 1406673540611)) (n := 12)
    (lo := (595174353 / 1000000000)) (hi := (297587177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906673540611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906673540611 / 500000000000) = 1/(500000000000 / 906673540611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (595174353 / 1000000000) (297587177 / 500000000) (Real.log (906673540611 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (906673540611 / 500000000000) = -Real.log (500000000000 / 906673540611) := by
    rw [show ((906673540611 / 500000000000) : ℝ) = ((500000000000 / 906673540611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (596102001 / 1000000000) ≤ -Real.log (50000000000 / 90751500411) ∧
    -Real.log (50000000000 / 90751500411) ≤ (298051001 / 500000000) := by
  have h := checkLog_sound (w := (40751500411 / 140751500411)) (n := 12)
    (lo := (596102001 / 1000000000)) (hi := (298051001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90751500411 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90751500411 / 50000000000) = 1/(50000000000 / 90751500411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (596102001 / 1000000000) (298051001 / 500000000) (Real.log (90751500411 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (90751500411 / 50000000000) = -Real.log (50000000000 / 90751500411) := by
    rw [show ((90751500411 / 50000000000) : ℝ) = ((50000000000 / 90751500411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (424815581 / 1000000000) ≤ -Real.log (250000000000 / 382327090157) ∧
    -Real.log (250000000000 / 382327090157) ≤ (212407791 / 500000000) := by
  have h := checkLog_sound (w := (132327090157 / 632327090157)) (n := 12)
    (lo := (424815581 / 1000000000)) (hi := (212407791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382327090157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382327090157 / 250000000000) = 1/(250000000000 / 382327090157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (424815581 / 1000000000) (212407791 / 500000000) (Real.log (382327090157 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (382327090157 / 250000000000) = -Real.log (250000000000 / 382327090157) := by
    rw [show ((382327090157 / 250000000000) : ℝ) = ((250000000000 / 382327090157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (425489123 / 1000000000) ≤ -Real.log (500000000000 / 765169380877) ∧
    -Real.log (500000000000 / 765169380877) ≤ (106372281 / 250000000) := by
  have h := checkLog_sound (w := (265169380877 / 1265169380877)) (n := 12)
    (lo := (425489123 / 1000000000)) (hi := (106372281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765169380877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765169380877 / 500000000000) = 1/(500000000000 / 765169380877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (425489123 / 1000000000) (106372281 / 250000000) (Real.log (765169380877 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (765169380877 / 500000000000) = -Real.log (500000000000 / 765169380877) := by
    rw [show ((765169380877 / 500000000000) : ℝ) = ((500000000000 / 765169380877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0463
