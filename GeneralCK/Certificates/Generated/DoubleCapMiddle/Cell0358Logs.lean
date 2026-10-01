import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0358
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

theorem reflection_log_1_neg : (210248263 / 1000000000) ≤ -Real.log (2560 / 3159) ∧
    -Real.log (2560 / 3159) ≤ (26281033 / 125000000) := by
  have h := checkLog_sound (w := (599 / 5719)) (n := 12)
    (lo := (210248263 / 1000000000)) (hi := (26281033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3159 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3159 / 2560) = 1/(2560 / 3159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (210248263 / 1000000000) (26281033 / 125000000) (Real.log (3159 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3159 / 2560) = -Real.log (2560 / 3159) := by
    rw [show ((3159 / 2560) : ℝ) = ((2560 / 3159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (266552711 / 1000000000) ≤ -Real.log (1961 / 2560) ∧
    -Real.log (1961 / 2560) ≤ (33319089 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4521)) (n := 12)
    (lo := (266552711 / 1000000000)) (hi := (33319089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1961) = 1/(1961 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33319089 / 125000000) (-266552711 / 1000000000) (Real.log (1961 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (105005409 / 500000000) ≤ -Real.log (10240 / 12633) ∧
    -Real.log (10240 / 12633) ≤ (210010819 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 22873)) (n := 12)
    (lo := (105005409 / 500000000)) (hi := (210010819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12633 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12633 / 10240) = 1/(10240 / 12633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (105005409 / 500000000) (210010819 / 1000000000) (Real.log (12633 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12633 / 10240) = -Real.log (10240 / 12633) := by
    rw [show ((12633 / 10240) : ℝ) = ((10240 / 12633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133085163 / 500000000) ≤ -Real.log (7847 / 10240) ∧
    -Real.log (7847 / 10240) ≤ (266170327 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 18087)) (n := 12)
    (lo := (133085163 / 500000000)) (hi := (266170327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7847) = 1/(7847 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266170327 / 1000000000) (-133085163 / 500000000) (Real.log (7847 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191939821 / 500000000) ≤ -Real.log (1280 / 1879) ∧
    -Real.log (1280 / 1879) ≤ (383879643 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 3159)) (n := 12)
    (lo := (191939821 / 500000000)) (hi := (383879643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1879 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1879 / 1280) = 1/(1280 / 1879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191939821 / 500000000) (383879643 / 1000000000) (Real.log (1879 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1879 / 1280) = -Real.log (1280 / 1879) := by
    rw [show ((1879 / 1280) : ℝ) = ((1280 / 1879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12621061 / 20000000) ≤ -Real.log (681 / 1280) ∧
    -Real.log (681 / 1280) ≤ (631053051 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 1961)) (n := 12)
    (lo := (12621061 / 20000000)) (hi := (631053051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 681) = 1/(681 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-631053051 / 1000000000) (-12621061 / 20000000) (Real.log (681 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191740207 / 500000000) ≤ -Real.log (5120 / 7513) ∧
    -Real.log (5120 / 7513) ≤ (76696083 / 200000000) := by
  have h := checkLog_sound (w := (2393 / 12633)) (n := 12)
    (lo := (191740207 / 500000000)) (hi := (76696083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7513 / 5120) = 1/(5120 / 7513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191740207 / 500000000) (76696083 / 200000000) (Real.log (7513 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7513 / 5120) = -Real.log (5120 / 7513) := by
    rw [show ((7513 / 5120) : ℝ) = ((5120 / 7513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (125990467 / 200000000) ≤ -Real.log (2727 / 5120) ∧
    -Real.log (2727 / 5120) ≤ (39372021 / 62500000) := by
  have h := checkLog_sound (w := (2393 / 7847)) (n := 12)
    (lo := (125990467 / 200000000)) (hi := (39372021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2727) = 1/(2727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-39372021 / 62500000) (-125990467 / 200000000) (Real.log (2727 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (288036509 / 1000000000) ≤ -Real.log (500000 / 666903) ∧
    -Real.log (500000 / 666903) ≤ (28803651 / 100000000) := by
  have h := checkLog_sound (w := (166903 / 1166903)) (n := 12)
    (lo := (288036509 / 1000000000)) (hi := (28803651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666903 / 500000) = 1/(500000 / 666903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (288036509 / 1000000000) (28803651 / 100000000) (Real.log (666903 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (666903 / 500000) = -Real.log (500000 / 666903) := by
    rw [show ((666903 / 500000) : ℝ) = ((500000 / 666903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (406174359 / 1000000000) ≤ -Real.log (333097 / 500000) ∧
    -Real.log (333097 / 500000) ≤ (10154359 / 25000000) := by
  have h := checkLog_sound (w := (166903 / 833097)) (n := 12)
    (lo := (406174359 / 1000000000)) (hi := (10154359 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333097) = 1/(333097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10154359 / 25000000) (-406174359 / 1000000000) (Real.log (333097 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (288358093 / 1000000000) ≤ -Real.log (200000 / 266847) ∧
    -Real.log (200000 / 266847) ≤ (144179047 / 500000000) := by
  have h := checkLog_sound (w := (66847 / 466847)) (n := 12)
    (lo := (288358093 / 1000000000)) (hi := (144179047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266847 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266847 / 200000) = 1/(200000 / 266847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (288358093 / 1000000000) (144179047 / 500000000) (Real.log (266847 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (266847 / 200000) = -Real.log (200000 / 266847) := by
    rw [show ((266847 / 200000) : ℝ) = ((200000 / 266847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (406818523 / 1000000000) ≤ -Real.log (133153 / 200000) ∧
    -Real.log (133153 / 200000) ≤ (101704631 / 250000000) := by
  have h := checkLog_sound (w := (66847 / 333153)) (n := 12)
    (lo := (406818523 / 1000000000)) (hi := (101704631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133153) = 1/(133153 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-101704631 / 250000000) (-406818523 / 1000000000) (Real.log (133153 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10898389 / 50000000) ≤ -Real.log (1000000 / 1243547) ∧
    -Real.log (1000000 / 1243547) ≤ (217967781 / 1000000000) := by
  have h := checkLog_sound (w := (243547 / 2243547)) (n := 12)
    (lo := (10898389 / 50000000)) (hi := (217967781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243547 / 1000000) = 1/(1000000 / 1243547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10898389 / 50000000) (217967781 / 1000000000) (Real.log (1243547 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1243547 / 1000000) = -Real.log (1000000 / 1243547) := by
    rw [show ((1243547 / 1000000) : ℝ) = ((1000000 / 1243547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2232919 / 8000000) ≤ -Real.log (756453 / 1000000) ∧
    -Real.log (756453 / 1000000) ≤ (69778719 / 250000000) := by
  have h := checkLog_sound (w := (243547 / 1756453)) (n := 12)
    (lo := (2232919 / 8000000)) (hi := (69778719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756453) = 1/(756453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-69778719 / 250000000) (-2232919 / 8000000) (Real.log (756453 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (109117763 / 500000000) ≤ -Real.log (25000 / 31097) ∧
    -Real.log (25000 / 31097) ≤ (218235527 / 1000000000) := by
  have h := checkLog_sound (w := (6097 / 56097)) (n := 12)
    (lo := (109117763 / 500000000)) (hi := (218235527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31097 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31097 / 25000) = 1/(25000 / 31097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (109117763 / 500000000) (218235527 / 1000000000) (Real.log (31097 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (31097 / 25000) = -Real.log (25000 / 31097) := by
    rw [show ((31097 / 25000) : ℝ) = ((25000 / 31097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55911037 / 200000000) ≤ -Real.log (18903 / 25000) ∧
    -Real.log (18903 / 25000) ≤ (139777593 / 500000000) := by
  have h := checkLog_sound (w := (6097 / 43903)) (n := 12)
    (lo := (55911037 / 200000000)) (hi := (139777593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18903) = 1/(18903 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139777593 / 500000000) (-55911037 / 200000000) (Real.log (18903 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173552717 / 250000000) ≤ -Real.log (125000000000 / 250266063639) ∧
    -Real.log (125000000000 / 250266063639) ≤ (69421087 / 100000000) := by
  have h := checkLog_sound (w := (266063639 / 500266063639)) (n := 12)
    (lo := (132961 / 125000000)) (hi := (1063689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250266063639 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250266063639 / 250000000000) = 1/(125000000000 / 250266063639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173552717 / 250000000) (69421087 / 100000000) (Real.log (250266063639 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (250266063639 / 125000000000) = -Real.log (125000000000 / 250266063639) := by
    rw [show ((250266063639 / 125000000000) : ℝ) = ((125000000000 / 250266063639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (86897077 / 125000000) ≤ -Real.log (500000000000 / 1002031497601) ∧
    -Real.log (500000000000 / 1002031497601) ≤ (347588309 / 500000000) := by
  have h := checkLog_sound (w := (2031497601 / 2002031497601)) (n := 12)
    (lo := (507359 / 250000000)) (hi := (2029437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002031497601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002031497601 / 1000000000000) = 1/(500000000000 / 1002031497601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (86897077 / 125000000) (347588309 / 500000000) (Real.log (1002031497601 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1002031497601 / 500000000000) = -Real.log (500000000000 / 1002031497601) := by
    rw [show ((1002031497601 / 500000000000) : ℝ) = ((500000000000 / 1002031497601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (99416531 / 200000000) ≤ -Real.log (500000000000 / 821959196407) ∧
    -Real.log (500000000000 / 821959196407) ≤ (15533833 / 31250000) := by
  have h := checkLog_sound (w := (321959196407 / 1321959196407)) (n := 12)
    (lo := (99416531 / 200000000)) (hi := (15533833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821959196407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821959196407 / 500000000000) = 1/(500000000000 / 821959196407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (99416531 / 200000000) (15533833 / 31250000) (Real.log (821959196407 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (821959196407 / 500000000000) = -Real.log (500000000000 / 821959196407) := by
    rw [show ((821959196407 / 500000000000) : ℝ) = ((500000000000 / 821959196407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (497790711 / 1000000000) ≤ -Real.log (250000000000 / 411270697773) ∧
    -Real.log (250000000000 / 411270697773) ≤ (62223839 / 125000000) := by
  have h := checkLog_sound (w := (161270697773 / 661270697773)) (n := 12)
    (lo := (497790711 / 1000000000)) (hi := (62223839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411270697773 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411270697773 / 250000000000) = 1/(250000000000 / 411270697773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (497790711 / 1000000000) (62223839 / 125000000) (Real.log (411270697773 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (411270697773 / 250000000000) = -Real.log (250000000000 / 411270697773) := by
    rw [show ((411270697773 / 250000000000) : ℝ) = ((250000000000 / 411270697773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0358
