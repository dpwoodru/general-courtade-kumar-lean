import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell097
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

theorem reflection_log_1_neg : (268057163 / 1000000000) ≤ -Real.log (2560 / 3347) ∧
    -Real.log (2560 / 3347) ≤ (67014291 / 250000000) := by
  have h := checkLog_sound (w := (787 / 5907)) (n := 12)
    (lo := (268057163 / 1000000000)) (hi := (67014291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3347 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3347 / 2560) = 1/(2560 / 3347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (268057163 / 1000000000) (67014291 / 250000000) (Real.log (3347 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3347 / 2560) = -Real.log (2560 / 3347) := by
    rw [show ((3347 / 2560) : ℝ) = ((2560 / 3347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (367334231 / 1000000000) ≤ -Real.log (1773 / 2560) ∧
    -Real.log (1773 / 2560) ≤ (45916779 / 125000000) := by
  have h := checkLog_sound (w := (787 / 4333)) (n := 12)
    (lo := (367334231 / 1000000000)) (hi := (45916779 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1773) = 1/(1773 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45916779 / 125000000) (-367334231 / 1000000000) (Real.log (1773 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2676089 / 10000000) ≤ -Real.log (5120 / 6691) ∧
    -Real.log (5120 / 6691) ≤ (267608901 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 11811)) (n := 12)
    (lo := (2676089 / 10000000)) (hi := (267608901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6691 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6691 / 5120) = 1/(5120 / 6691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2676089 / 10000000) (267608901 / 1000000000) (Real.log (6691 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6691 / 5120) = -Real.log (5120 / 6691) := by
    rw [show ((6691 / 5120) : ℝ) = ((5120 / 6691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73297713 / 200000000) ≤ -Real.log (3549 / 5120) ∧
    -Real.log (3549 / 5120) ≤ (183244283 / 500000000) := by
  have h := checkLog_sound (w := (1571 / 8669)) (n := 12)
    (lo := (73297713 / 200000000)) (hi := (183244283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3549) = 1/(3549 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-183244283 / 500000000) (-73297713 / 200000000) (Real.log (3549 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19708783 / 100000000) ≤ -Real.log (1000000 / 1217851) ∧
    -Real.log (1000000 / 1217851) ≤ (197087831 / 1000000000) := by
  have h := checkLog_sound (w := (217851 / 2217851)) (n := 12)
    (lo := (19708783 / 100000000)) (hi := (197087831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217851 / 1000000) = 1/(1000000 / 1217851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19708783 / 100000000) (197087831 / 1000000000) (Real.log (1217851 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1217851 / 1000000) = -Real.log (1000000 / 1217851) := by
    rw [show ((1217851 / 1000000) : ℝ) = ((1000000 / 1217851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245710019 / 1000000000) ≤ -Real.log (782149 / 1000000) ∧
    -Real.log (782149 / 1000000) ≤ (12285501 / 50000000) := by
  have h := checkLog_sound (w := (217851 / 1782149)) (n := 12)
    (lo := (245710019 / 1000000000)) (hi := (12285501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782149) = 1/(782149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12285501 / 50000000) (-245710019 / 1000000000) (Real.log (782149 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197433461 / 1000000000) ≤ -Real.log (31250 / 38071) ∧
    -Real.log (31250 / 38071) ≤ (98716731 / 500000000) := by
  have h := checkLog_sound (w := (6821 / 69321)) (n := 12)
    (lo := (197433461 / 1000000000)) (hi := (98716731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38071 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38071 / 31250) = 1/(31250 / 38071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197433461 / 1000000000) (98716731 / 500000000) (Real.log (38071 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (38071 / 31250) = -Real.log (31250 / 38071) := by
    rw [show ((38071 / 31250) : ℝ) = ((31250 / 38071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9849937 / 40000000) ≤ -Real.log (24429 / 31250) ∧
    -Real.log (24429 / 31250) ≤ (123124213 / 500000000) := by
  have h := checkLog_sound (w := (6821 / 55679)) (n := 12)
    (lo := (9849937 / 40000000)) (hi := (123124213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24429) = 1/(24429 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-123124213 / 500000000) (-9849937 / 40000000) (Real.log (24429 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36262419 / 250000000) ≤ -Real.log (1000000 / 1156097) ∧
    -Real.log (1000000 / 1156097) ≤ (145049677 / 1000000000) := by
  have h := checkLog_sound (w := (156097 / 2156097)) (n := 12)
    (lo := (36262419 / 250000000)) (hi := (145049677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156097 / 1000000) = 1/(1000000 / 1156097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36262419 / 250000000) (145049677 / 1000000000) (Real.log (1156097 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1156097 / 1000000) = -Real.log (1000000 / 1156097) := by
    rw [show ((1156097 / 1000000) : ℝ) = ((1000000 / 1156097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (169717719 / 1000000000) ≤ -Real.log (843903 / 1000000) ∧
    -Real.log (843903 / 1000000) ≤ (4242943 / 25000000) := by
  have h := checkLog_sound (w := (156097 / 1843903)) (n := 12)
    (lo := (169717719 / 1000000000)) (hi := (4242943 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843903) = 1/(843903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4242943 / 25000000) (-169717719 / 1000000000) (Real.log (843903 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18164723 / 125000000) ≤ -Real.log (1000000 / 1156407) ∧
    -Real.log (1000000 / 1156407) ≤ (29063557 / 200000000) := by
  have h := checkLog_sound (w := (156407 / 2156407)) (n := 12)
    (lo := (18164723 / 125000000)) (hi := (29063557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156407 / 1000000) = 1/(1000000 / 1156407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18164723 / 125000000) (29063557 / 200000000) (Real.log (1156407 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1156407 / 1000000) = -Real.log (1000000 / 1156407) := by
    rw [show ((1156407 / 1000000) : ℝ) = ((1000000 / 1156407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21260641 / 125000000) ≤ -Real.log (843593 / 1000000) ∧
    -Real.log (843593 / 1000000) ≤ (170085129 / 1000000000) := by
  have h := checkLog_sound (w := (156407 / 1843593)) (n := 12)
    (lo := (21260641 / 125000000)) (hi := (170085129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 843593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 843593) = 1/(843593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170085129 / 1000000000) (-21260641 / 125000000) (Real.log (843593 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (317048733 / 500000000) ≤ -Real.log (250000000000 / 471329952099) ∧
    -Real.log (250000000000 / 471329952099) ≤ (634097467 / 1000000000) := by
  have h := checkLog_sound (w := (221329952099 / 721329952099)) (n := 12)
    (lo := (317048733 / 500000000)) (hi := (634097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471329952099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471329952099 / 250000000000) = 1/(250000000000 / 471329952099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (317048733 / 500000000) (634097467 / 1000000000) (Real.log (471329952099 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (471329952099 / 250000000000) = -Real.log (250000000000 / 471329952099) := by
    rw [show ((471329952099 / 250000000000) : ℝ) = ((250000000000 / 471329952099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (127078279 / 200000000) ≤ -Real.log (500000000000 / 943880428653) ∧
    -Real.log (500000000000 / 943880428653) ≤ (158847849 / 250000000) := by
  have h := checkLog_sound (w := (443880428653 / 1443880428653)) (n := 12)
    (lo := (127078279 / 200000000)) (hi := (158847849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943880428653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943880428653 / 500000000000) = 1/(500000000000 / 943880428653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (127078279 / 200000000) (158847849 / 250000000) (Real.log (943880428653 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (943880428653 / 500000000000) = -Real.log (500000000000 / 943880428653) := by
    rw [show ((943880428653 / 500000000000) : ℝ) = ((500000000000 / 943880428653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (442797849 / 1000000000) ≤ -Real.log (125000000000 / 194632192843) ∧
    -Real.log (125000000000 / 194632192843) ≤ (8855957 / 20000000) := by
  have h := checkLog_sound (w := (69632192843 / 319632192843)) (n := 12)
    (lo := (442797849 / 1000000000)) (hi := (8855957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194632192843 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194632192843 / 125000000000) = 1/(125000000000 / 194632192843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (442797849 / 1000000000) (8855957 / 20000000) (Real.log (194632192843 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (194632192843 / 125000000000) = -Real.log (125000000000 / 194632192843) := by
    rw [show ((194632192843 / 125000000000) : ℝ) = ((125000000000 / 194632192843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (221840943 / 500000000) ≤ -Real.log (500000000000 / 779217323673) ∧
    -Real.log (500000000000 / 779217323673) ≤ (443681887 / 1000000000) := by
  have h := checkLog_sound (w := (279217323673 / 1279217323673)) (n := 12)
    (lo := (221840943 / 500000000)) (hi := (443681887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779217323673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779217323673 / 500000000000) = 1/(500000000000 / 779217323673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (221840943 / 500000000) (443681887 / 1000000000) (Real.log (779217323673 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (779217323673 / 500000000000) = -Real.log (500000000000 / 779217323673) := by
    rw [show ((779217323673 / 500000000000) : ℝ) = ((500000000000 / 779217323673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (78691849 / 250000000) ≤ -Real.log (62500000000 / 85621288821) ∧
    -Real.log (62500000000 / 85621288821) ≤ (314767397 / 1000000000) := by
  have h := checkLog_sound (w := (23121288821 / 148121288821)) (n := 12)
    (lo := (78691849 / 250000000)) (hi := (314767397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85621288821 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85621288821 / 62500000000) = 1/(62500000000 / 85621288821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78691849 / 250000000) (314767397 / 1000000000) (Real.log (85621288821 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (85621288821 / 62500000000) = -Real.log (62500000000 / 85621288821) := by
    rw [show ((85621288821 / 62500000000) : ℝ) = ((62500000000 / 85621288821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9856341 / 31250000) ≤ -Real.log (100000000000 / 137081151693) ∧
    -Real.log (100000000000 / 137081151693) ≤ (315402913 / 1000000000) := by
  have h := checkLog_sound (w := (37081151693 / 237081151693)) (n := 12)
    (lo := (9856341 / 31250000)) (hi := (315402913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137081151693 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137081151693 / 100000000000) = 1/(100000000000 / 137081151693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9856341 / 31250000) (315402913 / 1000000000) (Real.log (137081151693 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137081151693 / 100000000000) = -Real.log (100000000000 / 137081151693) := by
    rw [show ((137081151693 / 100000000000) : ℝ) = ((100000000000 / 137081151693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24767343 / 1000000000) ≤ -Real.log (975536850351 / 1000000000000) ∧
    -Real.log (975536850351 / 1000000000000) ≤ (1547959 / 62500000) := by
  have h := checkLog_sound (w := (24463149649 / 1975536850351)) (n := 12)
    (lo := (24767343 / 1000000000)) (hi := (1547959 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975536850351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975536850351) = 1/(975536850351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1547959 / 62500000) (-24767343 / 1000000000) (Real.log (975536850351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24668043 / 1000000000) ≤ -Real.log (975633726591 / 1000000000000) ∧
    -Real.log (975633726591 / 1000000000000) ≤ (6167011 / 250000000) := by
  have h := checkLog_sound (w := (24366273409 / 1975633726591)) (n := 12)
    (lo := (24668043 / 1000000000)) (hi := (6167011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975633726591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975633726591) = 1/(975633726591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6167011 / 250000000) (-24668043 / 1000000000) (Real.log (975633726591 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell097
