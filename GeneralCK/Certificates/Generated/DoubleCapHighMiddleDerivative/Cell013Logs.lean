import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell013
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

theorem reflection_log_1_neg : (229684611 / 1000000000) ≤ -Real.log (2560 / 3221) ∧
    -Real.log (2560 / 3221) ≤ (57421153 / 250000000) := by
  have h := checkLog_sound (w := (661 / 5781)) (n := 12)
    (lo := (229684611 / 1000000000)) (hi := (57421153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3221 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3221 / 2560) = 1/(2560 / 3221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229684611 / 1000000000) (57421153 / 250000000) (Real.log (3221 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3221 / 2560) = -Real.log (2560 / 3221) := by
    rw [show ((3221 / 2560) : ℝ) = ((2560 / 3221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149339913 / 500000000) ≤ -Real.log (1899 / 2560) ∧
    -Real.log (1899 / 2560) ≤ (298679827 / 1000000000) := by
  have h := checkLog_sound (w := (661 / 4459)) (n := 12)
    (lo := (149339913 / 500000000)) (hi := (298679827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1899) = 1/(1899 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-298679827 / 1000000000) (-149339913 / 500000000) (Real.log (1899 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229218809 / 1000000000) ≤ -Real.log (5120 / 6439) ∧
    -Real.log (5120 / 6439) ≤ (22921881 / 100000000) := by
  have h := checkLog_sound (w := (1319 / 11559)) (n := 12)
    (lo := (229218809 / 1000000000)) (hi := (22921881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6439 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6439 / 5120) = 1/(5120 / 6439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229218809 / 1000000000) (22921881 / 100000000) (Real.log (6439 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6439 / 5120) = -Real.log (5120 / 6439) := by
    rw [show ((6439 / 5120) : ℝ) = ((5120 / 6439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (297890249 / 1000000000) ≤ -Real.log (3801 / 5120) ∧
    -Real.log (3801 / 5120) ≤ (1191561 / 4000000) := by
  have h := checkLog_sound (w := (1319 / 8921)) (n := 12)
    (lo := (297890249 / 1000000000)) (hi := (1191561 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3801) = 1/(3801 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1191561 / 4000000) (-297890249 / 1000000000) (Real.log (3801 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167783049 / 1000000000) ≤ -Real.log (25000 / 29567) ∧
    -Real.log (25000 / 29567) ≤ (3355661 / 20000000) := by
  have h := checkLog_sound (w := (4567 / 54567)) (n := 12)
    (lo := (167783049 / 1000000000)) (hi := (3355661 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29567 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29567 / 25000) = 1/(25000 / 29567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167783049 / 1000000000) (3355661 / 20000000) (Real.log (29567 / 25000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29567 / 25000) = -Real.log (25000 / 29567) := by
    rw [show ((29567 / 25000) : ℝ) = ((25000 / 29567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (201724583 / 1000000000) ≤ -Real.log (20433 / 25000) ∧
    -Real.log (20433 / 25000) ≤ (25215573 / 125000000) := by
  have h := checkLog_sound (w := (4567 / 45433)) (n := 12)
    (lo := (201724583 / 1000000000)) (hi := (25215573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20433) = 1/(20433 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25215573 / 125000000) (-201724583 / 1000000000) (Real.log (20433 / 25000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168137267 / 1000000000) ≤ -Real.log (1000000 / 1183099) ∧
    -Real.log (1000000 / 1183099) ≤ (42034317 / 250000000) := by
  have h := checkLog_sound (w := (183099 / 2183099)) (n := 12)
    (lo := (168137267 / 1000000000)) (hi := (42034317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183099 / 1000000) = 1/(1000000 / 1183099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168137267 / 1000000000) (42034317 / 250000000) (Real.log (1183099 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1183099 / 1000000) = -Real.log (1000000 / 1183099) := by
    rw [show ((1183099 / 1000000) : ℝ) = ((1000000 / 1183099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (101118683 / 500000000) ≤ -Real.log (816901 / 1000000) ∧
    -Real.log (816901 / 1000000) ≤ (202237367 / 1000000000) := by
  have h := checkLog_sound (w := (183099 / 1816901)) (n := 12)
    (lo := (101118683 / 500000000)) (hi := (202237367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816901) = 1/(816901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-202237367 / 1000000000) (-101118683 / 500000000) (Real.log (816901 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122553859 / 1000000000) ≤ -Real.log (50000 / 56519) ∧
    -Real.log (50000 / 56519) ≤ (6127693 / 50000000) := by
  have h := checkLog_sound (w := (6519 / 106519)) (n := 12)
    (lo := (122553859 / 1000000000)) (hi := (6127693 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56519 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56519 / 50000) = 1/(50000 / 56519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122553859 / 1000000000) (6127693 / 50000000) (Real.log (56519 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56519 / 50000) = -Real.log (50000 / 56519) := by
    rw [show ((56519 / 50000) : ℝ) = ((50000 / 56519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (545699 / 3906250) ≤ -Real.log (43481 / 50000) ∧
    -Real.log (43481 / 50000) ≤ (27939789 / 200000000) := by
  have h := checkLog_sound (w := (6519 / 93481)) (n := 12)
    (lo := (545699 / 3906250)) (hi := (27939789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43481) = 1/(43481 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-27939789 / 200000000) (-545699 / 3906250) (Real.log (43481 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (122823643 / 1000000000) ≤ -Real.log (200000 / 226137) ∧
    -Real.log (200000 / 226137) ≤ (30705911 / 250000000) := by
  have h := checkLog_sound (w := (26137 / 426137)) (n := 12)
    (lo := (122823643 / 1000000000)) (hi := (30705911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226137 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226137 / 200000) = 1/(200000 / 226137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (122823643 / 1000000000) (30705911 / 250000000) (Real.log (226137 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226137 / 200000) = -Real.log (200000 / 226137) := by
    rw [show ((226137 / 200000) : ℝ) = ((200000 / 226137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (140049733 / 1000000000) ≤ -Real.log (173863 / 200000) ∧
    -Real.log (173863 / 200000) ≤ (70024867 / 500000000) := by
  have h := checkLog_sound (w := (26137 / 373863)) (n := 12)
    (lo := (140049733 / 1000000000)) (hi := (70024867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173863) = 1/(173863 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-70024867 / 500000000) (-140049733 / 1000000000) (Real.log (173863 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263554529 / 500000000) ≤ -Real.log (500000000000 / 847013943699) ∧
    -Real.log (500000000000 / 847013943699) ≤ (527109059 / 1000000000) := by
  have h := checkLog_sound (w := (347013943699 / 1347013943699)) (n := 12)
    (lo := (263554529 / 500000000)) (hi := (527109059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847013943699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847013943699 / 500000000000) = 1/(500000000000 / 847013943699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263554529 / 500000000) (527109059 / 1000000000) (Real.log (847013943699 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (847013943699 / 500000000000) = -Real.log (500000000000 / 847013943699) := by
    rw [show ((847013943699 / 500000000000) : ℝ) = ((500000000000 / 847013943699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (264182219 / 500000000) ≤ -Real.log (125000000000 / 212019483939) ∧
    -Real.log (125000000000 / 212019483939) ≤ (528364439 / 1000000000) := by
  have h := checkLog_sound (w := (87019483939 / 337019483939)) (n := 12)
    (lo := (264182219 / 500000000)) (hi := (528364439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212019483939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212019483939 / 125000000000) = 1/(125000000000 / 212019483939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (264182219 / 500000000) (528364439 / 1000000000) (Real.log (212019483939 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (212019483939 / 125000000000) = -Real.log (125000000000 / 212019483939) := by
    rw [show ((212019483939 / 125000000000) : ℝ) = ((125000000000 / 212019483939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (369507633 / 1000000000) ≤ -Real.log (62500000000 / 90438873391) ∧
    -Real.log (62500000000 / 90438873391) ≤ (184753817 / 500000000) := by
  have h := checkLog_sound (w := (27938873391 / 152938873391)) (n := 12)
    (lo := (369507633 / 1000000000)) (hi := (184753817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90438873391 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90438873391 / 62500000000) = 1/(62500000000 / 90438873391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (369507633 / 1000000000) (184753817 / 500000000) (Real.log (90438873391 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90438873391 / 62500000000) = -Real.log (62500000000 / 90438873391) := by
    rw [show ((90438873391 / 62500000000) : ℝ) = ((62500000000 / 90438873391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (370374633 / 1000000000) ≤ -Real.log (244140625 / 353583273) ∧
    -Real.log (244140625 / 353583273) ≤ (185187317 / 500000000) := by
  have h := checkLog_sound (w := (54721324 / 298861949)) (n := 12)
    (lo := (370374633 / 1000000000)) (hi := (185187317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353583273 / 244140625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353583273 / 244140625) = 1/(244140625 / 353583273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (370374633 / 1000000000) (185187317 / 500000000) (Real.log (353583273 / 244140625)) := by
  have h := reflection_log_16_neg
  have he : Real.log (353583273 / 244140625) = -Real.log (244140625 / 353583273) := by
    rw [show ((353583273 / 244140625) : ℝ) = ((244140625 / 353583273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (262252803 / 1000000000) ≤ -Real.log (125000000000 / 162481888641) ∧
    -Real.log (125000000000 / 162481888641) ≤ (65563201 / 250000000) := by
  have h := checkLog_sound (w := (37481888641 / 287481888641)) (n := 12)
    (lo := (262252803 / 1000000000)) (hi := (65563201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162481888641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162481888641 / 125000000000) = 1/(125000000000 / 162481888641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (262252803 / 1000000000) (65563201 / 250000000) (Real.log (162481888641 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (162481888641 / 125000000000) = -Real.log (125000000000 / 162481888641) := by
    rw [show ((162481888641 / 125000000000) : ℝ) = ((125000000000 / 162481888641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (262873377 / 1000000000) ≤ -Real.log (125000000000 / 162582751937) ∧
    -Real.log (125000000000 / 162582751937) ≤ (131436689 / 500000000) := by
  have h := checkLog_sound (w := (37582751937 / 287582751937)) (n := 12)
    (lo := (262873377 / 1000000000)) (hi := (131436689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162582751937 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162582751937 / 125000000000) = 1/(125000000000 / 162582751937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (262873377 / 1000000000) (131436689 / 500000000) (Real.log (162582751937 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (162582751937 / 125000000000) = -Real.log (125000000000 / 162582751937) := by
    rw [show ((162582751937 / 125000000000) : ℝ) = ((125000000000 / 162582751937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1722609 / 100000000) ≤ -Real.log (39316857231 / 40000000000) ∧
    -Real.log (39316857231 / 40000000000) ≤ (17226091 / 1000000000) := by
  have h := checkLog_sound (w := (683142769 / 79316857231)) (n := 12)
    (lo := (1722609 / 100000000)) (hi := (17226091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39316857231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39316857231) = 1/(39316857231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17226091 / 1000000000) (-1722609 / 100000000) (Real.log (39316857231 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4286271 / 250000000) ≤ -Real.log (2457502639 / 2500000000) ∧
    -Real.log (2457502639 / 2500000000) ≤ (3429017 / 200000000) := by
  have h := checkLog_sound (w := (42497361 / 4957502639)) (n := 12)
    (lo := (4286271 / 250000000)) (hi := (3429017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2457502639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2457502639) = 1/(2457502639 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3429017 / 200000000) (-4286271 / 250000000) (Real.log (2457502639 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell013
