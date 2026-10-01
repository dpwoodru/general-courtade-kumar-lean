import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038
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

theorem reflection_log_1_neg : (68018759 / 100000000) ≤ -Real.log (102400 / 202163) ∧
    -Real.log (102400 / 202163) ≤ (680187591 / 1000000000) := by
  have h := checkLog_sound (w := (99763 / 304563)) (n := 12)
    (lo := (68018759 / 100000000)) (hi := (680187591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202163 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202163 / 102400) = 1/(102400 / 202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68018759 / 100000000) (680187591 / 1000000000) (Real.log (202163 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202163 / 102400) = -Real.log (102400 / 202163) := by
    rw [show ((202163 / 102400) : ℝ) = ((102400 / 202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1829622401 / 500000000) ≤ -Real.log (2637 / 102400) ∧
    -Real.log (2637 / 102400) ≤ (457405601 / 125000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2637) = 1/(2637 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) (Real.log (2637 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (340046801 / 500000000) ≤ -Real.log (3200 / 6317) ∧
    -Real.log (3200 / 6317) ≤ (680093603 / 1000000000) := by
  have h := checkLog_sound (w := (3117 / 9517)) (n := 12)
    (lo := (340046801 / 500000000)) (hi := (680093603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6317 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6317 / 3200) = 1/(3200 / 6317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (340046801 / 500000000) (680093603 / 1000000000) (Real.log (6317 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6317 / 3200) = -Real.log (3200 / 6317) := by
    rw [show ((6317 / 3200) : ℝ) = ((3200 / 6317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1826032739 / 500000000) ≤ -Real.log (83 / 3200) ∧
    -Real.log (83 / 3200) ≤ (913016371 / 250000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(100 / 83) = 1/(83 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) (Real.log (83 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667057841 / 1000000000) ≤ -Real.log (51200 / 99763) ∧
    -Real.log (51200 / 99763) ≤ (333528921 / 500000000) := by
  have h := checkLog_sound (w := (48563 / 150963)) (n := 12)
    (lo := (667057841 / 1000000000)) (hi := (333528921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99763 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99763 / 51200) = 1/(51200 / 99763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667057841 / 1000000000) (333528921 / 500000000) (Real.log (99763 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99763 / 51200) = -Real.log (51200 / 99763) := by
    rw [show ((99763 / 51200) : ℝ) = ((51200 / 99763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1483048811 / 500000000) ≤ -Real.log (2637 / 51200) ∧
    -Real.log (2637 / 51200) ≤ (2966097627 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2637) = 1/(2637 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) (Real.log (2637 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (666867371 / 1000000000) ≤ -Real.log (1600 / 3117) ∧
    -Real.log (1600 / 3117) ≤ (166716843 / 250000000) := by
  have h := checkLog_sound (w := (1517 / 4717)) (n := 12)
    (lo := (666867371 / 1000000000)) (hi := (166716843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 1600) = 1/(1600 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (666867371 / 1000000000) (166716843 / 250000000) (Real.log (3117 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3117 / 1600) = -Real.log (1600 / 3117) := by
    rw [show ((3117 / 1600) : ℝ) = ((1600 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1479459149 / 500000000) ≤ -Real.log (83 / 1600) ∧
    -Real.log (83 / 1600) ≤ (2958918303 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 83) = 1/(83 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) (Real.log (83 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17054317 / 25000000) ≤ -Real.log (1000000 / 1978171) ∧
    -Real.log (1000000 / 1978171) ≤ (682172681 / 1000000000) := by
  have h := checkLog_sound (w := (978171 / 2978171)) (n := 12)
    (lo := (17054317 / 25000000)) (hi := (682172681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978171 / 1000000) = 1/(1000000 / 1978171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17054317 / 25000000) (682172681 / 1000000000) (Real.log (1978171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978171 / 1000000) = -Real.log (1000000 / 1978171) := by
    rw [show ((1978171 / 1000000) : ℝ) = ((1000000 / 1978171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (764903183 / 200000000) ≤ -Real.log (21829 / 1000000) ∧
    -Real.log (21829 / 1000000) ≤ (3824515921 / 1000000000) := by
  have h := checkLog_sound (w := (9421 / 53079)) (n := 12)
    (lo := (71756003 / 200000000)) (hi := (22423751 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21829) = 1/(21829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3824515921 / 1000000000) (-764903183 / 200000000) (Real.log (21829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136449701 / 200000000) ≤ -Real.log (1000000 / 1978321) ∧
    -Real.log (1000000 / 1978321) ≤ (341124253 / 500000000) := by
  have h := checkLog_sound (w := (978321 / 2978321)) (n := 12)
    (lo := (136449701 / 200000000)) (hi := (341124253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978321 / 1000000) = 1/(1000000 / 1978321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136449701 / 200000000) (341124253 / 500000000) (Real.log (1978321 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978321 / 1000000) = -Real.log (1000000 / 1978321) := by
    rw [show ((1978321 / 1000000) : ℝ) = ((1000000 / 1978321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1915705613 / 500000000) ≤ -Real.log (21679 / 1000000) ∧
    -Real.log (21679 / 1000000) ≤ (119731601 / 31250000) := by
  have h := checkLog_sound (w := (9571 / 52929)) (n := 12)
    (lo := (182837663 / 500000000)) (hi := (365675327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21679) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21679) = 1/(21679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-119731601 / 31250000) (-1915705613 / 500000000) (Real.log (21679 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682117071 / 1000000000) ≤ -Real.log (1000000 / 1978061) ∧
    -Real.log (1000000 / 1978061) ≤ (42632317 / 62500000) := by
  have h := checkLog_sound (w := (978061 / 2978061)) (n := 12)
    (lo := (682117071 / 1000000000)) (hi := (42632317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978061 / 1000000) = 1/(1000000 / 1978061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682117071 / 1000000000) (42632317 / 62500000) (Real.log (1978061 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978061 / 1000000) = -Real.log (1000000 / 1978061) := by
    rw [show ((1978061 / 1000000) : ℝ) = ((1000000 / 1978061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3819489401 / 1000000000) ≤ -Real.log (21939 / 1000000) ∧
    -Real.log (21939 / 1000000) ≤ (3819489407 / 1000000000) := by
  have h := checkLog_sound (w := (9311 / 53189)) (n := 12)
    (lo := (353753501 / 1000000000)) (hi := (176876751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21939) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21939) = 1/(21939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3819489407 / 1000000000) (-3819489401 / 1000000000) (Real.log (21939 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682193911 / 1000000000) ≤ -Real.log (1000000 / 1978213) ∧
    -Real.log (1000000 / 1978213) ≤ (85274239 / 125000000) := by
  have h := checkLog_sound (w := (978213 / 2978213)) (n := 12)
    (lo := (682193911 / 1000000000)) (hi := (85274239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978213 / 1000000) = 1/(1000000 / 1978213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682193911 / 1000000000) (85274239 / 125000000) (Real.log (1978213 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978213 / 1000000) = -Real.log (1000000 / 1978213) := by
    rw [show ((1978213 / 1000000) : ℝ) = ((1000000 / 1978213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1913220907 / 500000000) ≤ -Real.log (21787 / 1000000) ∧
    -Real.log (21787 / 1000000) ≤ (191322091 / 50000000) := by
  have h := checkLog_sound (w := (9463 / 53037)) (n := 12)
    (lo := (180352957 / 500000000)) (hi := (72141183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21787) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21787) = 1/(21787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-191322091 / 50000000) (-1913220907 / 500000000) (Real.log (21787 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (901337719 / 200000000) ≤ -Real.log (500000000000 / 45310618901461) ∧
    -Real.log (500000000000 / 45310618901461) ≤ (2253344301 / 500000000) := by
  have h := checkLog_sound (w := (13310618901461 / 77310618901461)) (n := 12)
    (lo := (69561103 / 200000000)) (hi := (86951379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45310618901461 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45310618901461 / 32000000000000) = 1/(500000000000 / 45310618901461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (901337719 / 200000000) (2253344301 / 500000000) (Real.log (45310618901461 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45310618901461 / 500000000000) = -Real.log (500000000000 / 45310618901461) := by
    rw [show ((45310618901461 / 500000000000) : ℝ) = ((500000000000 / 45310618901461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (451365973 / 100000000) ≤ -Real.log (31250000000 / 2851724306933) ∧
    -Real.log (31250000000 / 2851724306933) ≤ (4513659737 / 1000000000) := by
  have h := checkLog_sound (w := (851724306933 / 4851724306933)) (n := 12)
    (lo := (7095533 / 20000000)) (hi := (354776651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2851724306933 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2851724306933 / 2000000000000) = 1/(31250000000 / 2851724306933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (451365973 / 100000000) (4513659737 / 1000000000) (Real.log (2851724306933 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2851724306933 / 31250000000) = -Real.log (31250000000 / 2851724306933) := by
    rw [show ((2851724306933 / 31250000000) : ℝ) = ((31250000000 / 2851724306933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (562700809 / 125000000) ≤ -Real.log (500000000000 / 45080928939331) ∧
    -Real.log (500000000000 / 45080928939331) ≤ (4501606479 / 1000000000) := by
  have h := checkLog_sound (w := (13080928939331 / 77080928939331)) (n := 12)
    (lo := (5355053 / 15625000)) (hi := (342723393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45080928939331 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45080928939331 / 32000000000000) = 1/(500000000000 / 45080928939331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (562700809 / 125000000) (4501606479 / 1000000000) (Real.log (45080928939331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45080928939331 / 500000000000) = -Real.log (500000000000 / 45080928939331) := by
    rw [show ((45080928939331 / 500000000000) : ℝ) = ((500000000000 / 45080928939331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (180345429 / 40000000) ≤ -Real.log (500000000000 / 45398930554919) ∧
    -Real.log (500000000000 / 45398930554919) ≤ (1127158933 / 250000000) := by
  have h := checkLog_sound (w := (13398930554919 / 77398930554919)) (n := 12)
    (lo := (69950529 / 200000000)) (hi := (174876323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45398930554919 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45398930554919 / 32000000000000) = 1/(500000000000 / 45398930554919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (180345429 / 40000000) (1127158933 / 250000000) (Real.log (45398930554919 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45398930554919 / 500000000000) = -Real.log (500000000000 / 45398930554919) := by
    rw [show ((45398930554919 / 500000000000) : ℝ) = ((500000000000 / 45398930554919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038
