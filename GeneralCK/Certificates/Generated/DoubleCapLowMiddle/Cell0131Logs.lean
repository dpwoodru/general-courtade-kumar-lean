import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0131
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

theorem reflection_log_1_neg : (165470559 / 250000000) ≤ -Real.log (3200 / 6203) ∧
    -Real.log (3200 / 6203) ≤ (661882237 / 1000000000) := by
  have h := checkLog_sound (w := (3003 / 9403)) (n := 12)
    (lo := (165470559 / 250000000)) (hi := (661882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6203 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6203 / 3200) = 1/(3200 / 6203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (165470559 / 250000000) (661882237 / 1000000000) (Real.log (6203 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6203 / 3200) = -Real.log (3200 / 6203) := by
    rw [show ((6203 / 3200) : ℝ) = ((3200 / 6203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2787702357 / 1000000000) ≤ -Real.log (197 / 3200) ∧
    -Real.log (197 / 3200) ≤ (1393851181 / 500000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 197) = 1/(197 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1393851181 / 500000000) (-2787702357 / 1000000000) (Real.log (197 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (661499283 / 1000000000) ≤ -Real.log (5120 / 9921) ∧
    -Real.log (5120 / 9921) ≤ (165374821 / 250000000) := by
  have h := checkLog_sound (w := (4801 / 15041)) (n := 12)
    (lo := (661499283 / 1000000000)) (hi := (165374821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9921 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9921 / 5120) = 1/(5120 / 9921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (661499283 / 1000000000) (165374821 / 250000000) (Real.log (9921 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9921 / 5120) = -Real.log (5120 / 9921) := by
    rw [show ((9921 / 5120) : ℝ) = ((5120 / 9921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2775718613 / 1000000000) ≤ -Real.log (319 / 5120) ∧
    -Real.log (319 / 5120) ≤ (1387859309 / 500000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 319) = 1/(319 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1387859309 / 500000000) (-2775718613 / 1000000000) (Real.log (319 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (629608159 / 1000000000) ≤ -Real.log (1600 / 3003) ∧
    -Real.log (1600 / 3003) ≤ (3935051 / 6250000) := by
  have h := checkLog_sound (w := (1403 / 4603)) (n := 12)
    (lo := (629608159 / 1000000000)) (hi := (3935051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3003 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3003 / 1600) = 1/(1600 / 3003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (629608159 / 1000000000) (3935051 / 6250000) (Real.log (3003 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3003 / 1600) = -Real.log (1600 / 3003) := by
    rw [show ((3003 / 1600) : ℝ) = ((1600 / 3003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2094555177 / 1000000000) ≤ -Real.log (197 / 1600) ∧
    -Real.log (197 / 1600) ≤ (2094555181 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 197) = 1/(197 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2094555181 / 1000000000) (-2094555177 / 1000000000) (Real.log (197 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (628816971 / 1000000000) ≤ -Real.log (2560 / 4801) ∧
    -Real.log (2560 / 4801) ≤ (157204243 / 250000000) := by
  have h := checkLog_sound (w := (2241 / 7361)) (n := 12)
    (lo := (628816971 / 1000000000)) (hi := (157204243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 2560) = 1/(2560 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (628816971 / 1000000000) (157204243 / 250000000) (Real.log (4801 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4801 / 2560) = -Real.log (2560 / 4801) := by
    rw [show ((4801 / 2560) : ℝ) = ((2560 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2082571433 / 1000000000) ≤ -Real.log (319 / 2560) ∧
    -Real.log (319 / 2560) ≤ (2082571437 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 319) = 1/(319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2082571437 / 1000000000) (-2082571433 / 1000000000) (Real.log (319 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166976573 / 250000000) ≤ -Real.log (20000 / 39003) ∧
    -Real.log (20000 / 39003) ≤ (667906293 / 1000000000) := by
  have h := checkLog_sound (w := (19003 / 59003)) (n := 12)
    (lo := (166976573 / 250000000)) (hi := (667906293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39003 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39003 / 20000) = 1/(20000 / 39003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166976573 / 250000000) (667906293 / 1000000000) (Real.log (39003 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (39003 / 20000) = -Real.log (20000 / 39003) := by
    rw [show ((39003 / 20000) : ℝ) = ((20000 / 39003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149936839 / 50000000) ≤ -Real.log (997 / 20000) ∧
    -Real.log (997 / 20000) ≤ (599747357 / 200000000) := by
  have h := checkLog_sound (w := (253 / 2247)) (n := 12)
    (lo := (11307403 / 50000000)) (hi := (226148061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 997) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1250 / 997) = 1/(997 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-599747357 / 200000000) (-149936839 / 50000000) (Real.log (997 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334094141 / 500000000) ≤ -Real.log (10000 / 19507) ∧
    -Real.log (10000 / 19507) ≤ (668188283 / 1000000000) := by
  have h := checkLog_sound (w := (9507 / 29507)) (n := 12)
    (lo := (334094141 / 500000000)) (hi := (668188283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19507 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19507 / 10000) = 1/(10000 / 19507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334094141 / 500000000) (668188283 / 1000000000) (Real.log (19507 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19507 / 10000) = -Real.log (10000 / 19507) := by
    rw [show ((19507 / 10000) : ℝ) = ((10000 / 19507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (601966239 / 200000000) ≤ -Real.log (493 / 10000) ∧
    -Real.log (493 / 10000) ≤ (3762289 / 1250000) := by
  have h := checkLog_sound (w := (66 / 559)) (n := 12)
    (lo := (9489699 / 40000000)) (hi := (59310619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 493) = 1/(493 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3762289 / 1250000) (-601966239 / 200000000) (Real.log (493 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (333749787 / 500000000) ≤ -Real.log (1000000 / 1949357) ∧
    -Real.log (1000000 / 1949357) ≤ (26699983 / 40000000) := by
  have h := checkLog_sound (w := (949357 / 2949357)) (n := 12)
    (lo := (333749787 / 500000000)) (hi := (26699983 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949357 / 1000000) = 1/(1000000 / 1949357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (333749787 / 500000000) (26699983 / 40000000) (Real.log (1949357 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1949357 / 1000000) = -Real.log (1000000 / 1949357) := by
    rw [show ((1949357 / 1000000) : ℝ) = ((1000000 / 1949357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1491477129 / 500000000) ≤ -Real.log (50643 / 1000000) ∧
    -Real.log (50643 / 1000000) ≤ (2982954263 / 1000000000) := by
  have h := checkLog_sound (w := (11857 / 113143)) (n := 12)
    (lo := (105182769 / 500000000)) (hi := (210365539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50643) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50643) = 1/(50643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2982954263 / 1000000000) (-1491477129 / 500000000) (Real.log (50643 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (667792961 / 1000000000) ≤ -Real.log (1000000 / 1949929) ∧
    -Real.log (1000000 / 1949929) ≤ (333896481 / 500000000) := by
  have h := checkLog_sound (w := (949929 / 2949929)) (n := 12)
    (lo := (667792961 / 1000000000)) (hi := (333896481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949929 / 1000000) = 1/(1000000 / 1949929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (667792961 / 1000000000) (333896481 / 500000000) (Real.log (1949929 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1949929 / 1000000) = -Real.log (1000000 / 1949929) := by
    rw [show ((1949929 / 1000000) : ℝ) = ((1000000 / 1949929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1497156639 / 500000000) ≤ -Real.log (50071 / 1000000) ∧
    -Real.log (50071 / 1000000) ≤ (2994313283 / 1000000000) := by
  have h := checkLog_sound (w := (12429 / 112571)) (n := 12)
    (lo := (110862279 / 500000000)) (hi := (221724559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50071) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50071) = 1/(50071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2994313283 / 1000000000) (-1497156639 / 500000000) (Real.log (50071 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (28645649 / 7812500) ≤ -Real.log (62500000000 / 2445022567703) ∧
    -Real.log (62500000000 / 2445022567703) ≤ (1833321539 / 500000000) := by
  have h := checkLog_sound (w := (445022567703 / 4445022567703)) (n := 12)
    (lo := (50226793 / 250000000)) (hi := (200907173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2445022567703 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2445022567703 / 2000000000000) = 1/(62500000000 / 2445022567703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28645649 / 7812500) (1833321539 / 500000000) (Real.log (2445022567703 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2445022567703 / 62500000000) = -Real.log (62500000000 / 2445022567703) := by
    rw [show ((2445022567703 / 62500000000) : ℝ) = ((62500000000 / 2445022567703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3678019477 / 1000000000) ≤ -Real.log (50000000000 / 1978397565923) ∧
    -Real.log (50000000000 / 1978397565923) ≤ (3678019483 / 1000000000) := by
  have h := checkLog_sound (w := (378397565923 / 3578397565923)) (n := 12)
    (lo := (212283577 / 1000000000)) (hi := (106141789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978397565923 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1978397565923 / 1600000000000) = 1/(50000000000 / 1978397565923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3678019477 / 1000000000) (3678019483 / 1000000000) (Real.log (1978397565923 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1978397565923 / 50000000000) = -Real.log (50000000000 / 1978397565923) := by
    rw [show ((1978397565923 / 50000000000) : ℝ) = ((50000000000 / 1978397565923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3650453833 / 1000000000) ≤ -Real.log (500000000000 / 19246065596429) ∧
    -Real.log (500000000000 / 19246065596429) ≤ (3650453839 / 1000000000) := by
  have h := checkLog_sound (w := (3246065596429 / 35246065596429)) (n := 12)
    (lo := (184717933 / 1000000000)) (hi := (92358967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19246065596429 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19246065596429 / 16000000000000) = 1/(500000000000 / 19246065596429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3650453833 / 1000000000) (3650453839 / 1000000000) (Real.log (19246065596429 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19246065596429 / 500000000000) = -Real.log (500000000000 / 19246065596429) := by
    rw [show ((19246065596429 / 500000000000) : ℝ) = ((500000000000 / 19246065596429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3662106239 / 1000000000) ≤ -Real.log (15625000000 / 608488758463) ∧
    -Real.log (15625000000 / 608488758463) ≤ (732421249 / 200000000) := by
  have h := checkLog_sound (w := (108488758463 / 1108488758463)) (n := 12)
    (lo := (196370339 / 1000000000)) (hi := (9818517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608488758463 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(608488758463 / 500000000000) = 1/(15625000000 / 608488758463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3662106239 / 1000000000) (732421249 / 200000000) (Real.log (608488758463 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (608488758463 / 15625000000) = -Real.log (15625000000 / 608488758463) := by
    rw [show ((608488758463 / 15625000000) : ℝ) = ((15625000000 / 608488758463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0131
