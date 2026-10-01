import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell229
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

theorem reflection_log_1_neg : (325530901 / 1000000000) ≤ -Real.log (512 / 709) ∧
    -Real.log (512 / 709) ≤ (162765451 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1221)) (n := 12)
    (lo := (325530901 / 1000000000)) (hi := (162765451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 512) = 1/(512 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325530901 / 1000000000) (162765451 / 500000000) (Real.log (709 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (709 / 512) = -Real.log (512 / 709) := by
    rw [show ((709 / 512) : ℝ) = ((512 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (242875993 / 500000000) ≤ -Real.log (315 / 512) ∧
    -Real.log (315 / 512) ≤ (485751987 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 827)) (n := 12)
    (lo := (242875993 / 500000000)) (hi := (485751987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 315) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 315) = 1/(315 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-485751987 / 1000000000) (-242875993 / 500000000) (Real.log (315 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2031923 / 6250000) ≤ -Real.log (5120 / 7087) ∧
    -Real.log (5120 / 7087) ≤ (325107681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 12207)) (n := 12)
    (lo := (2031923 / 6250000)) (hi := (325107681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7087 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7087 / 5120) = 1/(5120 / 7087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2031923 / 6250000) (325107681 / 1000000000) (Real.log (7087 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7087 / 5120) = -Real.log (5120 / 7087) := by
    rw [show ((7087 / 5120) : ℝ) = ((5120 / 7087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (242400029 / 500000000) ≤ -Real.log (3153 / 5120) ∧
    -Real.log (3153 / 5120) ≤ (484800059 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 8273)) (n := 12)
    (lo := (242400029 / 500000000)) (hi := (484800059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3153) = 1/(3153 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-484800059 / 1000000000) (-242400029 / 500000000) (Real.log (3153 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30214943 / 125000000) ≤ -Real.log (1000000 / 1273437) ∧
    -Real.log (1000000 / 1273437) ≤ (48343909 / 200000000) := by
  have h := checkLog_sound (w := (273437 / 2273437)) (n := 12)
    (lo := (30214943 / 125000000)) (hi := (48343909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273437 / 1000000) = 1/(1000000 / 1273437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30214943 / 125000000) (48343909 / 200000000) (Real.log (1273437 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1273437 / 1000000) = -Real.log (1000000 / 1273437) := by
    rw [show ((1273437 / 1000000) : ℝ) = ((1000000 / 1273437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159715041 / 500000000) ≤ -Real.log (726563 / 1000000) ∧
    -Real.log (726563 / 1000000) ≤ (319430083 / 1000000000) := by
  have h := checkLog_sound (w := (273437 / 1726563)) (n := 12)
    (lo := (159715041 / 500000000)) (hi := (319430083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726563) = 1/(726563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-319430083 / 1000000000) (-159715041 / 500000000) (Real.log (726563 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121026223 / 500000000) ≤ -Real.log (1000000 / 1273861) ∧
    -Real.log (1000000 / 1273861) ≤ (242052447 / 1000000000) := by
  have h := checkLog_sound (w := (273861 / 2273861)) (n := 12)
    (lo := (121026223 / 500000000)) (hi := (242052447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273861 / 1000000) = 1/(1000000 / 1273861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121026223 / 500000000) (242052447 / 1000000000) (Real.log (1273861 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1273861 / 1000000) = -Real.log (1000000 / 1273861) := by
    rw [show ((1273861 / 1000000) : ℝ) = ((1000000 / 1273861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160006911 / 500000000) ≤ -Real.log (726139 / 1000000) ∧
    -Real.log (726139 / 1000000) ≤ (320013823 / 1000000000) := by
  have h := checkLog_sound (w := (273861 / 1726139)) (n := 12)
    (lo := (160006911 / 500000000)) (hi := (320013823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726139) = 1/(726139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-320013823 / 1000000000) (-160006911 / 500000000) (Real.log (726139 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (90092137 / 500000000) ≤ -Real.log (500000 / 598719) ∧
    -Real.log (500000 / 598719) ≤ (7207371 / 40000000) := by
  have h := checkLog_sound (w := (98719 / 1098719)) (n := 12)
    (lo := (90092137 / 500000000)) (hi := (7207371 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598719 / 500000) = 1/(500000 / 598719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (90092137 / 500000000) (7207371 / 40000000) (Real.log (598719 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (598719 / 500000) = -Real.log (500000 / 598719) := by
    rw [show ((598719 / 500000) : ℝ) = ((500000 / 598719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27493271 / 125000000) ≤ -Real.log (401281 / 500000) ∧
    -Real.log (401281 / 500000) ≤ (219946169 / 1000000000) := by
  have h := checkLog_sound (w := (98719 / 901281)) (n := 12)
    (lo := (27493271 / 125000000)) (hi := (219946169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401281) = 1/(401281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219946169 / 1000000000) (-27493271 / 125000000) (Real.log (401281 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180450641 / 1000000000) ≤ -Real.log (1000000 / 1197757) ∧
    -Real.log (1000000 / 1197757) ≤ (90225321 / 500000000) := by
  have h := checkLog_sound (w := (197757 / 2197757)) (n := 12)
    (lo := (180450641 / 1000000000)) (hi := (90225321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197757 / 1000000) = 1/(1000000 / 1197757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180450641 / 1000000000) (90225321 / 500000000) (Real.log (1197757 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1197757 / 1000000) = -Real.log (1000000 / 1197757) := by
    rw [show ((1197757 / 1000000) : ℝ) = ((1000000 / 1197757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55085931 / 250000000) ≤ -Real.log (802243 / 1000000) ∧
    -Real.log (802243 / 1000000) ≤ (8813749 / 40000000) := by
  have h := checkLog_sound (w := (197757 / 1802243)) (n := 12)
    (lo := (55085931 / 250000000)) (hi := (8813749 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802243) = 1/(802243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8813749 / 40000000) (-55085931 / 250000000) (Real.log (802243 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (404953869 / 500000000) ≤ -Real.log (5000000000 / 11238503013) ∧
    -Real.log (5000000000 / 11238503013) ≤ (40495387 / 50000000) := by
  have h := checkLog_sound (w := (1238503013 / 21238503013)) (n := 12)
    (lo := (58380279 / 500000000)) (hi := (116760559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11238503013 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11238503013 / 10000000000) = 1/(5000000000 / 11238503013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (404953869 / 500000000) (40495387 / 50000000) (Real.log (11238503013 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (11238503013 / 5000000000) = -Real.log (5000000000 / 11238503013) := by
    rw [show ((11238503013 / 5000000000) : ℝ) = ((5000000000 / 11238503013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (811282887 / 1000000000) ≤ -Real.log (500000000000 / 1125396825397) ∧
    -Real.log (500000000000 / 1125396825397) ≤ (811282889 / 1000000000) := by
  have h := checkLog_sound (w := (125396825397 / 2125396825397)) (n := 12)
    (lo := (118135707 / 1000000000)) (hi := (29533927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125396825397 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1125396825397 / 1000000000000) = 1/(500000000000 / 1125396825397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (811282887 / 1000000000) (811282889 / 1000000000) (Real.log (1125396825397 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1125396825397 / 500000000000) = -Real.log (500000000000 / 1125396825397) := by
    rw [show ((1125396825397 / 500000000000) : ℝ) = ((500000000000 / 1125396825397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (280574813 / 500000000) ≤ -Real.log (25000000000 / 43817156943) ∧
    -Real.log (25000000000 / 43817156943) ≤ (561149627 / 1000000000) := by
  have h := checkLog_sound (w := (18817156943 / 68817156943)) (n := 12)
    (lo := (280574813 / 500000000)) (hi := (561149627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43817156943 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43817156943 / 25000000000) = 1/(25000000000 / 43817156943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280574813 / 500000000) (561149627 / 1000000000) (Real.log (43817156943 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (43817156943 / 25000000000) = -Real.log (25000000000 / 43817156943) := by
    rw [show ((43817156943 / 25000000000) : ℝ) = ((25000000000 / 43817156943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140516567 / 250000000) ≤ -Real.log (250000000000 / 438573399859) ∧
    -Real.log (250000000000 / 438573399859) ≤ (562066269 / 1000000000) := by
  have h := checkLog_sound (w := (188573399859 / 688573399859)) (n := 12)
    (lo := (140516567 / 250000000)) (hi := (562066269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438573399859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438573399859 / 250000000000) = 1/(250000000000 / 438573399859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140516567 / 250000000) (562066269 / 1000000000) (Real.log (438573399859 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (438573399859 / 250000000000) = -Real.log (250000000000 / 438573399859) := by
    rw [show ((438573399859 / 250000000000) : ℝ) = ((250000000000 / 438573399859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (200065221 / 500000000) ≤ -Real.log (250000000000 / 373004827041) ∧
    -Real.log (250000000000 / 373004827041) ≤ (400130443 / 1000000000) := by
  have h := checkLog_sound (w := (123004827041 / 623004827041)) (n := 12)
    (lo := (200065221 / 500000000)) (hi := (400130443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373004827041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373004827041 / 250000000000) = 1/(250000000000 / 373004827041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (200065221 / 500000000) (400130443 / 1000000000) (Real.log (373004827041 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (373004827041 / 250000000000) = -Real.log (250000000000 / 373004827041) := by
    rw [show ((373004827041 / 250000000000) : ℝ) = ((250000000000 / 373004827041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (80158873 / 200000000) ≤ -Real.log (100000000000 / 149301022259) ∧
    -Real.log (100000000000 / 149301022259) ≤ (200397183 / 500000000) := by
  have h := checkLog_sound (w := (49301022259 / 249301022259)) (n := 12)
    (lo := (80158873 / 200000000)) (hi := (200397183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149301022259 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149301022259 / 100000000000) = 1/(100000000000 / 149301022259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (80158873 / 200000000) (200397183 / 500000000) (Real.log (149301022259 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (149301022259 / 100000000000) = -Real.log (100000000000 / 149301022259) := by
    rw [show ((149301022259 / 100000000000) : ℝ) = ((100000000000 / 149301022259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39893083 / 1000000000) ≤ -Real.log (960892168951 / 1000000000000) ∧
    -Real.log (960892168951 / 1000000000000) ≤ (9973271 / 250000000) := by
  have h := checkLog_sound (w := (39107831049 / 1960892168951)) (n := 12)
    (lo := (39893083 / 1000000000)) (hi := (9973271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960892168951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960892168951) = 1/(960892168951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9973271 / 250000000) (-39893083 / 1000000000) (Real.log (960892168951 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39761893 / 1000000000) ≤ -Real.log (240254559039 / 250000000000) ∧
    -Real.log (240254559039 / 250000000000) ≤ (19880947 / 500000000) := by
  have h := checkLog_sound (w := (9745440961 / 490254559039)) (n := 12)
    (lo := (39761893 / 1000000000)) (hi := (19880947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240254559039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240254559039) = 1/(240254559039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19880947 / 500000000) (-39761893 / 1000000000) (Real.log (240254559039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell229
