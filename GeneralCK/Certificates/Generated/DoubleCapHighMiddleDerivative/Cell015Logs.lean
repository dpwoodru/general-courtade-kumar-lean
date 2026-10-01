import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell015
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

theorem reflection_log_1_neg : (115307783 / 500000000) ≤ -Real.log (320 / 403) ∧
    -Real.log (320 / 403) ≤ (230615567 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 723)) (n := 12)
    (lo := (115307783 / 500000000)) (hi := (230615567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403 / 320) = 1/(320 / 403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115307783 / 500000000) (230615567 / 1000000000) (Real.log (403 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (403 / 320) = -Real.log (320 / 403) := by
    rw [show ((403 / 320) : ℝ) = ((320 / 403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150130427 / 500000000) ≤ -Real.log (237 / 320) ∧
    -Real.log (237 / 320) ≤ (60052171 / 200000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 237) = 1/(237 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60052171 / 200000000) (-150130427 / 500000000) (Real.log (237 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230150197 / 1000000000) ≤ -Real.log (1024 / 1289) ∧
    -Real.log (1024 / 1289) ≤ (115075099 / 500000000) := by
  have h := checkLog_sound (w := (265 / 2313)) (n := 12)
    (lo := (230150197 / 1000000000)) (hi := (115075099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289 / 1024) = 1/(1024 / 1289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230150197 / 1000000000) (115075099 / 500000000) (Real.log (1289 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1289 / 1024) = -Real.log (1024 / 1289) := by
    rw [show ((1289 / 1024) : ℝ) = ((1024 / 1289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74867507 / 250000000) ≤ -Real.log (759 / 1024) ∧
    -Real.log (759 / 1024) ≤ (299470029 / 1000000000) := by
  have h := checkLog_sound (w := (265 / 1783)) (n := 12)
    (lo := (74867507 / 250000000)) (hi := (299470029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 759) = 1/(759 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299470029 / 1000000000) (-74867507 / 250000000) (Real.log (759 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168489669 / 1000000000) ≤ -Real.log (250000 / 295879) ∧
    -Real.log (250000 / 295879) ≤ (16848967 / 100000000) := by
  have h := checkLog_sound (w := (45879 / 545879)) (n := 12)
    (lo := (168489669 / 1000000000)) (hi := (16848967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295879 / 250000) = 1/(250000 / 295879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168489669 / 1000000000) (16848967 / 100000000) (Real.log (295879 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (295879 / 250000) = -Real.log (250000 / 295879) := by
    rw [show ((295879 / 250000) : ℝ) = ((250000 / 295879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (101373981 / 500000000) ≤ -Real.log (204121 / 250000) ∧
    -Real.log (204121 / 250000) ≤ (202747963 / 1000000000) := by
  have h := checkLog_sound (w := (45879 / 454121)) (n := 12)
    (lo := (101373981 / 500000000)) (hi := (202747963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204121) = 1/(204121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) (Real.log (204121 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42210909 / 250000000) ≤ -Real.log (200000 / 236787) ∧
    -Real.log (200000 / 236787) ≤ (168843637 / 1000000000) := by
  have h := checkLog_sound (w := (36787 / 436787)) (n := 12)
    (lo := (42210909 / 250000000)) (hi := (168843637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236787 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236787 / 200000) = 1/(200000 / 236787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42210909 / 250000000) (168843637 / 1000000000) (Real.log (236787 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (236787 / 200000) = -Real.log (200000 / 236787) := by
    rw [show ((236787 / 200000) : ℝ) = ((200000 / 236787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20326127 / 100000000) ≤ -Real.log (163213 / 200000) ∧
    -Real.log (163213 / 200000) ≤ (203261271 / 1000000000) := by
  have h := checkLog_sound (w := (36787 / 363213)) (n := 12)
    (lo := (20326127 / 100000000)) (hi := (203261271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163213) = 1/(163213 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-203261271 / 1000000000) (-20326127 / 100000000) (Real.log (163213 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61545793 / 500000000) ≤ -Real.log (250000 / 282747) ∧
    -Real.log (250000 / 282747) ≤ (123091587 / 1000000000) := by
  have h := checkLog_sound (w := (32747 / 532747)) (n := 12)
    (lo := (61545793 / 500000000)) (hi := (123091587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282747 / 250000) = 1/(250000 / 282747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61545793 / 500000000) (123091587 / 1000000000) (Real.log (282747 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282747 / 250000) = -Real.log (250000 / 282747) := by
    rw [show ((282747 / 250000) : ℝ) = ((250000 / 282747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17549793 / 125000000) ≤ -Real.log (217253 / 250000) ∧
    -Real.log (217253 / 250000) ≤ (28079669 / 200000000) := by
  have h := checkLog_sound (w := (32747 / 467253)) (n := 12)
    (lo := (17549793 / 125000000)) (hi := (28079669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217253) = 1/(217253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28079669 / 200000000) (-17549793 / 125000000) (Real.log (217253 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61680613 / 500000000) ≤ -Real.log (1000000 / 1131293) ∧
    -Real.log (1000000 / 1131293) ≤ (123361227 / 1000000000) := by
  have h := checkLog_sound (w := (131293 / 2131293)) (n := 12)
    (lo := (61680613 / 500000000)) (hi := (123361227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131293 / 1000000) = 1/(1000000 / 1131293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61680613 / 500000000) (123361227 / 1000000000) (Real.log (1131293 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131293 / 1000000) = -Real.log (1000000 / 1131293) := by
    rw [show ((1131293 / 1000000) : ℝ) = ((1000000 / 1131293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (140749379 / 1000000000) ≤ -Real.log (868707 / 1000000) ∧
    -Real.log (868707 / 1000000) ≤ (7037469 / 50000000) := by
  have h := checkLog_sound (w := (131293 / 1868707)) (n := 12)
    (lo := (140749379 / 1000000000)) (hi := (7037469 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868707) = 1/(868707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-7037469 / 50000000) (-140749379 / 1000000000) (Real.log (868707 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21184809 / 40000000) ≤ -Real.log (500000000000 / 849143610013) ∧
    -Real.log (500000000000 / 849143610013) ≤ (264810113 / 500000000) := by
  have h := checkLog_sound (w := (349143610013 / 1349143610013)) (n := 12)
    (lo := (21184809 / 40000000)) (hi := (264810113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849143610013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849143610013 / 500000000000) = 1/(500000000000 / 849143610013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21184809 / 40000000) (264810113 / 500000000) (Real.log (849143610013 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (849143610013 / 500000000000) = -Real.log (500000000000 / 849143610013) := by
    rw [show ((849143610013 / 500000000000) : ℝ) = ((500000000000 / 849143610013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26543821 / 50000000) ≤ -Real.log (100000000000 / 170042194093) ∧
    -Real.log (100000000000 / 170042194093) ≤ (530876421 / 1000000000) := by
  have h := checkLog_sound (w := (70042194093 / 270042194093)) (n := 12)
    (lo := (26543821 / 50000000)) (hi := (530876421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170042194093 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170042194093 / 100000000000) = 1/(100000000000 / 170042194093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (26543821 / 50000000) (530876421 / 1000000000) (Real.log (170042194093 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (170042194093 / 100000000000) = -Real.log (100000000000 / 170042194093) := by
    rw [show ((170042194093 / 100000000000) : ℝ) = ((100000000000 / 170042194093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (371237631 / 1000000000) ≤ -Real.log (500000000000 / 724763743073) ∧
    -Real.log (500000000000 / 724763743073) ≤ (1450147 / 3906250) := by
  have h := checkLog_sound (w := (224763743073 / 1224763743073)) (n := 12)
    (lo := (371237631 / 1000000000)) (hi := (1450147 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724763743073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724763743073 / 500000000000) = 1/(500000000000 / 724763743073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (371237631 / 1000000000) (1450147 / 3906250) (Real.log (724763743073 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (724763743073 / 500000000000) = -Real.log (500000000000 / 724763743073) := by
    rw [show ((724763743073 / 500000000000) : ℝ) = ((500000000000 / 724763743073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (186052453 / 500000000) ≤ -Real.log (10000000000 / 14507851703) ∧
    -Real.log (10000000000 / 14507851703) ≤ (372104907 / 1000000000) := by
  have h := checkLog_sound (w := (4507851703 / 24507851703)) (n := 12)
    (lo := (186052453 / 500000000)) (hi := (372104907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14507851703 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14507851703 / 10000000000) = 1/(10000000000 / 14507851703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (186052453 / 500000000) (372104907 / 1000000000) (Real.log (14507851703 / 10000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (14507851703 / 10000000000) = -Real.log (10000000000 / 14507851703) := by
    rw [show ((14507851703 / 10000000000) : ℝ) = ((10000000000 / 14507851703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (263489931 / 1000000000) ≤ -Real.log (500000000000 / 650732095759) ∧
    -Real.log (500000000000 / 650732095759) ≤ (65872483 / 250000000) := by
  have h := checkLog_sound (w := (150732095759 / 1150732095759)) (n := 12)
    (lo := (263489931 / 1000000000)) (hi := (65872483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650732095759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650732095759 / 500000000000) = 1/(500000000000 / 650732095759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (263489931 / 1000000000) (65872483 / 250000000) (Real.log (650732095759 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (650732095759 / 500000000000) = -Real.log (500000000000 / 650732095759) := by
    rw [show ((650732095759 / 500000000000) : ℝ) = ((500000000000 / 650732095759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132055303 / 500000000) ≤ -Real.log (125000000000 / 162784028447) ∧
    -Real.log (125000000000 / 162784028447) ≤ (264110607 / 1000000000) := by
  have h := checkLog_sound (w := (37784028447 / 287784028447)) (n := 12)
    (lo := (132055303 / 500000000)) (hi := (264110607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162784028447 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162784028447 / 125000000000) = 1/(125000000000 / 162784028447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132055303 / 500000000) (264110607 / 1000000000) (Real.log (162784028447 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (162784028447 / 125000000000) = -Real.log (125000000000 / 162784028447) := by
    rw [show ((162784028447 / 125000000000) : ℝ) = ((125000000000 / 162784028447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17388153 / 1000000000) ≤ -Real.log (982762148151 / 1000000000000) ∧
    -Real.log (982762148151 / 1000000000000) ≤ (8694077 / 500000000) := by
  have h := checkLog_sound (w := (17237851849 / 1982762148151)) (n := 12)
    (lo := (17388153 / 1000000000)) (hi := (8694077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982762148151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982762148151) = 1/(982762148151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8694077 / 500000000) (-17388153 / 1000000000) (Real.log (982762148151 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17306757 / 1000000000) ≤ -Real.log (61427633991 / 62500000000) ∧
    -Real.log (61427633991 / 62500000000) ≤ (8653379 / 500000000) := by
  have h := checkLog_sound (w := (1072366009 / 123927633991)) (n := 12)
    (lo := (17306757 / 1000000000)) (hi := (8653379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61427633991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61427633991) = 1/(61427633991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8653379 / 500000000) (-17306757 / 1000000000) (Real.log (61427633991 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell015
