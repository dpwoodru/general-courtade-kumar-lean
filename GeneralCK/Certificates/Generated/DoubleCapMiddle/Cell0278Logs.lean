import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0278
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

theorem reflection_log_1_neg : (114997513 / 500000000) ≤ -Real.log (1280 / 1611) ∧
    -Real.log (1280 / 1611) ≤ (229995027 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2891)) (n := 12)
    (lo := (114997513 / 500000000)) (hi := (229995027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1280) = 1/(1280 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (114997513 / 500000000) (229995027 / 1000000000) (Real.log (1611 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1611 / 1280) = -Real.log (1280 / 1611) := by
    rw [show ((1611 / 1280) : ℝ) = ((1280 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149603279 / 500000000) ≤ -Real.log (949 / 1280) ∧
    -Real.log (949 / 1280) ≤ (299206559 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2229)) (n := 12)
    (lo := (149603279 / 500000000)) (hi := (299206559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 949) = 1/(949 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) (Real.log (949 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (28691171 / 125000000) ≤ -Real.log (5120 / 6441) ∧
    -Real.log (5120 / 6441) ≤ (229529369 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 11561)) (n := 12)
    (lo := (28691171 / 125000000)) (hi := (229529369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6441 / 5120) = 1/(5120 / 6441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (28691171 / 125000000) (229529369 / 1000000000) (Real.log (6441 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6441 / 5120) = -Real.log (5120 / 6441) := by
    rw [show ((6441 / 5120) : ℝ) = ((5120 / 6441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74604141 / 250000000) ≤ -Real.log (3799 / 5120) ∧
    -Real.log (3799 / 5120) ≤ (59683313 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 8919)) (n := 12)
    (lo := (74604141 / 250000000)) (hi := (59683313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3799) = 1/(3799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59683313 / 200000000) (-74604141 / 250000000) (Real.log (3799 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (416858291 / 1000000000) ≤ -Real.log (640 / 971) ∧
    -Real.log (640 / 971) ≤ (104214573 / 250000000) := by
  have h := checkLog_sound (w := (331 / 1611)) (n := 12)
    (lo := (416858291 / 1000000000)) (hi := (104214573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971 / 640) = 1/(640 / 971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (416858291 / 1000000000) (104214573 / 250000000) (Real.log (971 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (971 / 640) = -Real.log (640 / 971) := by
    rw [show ((971 / 640) : ℝ) = ((640 / 971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (364063449 / 500000000) ≤ -Real.log (309 / 640) ∧
    -Real.log (309 / 640) ≤ (7281269 / 10000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 309) = 1/(309 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) (Real.log (309 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (416085593 / 1000000000) ≤ -Real.log (2560 / 3881) ∧
    -Real.log (2560 / 3881) ≤ (208042797 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 6441)) (n := 12)
    (lo := (416085593 / 1000000000)) (hi := (208042797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3881 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3881 / 2560) = 1/(2560 / 3881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (416085593 / 1000000000) (208042797 / 500000000) (Real.log (3881 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3881 / 2560) = -Real.log (2560 / 3881) := by
    rw [show ((3881 / 2560) : ℝ) = ((2560 / 3881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (145140531 / 200000000) ≤ -Real.log (1239 / 2560) ∧
    -Real.log (1239 / 2560) ≤ (725702657 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 2519)) (n := 12)
    (lo := (1302219 / 40000000)) (hi := (8138869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1239) = 1/(1239 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-725702657 / 1000000000) (-145140531 / 200000000) (Real.log (1239 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (314409199 / 1000000000) ≤ -Real.log (20000 / 27389) ∧
    -Real.log (20000 / 27389) ≤ (786023 / 2500000) := by
  have h := checkLog_sound (w := (7389 / 47389)) (n := 12)
    (lo := (314409199 / 1000000000)) (hi := (786023 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27389 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27389 / 20000) = 1/(20000 / 27389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (314409199 / 1000000000) (786023 / 2500000) (Real.log (27389 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27389 / 20000) = -Real.log (20000 / 27389) := by
    rw [show ((27389 / 20000) : ℝ) = ((20000 / 27389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57645353 / 125000000) ≤ -Real.log (12611 / 20000) ∧
    -Real.log (12611 / 20000) ≤ (18446513 / 40000000) := by
  have h := checkLog_sound (w := (7389 / 32611)) (n := 12)
    (lo := (57645353 / 125000000)) (hi := (18446513 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12611) = 1/(12611 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18446513 / 40000000) (-57645353 / 125000000) (Real.log (12611 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31503991 / 100000000) ≤ -Real.log (500000 / 685157) ∧
    -Real.log (500000 / 685157) ≤ (315039911 / 1000000000) := by
  have h := checkLog_sound (w := (185157 / 1185157)) (n := 12)
    (lo := (31503991 / 100000000)) (hi := (315039911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685157 / 500000) = 1/(500000 / 685157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31503991 / 100000000) (315039911 / 1000000000) (Real.log (685157 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (685157 / 500000) = -Real.log (500000 / 685157) := by
    rw [show ((685157 / 500000) : ℝ) = ((500000 / 685157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115633499 / 250000000) ≤ -Real.log (314843 / 500000) ∧
    -Real.log (314843 / 500000) ≤ (462533997 / 1000000000) := by
  have h := checkLog_sound (w := (185157 / 814843)) (n := 12)
    (lo := (115633499 / 250000000)) (hi := (462533997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314843) = 1/(314843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-462533997 / 1000000000) (-115633499 / 250000000) (Real.log (314843 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (240189441 / 1000000000) ≤ -Real.log (100000 / 127149) ∧
    -Real.log (100000 / 127149) ≤ (120094721 / 500000000) := by
  have h := checkLog_sound (w := (27149 / 227149)) (n := 12)
    (lo := (240189441 / 1000000000)) (hi := (120094721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127149 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127149 / 100000) = 1/(100000 / 127149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (240189441 / 1000000000) (120094721 / 500000000) (Real.log (127149 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (127149 / 100000) = -Real.log (100000 / 127149) := by
    rw [show ((127149 / 100000) : ℝ) = ((100000 / 127149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (158376963 / 500000000) ≤ -Real.log (72851 / 100000) ∧
    -Real.log (72851 / 100000) ≤ (316753927 / 1000000000) := by
  have h := checkLog_sound (w := (27149 / 172851)) (n := 12)
    (lo := (158376963 / 500000000)) (hi := (316753927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72851) = 1/(72851 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-316753927 / 1000000000) (-158376963 / 500000000) (Real.log (72851 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (120364017 / 500000000) ≤ -Real.log (40000 / 50887) ∧
    -Real.log (40000 / 50887) ≤ (48145607 / 200000000) := by
  have h := checkLog_sound (w := (10887 / 90887)) (n := 12)
    (lo := (120364017 / 500000000)) (hi := (48145607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50887 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50887 / 40000) = 1/(40000 / 50887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (120364017 / 500000000) (48145607 / 200000000) (Real.log (50887 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50887 / 40000) = -Real.log (40000 / 50887) := by
    rw [show ((50887 / 40000) : ℝ) = ((40000 / 50887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (79423661 / 250000000) ≤ -Real.log (29113 / 40000) ∧
    -Real.log (29113 / 40000) ≤ (63538929 / 200000000) := by
  have h := checkLog_sound (w := (10887 / 69113)) (n := 12)
    (lo := (79423661 / 250000000)) (hi := (63538929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29113) = 1/(29113 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-63538929 / 200000000) (-79423661 / 250000000) (Real.log (29113 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (775572023 / 1000000000) ≤ -Real.log (500000000000 / 1085917056537) ∧
    -Real.log (500000000000 / 1085917056537) ≤ (31022881 / 40000000) := by
  have h := checkLog_sound (w := (85917056537 / 2085917056537)) (n := 12)
    (lo := (82424843 / 1000000000)) (hi := (20606211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085917056537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1085917056537 / 1000000000000) = 1/(500000000000 / 1085917056537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (775572023 / 1000000000) (31022881 / 40000000) (Real.log (1085917056537 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1085917056537 / 500000000000) = -Real.log (500000000000 / 1085917056537) := by
    rw [show ((1085917056537 / 500000000000) : ℝ) = ((500000000000 / 1085917056537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (388786953 / 500000000) ≤ -Real.log (125000000000 / 272023278269) ∧
    -Real.log (125000000000 / 272023278269) ≤ (194393477 / 250000000) := by
  have h := checkLog_sound (w := (22023278269 / 522023278269)) (n := 12)
    (lo := (42213363 / 500000000)) (hi := (84426727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272023278269 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272023278269 / 250000000000) = 1/(125000000000 / 272023278269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (388786953 / 500000000) (194393477 / 250000000) (Real.log (272023278269 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (272023278269 / 125000000000) = -Real.log (125000000000 / 272023278269) := by
    rw [show ((272023278269 / 125000000000) : ℝ) = ((125000000000 / 272023278269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (556943367 / 1000000000) ≤ -Real.log (500000000000 / 872664754087) ∧
    -Real.log (500000000000 / 872664754087) ≤ (69617921 / 125000000) := by
  have h := checkLog_sound (w := (372664754087 / 1372664754087)) (n := 12)
    (lo := (556943367 / 1000000000)) (hi := (69617921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872664754087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872664754087 / 500000000000) = 1/(500000000000 / 872664754087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (556943367 / 1000000000) (69617921 / 125000000) (Real.log (872664754087 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (872664754087 / 500000000000) = -Real.log (500000000000 / 872664754087) := by
    rw [show ((872664754087 / 500000000000) : ℝ) = ((500000000000 / 872664754087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (279211339 / 500000000) ≤ -Real.log (125000000000 / 218489162917) ∧
    -Real.log (125000000000 / 218489162917) ≤ (558422679 / 1000000000) := by
  have h := checkLog_sound (w := (93489162917 / 343489162917)) (n := 12)
    (lo := (279211339 / 500000000)) (hi := (558422679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218489162917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218489162917 / 125000000000) = 1/(125000000000 / 218489162917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (279211339 / 500000000) (558422679 / 1000000000) (Real.log (218489162917 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (218489162917 / 125000000000) = -Real.log (125000000000 / 218489162917) := by
    rw [show ((218489162917 / 125000000000) : ℝ) = ((125000000000 / 218489162917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0278
