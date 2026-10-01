import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell206
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

theorem reflection_log_1_neg : (157875609 / 500000000) ≤ -Real.log (5120 / 7021) ∧
    -Real.log (5120 / 7021) ≤ (315751219 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 12141)) (n := 12)
    (lo := (157875609 / 500000000)) (hi := (315751219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7021 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7021 / 5120) = 1/(5120 / 7021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157875609 / 500000000) (315751219 / 1000000000) (Real.log (7021 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7021 / 5120) = -Real.log (5120 / 7021) := by
    rw [show ((7021 / 5120) : ℝ) = ((5120 / 7021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232041843 / 500000000) ≤ -Real.log (3219 / 5120) ∧
    -Real.log (3219 / 5120) ≤ (464083687 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 8339)) (n := 12)
    (lo := (232041843 / 500000000)) (hi := (464083687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3219) = 1/(3219 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-464083687 / 1000000000) (-232041843 / 500000000) (Real.log (3219 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157661919 / 500000000) ≤ -Real.log (2560 / 3509) ∧
    -Real.log (2560 / 3509) ≤ (315323839 / 1000000000) := by
  have h := checkLog_sound (w := (949 / 6069)) (n := 12)
    (lo := (157661919 / 500000000)) (hi := (315323839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3509 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3509 / 2560) = 1/(2560 / 3509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157661919 / 500000000) (315323839 / 1000000000) (Real.log (3509 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3509 / 2560) = -Real.log (2560 / 3509) := by
    rw [show ((3509 / 2560) : ℝ) = ((2560 / 3509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (231576077 / 500000000) ≤ -Real.log (1611 / 2560) ∧
    -Real.log (1611 / 2560) ≤ (92630431 / 200000000) := by
  have h := checkLog_sound (w := (949 / 4171)) (n := 12)
    (lo := (231576077 / 500000000)) (hi := (92630431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1611) = 1/(1611 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-92630431 / 200000000) (-231576077 / 500000000) (Real.log (1611 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2925737 / 12500000) ≤ -Real.log (1000000 / 1263719) ∧
    -Real.log (1000000 / 1263719) ≤ (234058961 / 1000000000) := by
  have h := checkLog_sound (w := (263719 / 2263719)) (n := 12)
    (lo := (2925737 / 12500000)) (hi := (234058961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263719 / 1000000) = 1/(1000000 / 1263719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2925737 / 12500000) (234058961 / 1000000000) (Real.log (1263719 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1263719 / 1000000) = -Real.log (1000000 / 1263719) := by
    rw [show ((1263719 / 1000000) : ℝ) = ((1000000 / 1263719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (306143439 / 1000000000) ≤ -Real.log (736281 / 1000000) ∧
    -Real.log (736281 / 1000000) ≤ (3826793 / 12500000) := by
  have h := checkLog_sound (w := (263719 / 1736281)) (n := 12)
    (lo := (306143439 / 1000000000)) (hi := (3826793 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 736281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 736281) = 1/(736281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3826793 / 12500000) (-306143439 / 1000000000) (Real.log (736281 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (117197211 / 500000000) ≤ -Real.log (1000000 / 1264143) ∧
    -Real.log (1000000 / 1264143) ≤ (234394423 / 1000000000) := by
  have h := checkLog_sound (w := (264143 / 2264143)) (n := 12)
    (lo := (117197211 / 500000000)) (hi := (234394423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264143 / 1000000) = 1/(1000000 / 1264143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (117197211 / 500000000) (234394423 / 1000000000) (Real.log (1264143 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1264143 / 1000000) = -Real.log (1000000 / 1264143) := by
    rw [show ((1264143 / 1000000) : ℝ) = ((1000000 / 1264143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (19169967 / 62500000) ≤ -Real.log (735857 / 1000000) ∧
    -Real.log (735857 / 1000000) ≤ (306719473 / 1000000000) := by
  have h := checkLog_sound (w := (264143 / 1735857)) (n := 12)
    (lo := (19169967 / 62500000)) (hi := (306719473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735857) = 1/(735857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306719473 / 1000000000) (-19169967 / 62500000) (Real.log (735857 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174070947 / 1000000000) ≤ -Real.log (50000 / 59507) ∧
    -Real.log (50000 / 59507) ≤ (43517737 / 250000000) := by
  have h := checkLog_sound (w := (9507 / 109507)) (n := 12)
    (lo := (174070947 / 1000000000)) (hi := (43517737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59507 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59507 / 50000) = 1/(50000 / 59507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174070947 / 1000000000) (43517737 / 250000000) (Real.log (59507 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (59507 / 50000) = -Real.log (50000 / 59507) := by
    rw [show ((59507 / 50000) : ℝ) = ((50000 / 59507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42178777 / 200000000) ≤ -Real.log (40493 / 50000) ∧
    -Real.log (40493 / 50000) ≤ (105446943 / 500000000) := by
  have h := checkLog_sound (w := (9507 / 90493)) (n := 12)
    (lo := (42178777 / 200000000)) (hi := (105446943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40493) = 1/(40493 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105446943 / 500000000) (-42178777 / 200000000) (Real.log (40493 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174338107 / 1000000000) ≤ -Real.log (500000 / 595229) ∧
    -Real.log (500000 / 595229) ≤ (43584527 / 250000000) := by
  have h := checkLog_sound (w := (95229 / 1095229)) (n := 12)
    (lo := (174338107 / 1000000000)) (hi := (43584527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595229 / 500000) = 1/(500000 / 595229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174338107 / 1000000000) (43584527 / 250000000) (Real.log (595229 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (595229 / 500000) = -Real.log (500000 / 595229) := by
    rw [show ((595229 / 500000) : ℝ) = ((500000 / 595229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211286623 / 1000000000) ≤ -Real.log (404771 / 500000) ∧
    -Real.log (404771 / 500000) ≤ (6602707 / 31250000) := by
  have h := checkLog_sound (w := (95229 / 904771)) (n := 12)
    (lo := (211286623 / 1000000000)) (hi := (6602707 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404771) = 1/(404771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6602707 / 31250000) (-211286623 / 1000000000) (Real.log (404771 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (778475991 / 1000000000) ≤ -Real.log (125000000000 / 272268777157) ∧
    -Real.log (125000000000 / 272268777157) ≤ (778475993 / 1000000000) := by
  have h := checkLog_sound (w := (22268777157 / 522268777157)) (n := 12)
    (lo := (85328811 / 1000000000)) (hi := (21332203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272268777157 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272268777157 / 250000000000) = 1/(125000000000 / 272268777157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (778475991 / 1000000000) (778475993 / 1000000000) (Real.log (272268777157 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (272268777157 / 125000000000) = -Real.log (125000000000 / 272268777157) := by
    rw [show ((272268777157 / 125000000000) : ℝ) = ((125000000000 / 272268777157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155966981 / 200000000) ≤ -Real.log (100000000000 / 218111214663) ∧
    -Real.log (100000000000 / 218111214663) ≤ (779834907 / 1000000000) := by
  have h := checkLog_sound (w := (18111214663 / 418111214663)) (n := 12)
    (lo := (3467509 / 40000000)) (hi := (43343863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218111214663 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218111214663 / 200000000000) = 1/(100000000000 / 218111214663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (155966981 / 200000000) (779834907 / 1000000000) (Real.log (218111214663 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (218111214663 / 100000000000) = -Real.log (100000000000 / 218111214663) := by
    rw [show ((218111214663 / 100000000000) : ℝ) = ((100000000000 / 218111214663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (675253 / 1250000) ≤ -Real.log (500000000000 / 858177109011) ∧
    -Real.log (500000000000 / 858177109011) ≤ (540202401 / 1000000000) := by
  have h := checkLog_sound (w := (358177109011 / 1358177109011)) (n := 12)
    (lo := (675253 / 1250000)) (hi := (540202401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858177109011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858177109011 / 500000000000) = 1/(500000000000 / 858177109011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675253 / 1250000) (540202401 / 1000000000) (Real.log (858177109011 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (858177109011 / 500000000000) = -Real.log (500000000000 / 858177109011) := by
    rw [show ((858177109011 / 500000000000) : ℝ) = ((500000000000 / 858177109011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (270556947 / 500000000) ≤ -Real.log (500000000000 / 858959689179) ∧
    -Real.log (500000000000 / 858959689179) ≤ (108222779 / 200000000) := by
  have h := checkLog_sound (w := (358959689179 / 1358959689179)) (n := 12)
    (lo := (270556947 / 500000000)) (hi := (108222779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858959689179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858959689179 / 500000000000) = 1/(500000000000 / 858959689179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (270556947 / 500000000) (108222779 / 200000000) (Real.log (858959689179 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (858959689179 / 500000000000) = -Real.log (500000000000 / 858959689179) := by
    rw [show ((858959689179 / 500000000000) : ℝ) = ((500000000000 / 858959689179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (384964833 / 1000000000) ≤ -Real.log (125000000000 / 183695330057) ∧
    -Real.log (125000000000 / 183695330057) ≤ (192482417 / 500000000) := by
  have h := checkLog_sound (w := (58695330057 / 308695330057)) (n := 12)
    (lo := (384964833 / 1000000000)) (hi := (192482417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183695330057 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183695330057 / 125000000000) = 1/(125000000000 / 183695330057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (384964833 / 1000000000) (192482417 / 500000000) (Real.log (183695330057 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183695330057 / 125000000000) = -Real.log (125000000000 / 183695330057) := by
    rw [show ((183695330057 / 125000000000) : ℝ) = ((125000000000 / 183695330057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38562473 / 100000000) ≤ -Real.log (250000000000 / 367633180243) ∧
    -Real.log (250000000000 / 367633180243) ≤ (385624731 / 1000000000) := by
  have h := checkLog_sound (w := (117633180243 / 617633180243)) (n := 12)
    (lo := (38562473 / 100000000)) (hi := (385624731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367633180243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367633180243 / 250000000000) = 1/(250000000000 / 367633180243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38562473 / 100000000) (385624731 / 1000000000) (Real.log (367633180243 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (367633180243 / 250000000000) = -Real.log (250000000000 / 367633180243) := by
    rw [show ((367633180243 / 250000000000) : ℝ) = ((250000000000 / 367633180243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9237129 / 250000000) ≤ -Real.log (240931437559 / 250000000000) ∧
    -Real.log (240931437559 / 250000000000) ≤ (36948517 / 1000000000) := by
  have h := checkLog_sound (w := (9068562441 / 490931437559)) (n := 12)
    (lo := (9237129 / 250000000)) (hi := (36948517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240931437559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240931437559) = 1/(240931437559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-36948517 / 1000000000) (-9237129 / 250000000) (Real.log (240931437559 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18411469 / 500000000) ≤ -Real.log (2409616951 / 2500000000) ∧
    -Real.log (2409616951 / 2500000000) ≤ (36822939 / 1000000000) := by
  have h := checkLog_sound (w := (90383049 / 4909616951)) (n := 12)
    (lo := (18411469 / 500000000)) (hi := (36822939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2409616951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2409616951) = 1/(2409616951 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36822939 / 1000000000) (-18411469 / 500000000) (Real.log (2409616951 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell206
