import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell170
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

theorem reflection_log_1_neg : (300249257 / 1000000000) ≤ -Real.log (5120 / 6913) ∧
    -Real.log (5120 / 6913) ≤ (150124629 / 500000000) := by
  have h := checkLog_sound (w := (1793 / 12033)) (n := 12)
    (lo := (300249257 / 1000000000)) (hi := (150124629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6913 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6913 / 5120) = 1/(5120 / 6913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (300249257 / 1000000000) (150124629 / 500000000) (Real.log (6913 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6913 / 5120) = -Real.log (5120 / 6913) := by
    rw [show ((6913 / 5120) : ℝ) = ((5120 / 6913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (215541721 / 500000000) ≤ -Real.log (3327 / 5120) ∧
    -Real.log (3327 / 5120) ≤ (431083443 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 8447)) (n := 12)
    (lo := (215541721 / 500000000)) (hi := (431083443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3327) = 1/(3327 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-431083443 / 1000000000) (-215541721 / 500000000) (Real.log (3327 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (149907599 / 500000000) ≤ -Real.log (512 / 691) ∧
    -Real.log (512 / 691) ≤ (299815199 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1203)) (n := 12)
    (lo := (149907599 / 500000000)) (hi := (299815199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 512) = 1/(512 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (149907599 / 500000000) (299815199 / 1000000000) (Real.log (691 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (691 / 512) = -Real.log (512 / 691) := by
    rw [show ((691 / 512) : ℝ) = ((512 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86036427 / 200000000) ≤ -Real.log (333 / 512) ∧
    -Real.log (333 / 512) ≤ (53772767 / 125000000) := by
  have h := checkLog_sound (w := (179 / 845)) (n := 12)
    (lo := (86036427 / 200000000)) (hi := (53772767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 333) = 1/(333 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-53772767 / 125000000) (-86036427 / 200000000) (Real.log (333 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (110986633 / 500000000) ≤ -Real.log (500000 / 624269) ∧
    -Real.log (500000 / 624269) ≤ (221973267 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 1124269)) (n := 12)
    (lo := (110986633 / 500000000)) (hi := (221973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624269 / 500000) = 1/(500000 / 624269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (110986633 / 500000000) (221973267 / 1000000000) (Real.log (624269 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624269 / 500000) = -Real.log (500000 / 624269) := by
    rw [show ((624269 / 500000) : ℝ) = ((500000 / 624269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71433659 / 250000000) ≤ -Real.log (375731 / 500000) ∧
    -Real.log (375731 / 500000) ≤ (285734637 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 875731)) (n := 12)
    (lo := (71433659 / 250000000)) (hi := (285734637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375731) = 1/(375731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-285734637 / 1000000000) (-71433659 / 250000000) (Real.log (375731 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44462241 / 200000000) ≤ -Real.log (3125 / 3903) ∧
    -Real.log (3125 / 3903) ≤ (111155603 / 500000000) := by
  have h := checkLog_sound (w := (389 / 3514)) (n := 12)
    (lo := (44462241 / 200000000)) (hi := (111155603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3903 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3903 / 3125) = 1/(3125 / 3903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44462241 / 200000000) (111155603 / 500000000) (Real.log (3903 / 3125)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3903 / 3125) = -Real.log (3125 / 3903) := by
    rw [show ((3903 / 3125) : ℝ) = ((3125 / 3903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (143148183 / 500000000) ≤ -Real.log (2347 / 3125) ∧
    -Real.log (2347 / 3125) ≤ (286296367 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2736)) (n := 12)
    (lo := (143148183 / 500000000)) (hi := (286296367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2347) = 1/(2347 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-286296367 / 1000000000) (-143148183 / 500000000) (Real.log (2347 / 3125)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41124667 / 250000000) ≤ -Real.log (500000 / 589401) ∧
    -Real.log (500000 / 589401) ≤ (164498669 / 1000000000) := by
  have h := checkLog_sound (w := (89401 / 1089401)) (n := 12)
    (lo := (41124667 / 250000000)) (hi := (164498669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589401 / 500000) = 1/(500000 / 589401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41124667 / 250000000) (164498669 / 1000000000) (Real.log (589401 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (589401 / 500000) = -Real.log (500000 / 589401) := by
    rw [show ((589401 / 500000) : ℝ) = ((500000 / 589401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196991029 / 1000000000) ≤ -Real.log (410599 / 500000) ∧
    -Real.log (410599 / 500000) ≤ (19699103 / 100000000) := by
  have h := checkLog_sound (w := (89401 / 910599)) (n := 12)
    (lo := (196991029 / 1000000000)) (hi := (19699103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410599) = 1/(410599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19699103 / 100000000) (-196991029 / 1000000000) (Real.log (410599 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164765853 / 1000000000) ≤ -Real.log (1000000 / 1179117) ∧
    -Real.log (1000000 / 1179117) ≤ (82382927 / 500000000) := by
  have h := checkLog_sound (w := (179117 / 2179117)) (n := 12)
    (lo := (164765853 / 1000000000)) (hi := (82382927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179117 / 1000000) = 1/(1000000 / 1179117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164765853 / 1000000000) (82382927 / 500000000) (Real.log (1179117 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1179117 / 1000000) = -Real.log (1000000 / 1179117) := by
    rw [show ((1179117 / 1000000) : ℝ) = ((1000000 / 1179117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6167959 / 31250000) ≤ -Real.log (820883 / 1000000) ∧
    -Real.log (820883 / 1000000) ≤ (197374689 / 1000000000) := by
  have h := checkLog_sound (w := (179117 / 1820883)) (n := 12)
    (lo := (6167959 / 31250000)) (hi := (197374689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820883) = 1/(820883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197374689 / 1000000000) (-6167959 / 31250000) (Real.log (820883 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (729997333 / 1000000000) ≤ -Real.log (500000000000 / 1037537537537) ∧
    -Real.log (500000000000 / 1037537537537) ≤ (145999467 / 200000000) := by
  have h := checkLog_sound (w := (37537537537 / 2037537537537)) (n := 12)
    (lo := (36850153 / 1000000000)) (hi := (18425077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037537537537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1037537537537 / 1000000000000) = 1/(500000000000 / 1037537537537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (729997333 / 1000000000) (145999467 / 200000000) (Real.log (1037537537537 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1037537537537 / 500000000000) = -Real.log (500000000000 / 1037537537537) := by
    rw [show ((1037537537537 / 500000000000) : ℝ) = ((500000000000 / 1037537537537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (731332699 / 1000000000) ≤ -Real.log (125000000000 / 259730988879) ∧
    -Real.log (125000000000 / 259730988879) ≤ (731332701 / 1000000000) := by
  have h := checkLog_sound (w := (9730988879 / 509730988879)) (n := 12)
    (lo := (38185519 / 1000000000)) (hi := (477319 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259730988879 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259730988879 / 250000000000) = 1/(125000000000 / 259730988879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (731332699 / 1000000000) (731332701 / 1000000000) (Real.log (259730988879 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (259730988879 / 125000000000) = -Real.log (125000000000 / 259730988879) := by
    rw [show ((259730988879 / 125000000000) : ℝ) = ((125000000000 / 259730988879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (507707903 / 1000000000) ≤ -Real.log (250000000000 / 415369639449) ∧
    -Real.log (250000000000 / 415369639449) ≤ (991617 / 1953125) := by
  have h := checkLog_sound (w := (165369639449 / 665369639449)) (n := 12)
    (lo := (507707903 / 1000000000)) (hi := (991617 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415369639449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415369639449 / 250000000000) = 1/(250000000000 / 415369639449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (507707903 / 1000000000) (991617 / 1953125) (Real.log (415369639449 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (415369639449 / 250000000000) = -Real.log (250000000000 / 415369639449) := by
    rw [show ((415369639449 / 250000000000) : ℝ) = ((250000000000 / 415369639449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (508607571 / 1000000000) ≤ -Real.log (500000000000 / 831487004687) ∧
    -Real.log (500000000000 / 831487004687) ≤ (127151893 / 250000000) := by
  have h := checkLog_sound (w := (331487004687 / 1331487004687)) (n := 12)
    (lo := (508607571 / 1000000000)) (hi := (127151893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831487004687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831487004687 / 500000000000) = 1/(500000000000 / 831487004687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (508607571 / 1000000000) (127151893 / 250000000) (Real.log (831487004687 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (831487004687 / 500000000000) = -Real.log (500000000000 / 831487004687) := by
    rw [show ((831487004687 / 500000000000) : ℝ) = ((500000000000 / 831487004687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (361489697 / 1000000000) ≤ -Real.log (500000000000 / 717733116739) ∧
    -Real.log (500000000000 / 717733116739) ≤ (180744849 / 500000000) := by
  have h := checkLog_sound (w := (217733116739 / 1217733116739)) (n := 12)
    (lo := (361489697 / 1000000000)) (hi := (180744849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717733116739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717733116739 / 500000000000) = 1/(500000000000 / 717733116739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (361489697 / 1000000000) (180744849 / 500000000) (Real.log (717733116739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (717733116739 / 500000000000) = -Real.log (500000000000 / 717733116739) := by
    rw [show ((717733116739 / 500000000000) : ℝ) = ((500000000000 / 717733116739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (181070271 / 500000000) ≤ -Real.log (125000000000 / 179550100319) ∧
    -Real.log (125000000000 / 179550100319) ≤ (362140543 / 1000000000) := by
  have h := checkLog_sound (w := (54550100319 / 304550100319)) (n := 12)
    (lo := (181070271 / 500000000)) (hi := (362140543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179550100319 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179550100319 / 125000000000) = 1/(125000000000 / 179550100319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (181070271 / 500000000) (362140543 / 1000000000) (Real.log (179550100319 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179550100319 / 125000000000) = -Real.log (125000000000 / 179550100319) := by
    rw [show ((179550100319 / 125000000000) : ℝ) = ((125000000000 / 179550100319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6521767 / 200000000) ≤ -Real.log (967917100311 / 1000000000000) ∧
    -Real.log (967917100311 / 1000000000000) ≤ (8152209 / 250000000) := by
  have h := checkLog_sound (w := (32082899689 / 1967917100311)) (n := 12)
    (lo := (6521767 / 200000000)) (hi := (8152209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967917100311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967917100311) = 1/(967917100311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8152209 / 250000000) (-6521767 / 200000000) (Real.log (967917100311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (812309 / 25000000) ≤ -Real.log (242007461199 / 250000000000) ∧
    -Real.log (242007461199 / 250000000000) ≤ (32492361 / 1000000000) := by
  have h := checkLog_sound (w := (7992538801 / 492007461199)) (n := 12)
    (lo := (812309 / 25000000)) (hi := (32492361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242007461199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242007461199) = 1/(242007461199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32492361 / 1000000000) (-812309 / 25000000) (Real.log (242007461199 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell170
