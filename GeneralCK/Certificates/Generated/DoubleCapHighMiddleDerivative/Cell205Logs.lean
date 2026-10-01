import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell205
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

theorem reflection_log_1_neg : (157661919 / 500000000) ≤ -Real.log (2560 / 3509) ∧
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


theorem reflection_log_1 : Bounds (157661919 / 500000000) (315323839 / 1000000000) (Real.log (3509 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3509 / 2560) = -Real.log (2560 / 3509) := by
    rw [show ((3509 / 2560) : ℝ) = ((2560 / 3509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (231576077 / 500000000) ≤ -Real.log (1611 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-92630431 / 200000000) (-231576077 / 500000000) (Real.log (1611 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157448137 / 500000000) ≤ -Real.log (1024 / 1403) ∧
    -Real.log (1024 / 1403) ≤ (12595851 / 40000000) := by
  have h := checkLog_sound (w := (379 / 2427)) (n := 12)
    (lo := (157448137 / 500000000)) (hi := (12595851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1024) = 1/(1024 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157448137 / 500000000) (12595851 / 40000000) (Real.log (1403 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1403 / 1024) = -Real.log (1024 / 1403) := by
    rw [show ((1403 / 1024) : ℝ) = ((1024 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28888843 / 62500000) ≤ -Real.log (645 / 1024) ∧
    -Real.log (645 / 1024) ≤ (462221489 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1669)) (n := 12)
    (lo := (28888843 / 62500000)) (hi := (462221489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 645) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 645) = 1/(645 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-462221489 / 1000000000) (-28888843 / 62500000) (Real.log (645 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23372497 / 100000000) ≤ -Real.log (1000000 / 1263297) ∧
    -Real.log (1000000 / 1263297) ≤ (233724971 / 1000000000) := by
  have h := checkLog_sound (w := (263297 / 2263297)) (n := 12)
    (lo := (23372497 / 100000000)) (hi := (233724971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263297 / 1000000) = 1/(1000000 / 1263297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23372497 / 100000000) (233724971 / 1000000000) (Real.log (1263297 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1263297 / 1000000) = -Real.log (1000000 / 1263297) := by
    rw [show ((1263297 / 1000000) : ℝ) = ((1000000 / 1263297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (305570453 / 1000000000) ≤ -Real.log (736703 / 1000000) ∧
    -Real.log (736703 / 1000000) ≤ (152785227 / 500000000) := by
  have h := checkLog_sound (w := (263297 / 1736703)) (n := 12)
    (lo := (305570453 / 1000000000)) (hi := (152785227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 736703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 736703) = 1/(736703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-152785227 / 500000000) (-305570453 / 1000000000) (Real.log (736703 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (29257469 / 125000000) ≤ -Real.log (25000 / 31593) ∧
    -Real.log (25000 / 31593) ≤ (234059753 / 1000000000) := by
  have h := checkLog_sound (w := (6593 / 56593)) (n := 12)
    (lo := (29257469 / 125000000)) (hi := (234059753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31593 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31593 / 25000) = 1/(25000 / 31593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (29257469 / 125000000) (234059753 / 1000000000) (Real.log (31593 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (31593 / 25000) = -Real.log (25000 / 31593) := by
    rw [show ((31593 / 25000) : ℝ) = ((25000 / 31593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (306144797 / 1000000000) ≤ -Real.log (18407 / 25000) ∧
    -Real.log (18407 / 25000) ≤ (153072399 / 500000000) := by
  have h := checkLog_sound (w := (6593 / 43407)) (n := 12)
    (lo := (306144797 / 1000000000)) (hi := (153072399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18407) = 1/(18407 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-153072399 / 500000000) (-306144797 / 1000000000) (Real.log (18407 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (173805397 / 1000000000) ≤ -Real.log (15625 / 18591) ∧
    -Real.log (15625 / 18591) ≤ (86902699 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 17108)) (n := 12)
    (lo := (173805397 / 1000000000)) (hi := (86902699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18591 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18591 / 15625) = 1/(15625 / 18591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (173805397 / 1000000000) (86902699 / 500000000) (Real.log (18591 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18591 / 15625) = -Real.log (15625 / 18591) := by
    rw [show ((18591 / 15625) : ℝ) = ((15625 / 18591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21050377 / 100000000) ≤ -Real.log (12659 / 15625) ∧
    -Real.log (12659 / 15625) ≤ (210503771 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 14142)) (n := 12)
    (lo := (21050377 / 100000000)) (hi := (210503771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12659) = 1/(12659 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-210503771 / 1000000000) (-21050377 / 100000000) (Real.log (12659 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174071787 / 1000000000) ≤ -Real.log (1000000 / 1190141) ∧
    -Real.log (1000000 / 1190141) ≤ (43517947 / 250000000) := by
  have h := checkLog_sound (w := (190141 / 2190141)) (n := 12)
    (lo := (174071787 / 1000000000)) (hi := (43517947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190141 / 1000000) = 1/(1000000 / 1190141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174071787 / 1000000000) (43517947 / 250000000) (Real.log (1190141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1190141 / 1000000) = -Real.log (1000000 / 1190141) := by
    rw [show ((1190141 / 1000000) : ℝ) = ((1000000 / 1190141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2636189 / 12500000) ≤ -Real.log (809859 / 1000000) ∧
    -Real.log (809859 / 1000000) ≤ (210895121 / 1000000000) := by
  have h := checkLog_sound (w := (190141 / 1809859)) (n := 12)
    (lo := (2636189 / 12500000)) (hi := (210895121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809859) = 1/(809859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210895121 / 1000000000) (-2636189 / 12500000) (Real.log (809859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (388558881 / 500000000) ≤ -Real.log (62500000000 / 135949612403) ∧
    -Real.log (62500000000 / 135949612403) ≤ (194279441 / 250000000) := by
  have h := checkLog_sound (w := (10949612403 / 260949612403)) (n := 12)
    (lo := (41985291 / 500000000)) (hi := (83970583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135949612403 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(135949612403 / 125000000000) = 1/(62500000000 / 135949612403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (388558881 / 500000000) (194279441 / 250000000) (Real.log (135949612403 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (135949612403 / 62500000000) = -Real.log (62500000000 / 135949612403) := by
    rw [show ((135949612403 / 62500000000) : ℝ) = ((62500000000 / 135949612403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (778475991 / 1000000000) ≤ -Real.log (500000000000 / 1089075108629) ∧
    -Real.log (500000000000 / 1089075108629) ≤ (778475993 / 1000000000) := by
  have h := checkLog_sound (w := (89075108629 / 2089075108629)) (n := 12)
    (lo := (85328811 / 1000000000)) (hi := (21332203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089075108629 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089075108629 / 1000000000000) = 1/(500000000000 / 1089075108629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (778475991 / 1000000000) (778475993 / 1000000000) (Real.log (1089075108629 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1089075108629 / 500000000000) = -Real.log (500000000000 / 1089075108629) := by
    rw [show ((1089075108629 / 500000000000) : ℝ) = ((500000000000 / 1089075108629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (539295423 / 1000000000) ≤ -Real.log (31250000000 / 53587444669) ∧
    -Real.log (31250000000 / 53587444669) ≤ (8426491 / 15625000) := by
  have h := checkLog_sound (w := (22337444669 / 84837444669)) (n := 12)
    (lo := (539295423 / 1000000000)) (hi := (8426491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53587444669 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53587444669 / 31250000000) = 1/(31250000000 / 53587444669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (539295423 / 1000000000) (8426491 / 15625000) (Real.log (53587444669 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53587444669 / 31250000000) = -Real.log (31250000000 / 53587444669) := by
    rw [show ((53587444669 / 31250000000) : ℝ) = ((31250000000 / 53587444669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10804091 / 20000000) ≤ -Real.log (500000000000 / 858178953659) ∧
    -Real.log (500000000000 / 858178953659) ≤ (540204551 / 1000000000) := by
  have h := checkLog_sound (w := (358178953659 / 1358178953659)) (n := 12)
    (lo := (10804091 / 20000000)) (hi := (540204551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858178953659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858178953659 / 500000000000) = 1/(500000000000 / 858178953659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (10804091 / 20000000) (540204551 / 1000000000) (Real.log (858178953659 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (858178953659 / 500000000000) = -Real.log (500000000000 / 858178953659) := by
    rw [show ((858178953659 / 500000000000) : ℝ) = ((500000000000 / 858178953659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (384309167 / 1000000000) ≤ -Real.log (500000000000 / 734299707717) ∧
    -Real.log (500000000000 / 734299707717) ≤ (24019323 / 62500000) := by
  have h := checkLog_sound (w := (234299707717 / 1234299707717)) (n := 12)
    (lo := (384309167 / 1000000000)) (hi := (24019323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734299707717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734299707717 / 500000000000) = 1/(500000000000 / 734299707717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (384309167 / 1000000000) (24019323 / 62500000) (Real.log (734299707717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (734299707717 / 500000000000) = -Real.log (500000000000 / 734299707717) := by
    rw [show ((734299707717 / 500000000000) : ℝ) = ((500000000000 / 734299707717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96241727 / 250000000) ≤ -Real.log (100000000000 / 146956568983) ∧
    -Real.log (100000000000 / 146956568983) ≤ (384966909 / 1000000000) := by
  have h := checkLog_sound (w := (46956568983 / 246956568983)) (n := 12)
    (lo := (96241727 / 250000000)) (hi := (384966909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146956568983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146956568983 / 100000000000) = 1/(100000000000 / 146956568983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96241727 / 250000000) (384966909 / 1000000000) (Real.log (146956568983 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (146956568983 / 100000000000) = -Real.log (100000000000 / 146956568983) := by
    rw [show ((146956568983 / 100000000000) : ℝ) = ((100000000000 / 146956568983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36823333 / 1000000000) ≤ -Real.log (963846400119 / 1000000000000) ∧
    -Real.log (963846400119 / 1000000000000) ≤ (18411667 / 500000000) := by
  have h := checkLog_sound (w := (36153599881 / 1963846400119)) (n := 12)
    (lo := (36823333 / 1000000000)) (hi := (18411667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963846400119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963846400119) = 1/(963846400119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18411667 / 500000000) (-36823333 / 1000000000) (Real.log (963846400119 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36698373 / 1000000000) ≤ -Real.log (235343469 / 244140625) ∧
    -Real.log (235343469 / 244140625) ≤ (18349187 / 500000000) := by
  have h := checkLog_sound (w := (4398578 / 239742047)) (n := 12)
    (lo := (36698373 / 1000000000)) (hi := (18349187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 235343469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 235343469) = 1/(235343469 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18349187 / 500000000) (-36698373 / 1000000000) (Real.log (235343469 / 244140625)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell205
