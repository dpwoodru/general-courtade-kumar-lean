import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell048
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

theorem reflection_log_1_neg : (24585249 / 100000000) ≤ -Real.log (5120 / 6547) ∧
    -Real.log (5120 / 6547) ≤ (245852491 / 1000000000) := by
  have h := checkLog_sound (w := (1427 / 11667)) (n := 12)
    (lo := (24585249 / 100000000)) (hi := (245852491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6547 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6547 / 5120) = 1/(5120 / 6547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24585249 / 100000000) (245852491 / 1000000000) (Real.log (6547 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6547 / 5120) = -Real.log (5120 / 6547) := by
    rw [show ((6547 / 5120) : ℝ) = ((5120 / 6547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (326715303 / 1000000000) ≤ -Real.log (3693 / 5120) ∧
    -Real.log (3693 / 5120) ≤ (40839413 / 125000000) := by
  have h := checkLog_sound (w := (1427 / 8813)) (n := 12)
    (lo := (326715303 / 1000000000)) (hi := (40839413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3693) = 1/(3693 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40839413 / 125000000) (-326715303 / 1000000000) (Real.log (3693 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3067427 / 12500000) ≤ -Real.log (320 / 409) ∧
    -Real.log (320 / 409) ≤ (245394161 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 729)) (n := 12)
    (lo := (3067427 / 12500000)) (hi := (245394161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409 / 320) = 1/(320 / 409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3067427 / 12500000) (245394161 / 1000000000) (Real.log (409 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (409 / 320) = -Real.log (320 / 409) := by
    rw [show ((409 / 320) : ℝ) = ((320 / 409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65180657 / 200000000) ≤ -Real.log (231 / 320) ∧
    -Real.log (231 / 320) ≤ (162951643 / 500000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 231) = 1/(231 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-162951643 / 500000000) (-65180657 / 200000000) (Real.log (231 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18008489 / 100000000) ≤ -Real.log (1000000 / 1197319) ∧
    -Real.log (1000000 / 1197319) ≤ (180084891 / 1000000000) := by
  have h := checkLog_sound (w := (197319 / 2197319)) (n := 12)
    (lo := (18008489 / 100000000)) (hi := (180084891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197319 / 1000000) = 1/(1000000 / 1197319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18008489 / 100000000) (180084891 / 1000000000) (Real.log (1197319 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1197319 / 1000000) = -Real.log (1000000 / 1197319) := by
    rw [show ((1197319 / 1000000) : ℝ) = ((1000000 / 1197319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13737369 / 62500000) ≤ -Real.log (802681 / 1000000) ∧
    -Real.log (802681 / 1000000) ≤ (43959581 / 200000000) := by
  have h := checkLog_sound (w := (197319 / 1802681)) (n := 12)
    (lo := (13737369 / 62500000)) (hi := (43959581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802681) = 1/(802681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-43959581 / 200000000) (-13737369 / 62500000) (Real.log (802681 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180434777 / 1000000000) ≤ -Real.log (500000 / 598869) ∧
    -Real.log (500000 / 598869) ≤ (90217389 / 500000000) := by
  have h := checkLog_sound (w := (98869 / 1098869)) (n := 12)
    (lo := (180434777 / 1000000000)) (hi := (90217389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598869 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598869 / 500000) = 1/(500000 / 598869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (180434777 / 1000000000) (90217389 / 500000000) (Real.log (598869 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (598869 / 500000) = -Real.log (500000 / 598869) := by
    rw [show ((598869 / 500000) : ℝ) = ((500000 / 598869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (220320041 / 1000000000) ≤ -Real.log (401131 / 500000) ∧
    -Real.log (401131 / 500000) ≤ (110160021 / 500000000) := by
  have h := checkLog_sound (w := (98869 / 901131)) (n := 12)
    (lo := (220320041 / 1000000000)) (hi := (110160021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401131) = 1/(401131 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110160021 / 500000000) (-220320041 / 1000000000) (Real.log (401131 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131946261 / 1000000000) ≤ -Real.log (1000000 / 1141047) ∧
    -Real.log (1000000 / 1141047) ≤ (65973131 / 500000000) := by
  have h := checkLog_sound (w := (141047 / 2141047)) (n := 12)
    (lo := (131946261 / 1000000000)) (hi := (65973131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141047 / 1000000) = 1/(1000000 / 1141047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131946261 / 1000000000) (65973131 / 500000000) (Real.log (1141047 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141047 / 1000000) = -Real.log (1000000 / 1141047) := by
    rw [show ((1141047 / 1000000) : ℝ) = ((1000000 / 1141047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152041073 / 1000000000) ≤ -Real.log (858953 / 1000000) ∧
    -Real.log (858953 / 1000000) ≤ (76020537 / 500000000) := by
  have h := checkLog_sound (w := (141047 / 1858953)) (n := 12)
    (lo := (152041073 / 1000000000)) (hi := (76020537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858953) = 1/(858953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76020537 / 500000000) (-152041073 / 1000000000) (Real.log (858953 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33053819 / 250000000) ≤ -Real.log (500000 / 570677) ∧
    -Real.log (500000 / 570677) ≤ (132215277 / 1000000000) := by
  have h := checkLog_sound (w := (70677 / 1070677)) (n := 12)
    (lo := (33053819 / 250000000)) (hi := (132215277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570677 / 500000) = 1/(500000 / 570677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33053819 / 250000000) (132215277 / 1000000000) (Real.log (570677 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570677 / 500000) = -Real.log (500000 / 570677) := by
    rw [show ((570677 / 500000) : ℝ) = ((500000 / 570677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152398549 / 1000000000) ≤ -Real.log (429323 / 500000) ∧
    -Real.log (429323 / 500000) ≤ (3047971 / 20000000) := by
  have h := checkLog_sound (w := (70677 / 929323)) (n := 12)
    (lo := (152398549 / 1000000000)) (hi := (3047971 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429323) = 1/(429323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3047971 / 20000000) (-152398549 / 1000000000) (Real.log (429323 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (114259489 / 200000000) ≤ -Real.log (500000000000 / 885281385281) ∧
    -Real.log (500000000000 / 885281385281) ≤ (285648723 / 500000000) := by
  have h := checkLog_sound (w := (385281385281 / 1385281385281)) (n := 12)
    (lo := (114259489 / 200000000)) (hi := (285648723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885281385281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885281385281 / 500000000000) = 1/(500000000000 / 885281385281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (114259489 / 200000000) (285648723 / 500000000) (Real.log (885281385281 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (885281385281 / 500000000000) = -Real.log (500000000000 / 885281385281) := by
    rw [show ((885281385281 / 500000000000) : ℝ) = ((500000000000 / 885281385281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (572567793 / 1000000000) ≤ -Real.log (31250000000 / 55400419713) ∧
    -Real.log (31250000000 / 55400419713) ≤ (286283897 / 500000000) := by
  have h := checkLog_sound (w := (24150419713 / 86650419713)) (n := 12)
    (lo := (572567793 / 1000000000)) (hi := (286283897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55400419713 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55400419713 / 31250000000) = 1/(31250000000 / 55400419713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (572567793 / 1000000000) (286283897 / 500000000) (Real.log (55400419713 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (55400419713 / 31250000000) = -Real.log (31250000000 / 55400419713) := by
    rw [show ((55400419713 / 31250000000) : ℝ) = ((31250000000 / 55400419713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (199941397 / 500000000) ≤ -Real.log (100000000000 / 149164985841) ∧
    -Real.log (100000000000 / 149164985841) ≤ (79976559 / 200000000) := by
  have h := checkLog_sound (w := (49164985841 / 249164985841)) (n := 12)
    (lo := (199941397 / 500000000)) (hi := (79976559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149164985841 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149164985841 / 100000000000) = 1/(100000000000 / 149164985841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (199941397 / 500000000) (79976559 / 200000000) (Real.log (149164985841 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149164985841 / 100000000000) = -Real.log (100000000000 / 149164985841) := by
    rw [show ((149164985841 / 100000000000) : ℝ) = ((100000000000 / 149164985841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (400754819 / 1000000000) ≤ -Real.log (500000000000 / 746475590269) ∧
    -Real.log (500000000000 / 746475590269) ≤ (20037741 / 50000000) := by
  have h := checkLog_sound (w := (246475590269 / 1246475590269)) (n := 12)
    (lo := (400754819 / 1000000000)) (hi := (20037741 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746475590269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746475590269 / 500000000000) = 1/(500000000000 / 746475590269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (400754819 / 1000000000) (20037741 / 50000000) (Real.log (746475590269 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (746475590269 / 500000000000) = -Real.log (500000000000 / 746475590269) := by
    rw [show ((746475590269 / 500000000000) : ℝ) = ((500000000000 / 746475590269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (56797467 / 200000000) ≤ -Real.log (125000000000 / 166052013323) ∧
    -Real.log (125000000000 / 166052013323) ≤ (35498417 / 125000000) := by
  have h := checkLog_sound (w := (41052013323 / 291052013323)) (n := 12)
    (lo := (56797467 / 200000000)) (hi := (35498417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166052013323 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166052013323 / 125000000000) = 1/(125000000000 / 166052013323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56797467 / 200000000) (35498417 / 125000000) (Real.log (166052013323 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (166052013323 / 125000000000) = -Real.log (125000000000 / 166052013323) := by
    rw [show ((166052013323 / 125000000000) : ℝ) = ((125000000000 / 166052013323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11384553 / 40000000) ≤ -Real.log (250000000000 / 332312151923) ∧
    -Real.log (250000000000 / 332312151923) ≤ (142306913 / 500000000) := by
  have h := checkLog_sound (w := (82312151923 / 582312151923)) (n := 12)
    (lo := (11384553 / 40000000)) (hi := (142306913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332312151923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332312151923 / 250000000000) = 1/(250000000000 / 332312151923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11384553 / 40000000) (142306913 / 500000000) (Real.log (332312151923 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (332312151923 / 250000000000) = -Real.log (250000000000 / 332312151923) := by
    rw [show ((332312151923 / 250000000000) : ℝ) = ((250000000000 / 332312151923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2522909 / 125000000) ≤ -Real.log (245004761671 / 250000000000) ∧
    -Real.log (245004761671 / 250000000000) ≤ (20183273 / 1000000000) := by
  have h := checkLog_sound (w := (4995238329 / 495004761671)) (n := 12)
    (lo := (2522909 / 125000000)) (hi := (20183273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245004761671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245004761671) = 1/(245004761671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20183273 / 1000000000) (-2522909 / 125000000) (Real.log (245004761671 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20094811 / 1000000000) ≤ -Real.log (980105743791 / 1000000000000) ∧
    -Real.log (980105743791 / 1000000000000) ≤ (5023703 / 250000000) := by
  have h := checkLog_sound (w := (19894256209 / 1980105743791)) (n := 12)
    (lo := (20094811 / 1000000000)) (hi := (5023703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980105743791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980105743791) = 1/(980105743791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5023703 / 250000000) (-20094811 / 1000000000) (Real.log (980105743791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell048
