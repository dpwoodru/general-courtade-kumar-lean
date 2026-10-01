import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell207
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

theorem reflection_log_1_neg : (316178417 / 1000000000) ≤ -Real.log (320 / 439) ∧
    -Real.log (320 / 439) ≤ (158089209 / 500000000) := by
  have h := checkLog_sound (w := (119 / 759)) (n := 12)
    (lo := (316178417 / 1000000000)) (hi := (158089209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439 / 320) = 1/(320 / 439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (316178417 / 1000000000) (158089209 / 500000000) (Real.log (439 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (439 / 320) = -Real.log (320 / 439) := by
    rw [show ((439 / 320) : ℝ) = ((320 / 439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (465016087 / 1000000000) ≤ -Real.log (201 / 320) ∧
    -Real.log (201 / 320) ≤ (58127011 / 125000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 201) = 1/(201 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58127011 / 125000000) (-465016087 / 1000000000) (Real.log (201 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157875609 / 500000000) ≤ -Real.log (5120 / 7021) ∧
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


theorem reflection_log_3 : Bounds (157875609 / 500000000) (315751219 / 1000000000) (Real.log (7021 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7021 / 5120) = -Real.log (5120 / 7021) := by
    rw [show ((7021 / 5120) : ℝ) = ((5120 / 7021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232041843 / 500000000) ≤ -Real.log (3219 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-464083687 / 1000000000) (-232041843 / 500000000) (Real.log (3219 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5859821 / 25000000) ≤ -Real.log (1000000 / 1264141) ∧
    -Real.log (1000000 / 1264141) ≤ (234392841 / 1000000000) := by
  have h := checkLog_sound (w := (264141 / 2264141)) (n := 12)
    (lo := (5859821 / 25000000)) (hi := (234392841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264141 / 1000000) = 1/(1000000 / 1264141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5859821 / 25000000) (234392841 / 1000000000) (Real.log (1264141 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1264141 / 1000000) = -Real.log (1000000 / 1264141) := by
    rw [show ((1264141 / 1000000) : ℝ) = ((1000000 / 1264141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153358377 / 500000000) ≤ -Real.log (735859 / 1000000) ∧
    -Real.log (735859 / 1000000) ≤ (61343351 / 200000000) := by
  have h := checkLog_sound (w := (264141 / 1735859)) (n := 12)
    (lo := (153358377 / 500000000)) (hi := (61343351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735859) = 1/(735859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-61343351 / 200000000) (-153358377 / 500000000) (Real.log (735859 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (234728189 / 1000000000) ≤ -Real.log (200000 / 252913) ∧
    -Real.log (200000 / 252913) ≤ (23472819 / 100000000) := by
  have h := checkLog_sound (w := (52913 / 452913)) (n := 12)
    (lo := (234728189 / 1000000000)) (hi := (23472819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252913 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252913 / 200000) = 1/(200000 / 252913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (234728189 / 1000000000) (23472819 / 100000000) (Real.log (252913 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (252913 / 200000) = -Real.log (200000 / 252913) := by
    rw [show ((252913 / 200000) : ℝ) = ((200000 / 252913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153646559 / 500000000) ≤ -Real.log (147087 / 200000) ∧
    -Real.log (147087 / 200000) ≤ (307293119 / 1000000000) := by
  have h := checkLog_sound (w := (52913 / 347087)) (n := 12)
    (lo := (153646559 / 500000000)) (hi := (307293119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147087) = 1/(147087 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307293119 / 1000000000) (-153646559 / 500000000) (Real.log (147087 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174337267 / 1000000000) ≤ -Real.log (1000000 / 1190457) ∧
    -Real.log (1000000 / 1190457) ≤ (43584317 / 250000000) := by
  have h := checkLog_sound (w := (190457 / 2190457)) (n := 12)
    (lo := (174337267 / 1000000000)) (hi := (43584317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190457 / 1000000) = 1/(1000000 / 1190457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174337267 / 1000000000) (43584317 / 250000000) (Real.log (1190457 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1190457 / 1000000) = -Real.log (1000000 / 1190457) := by
    rw [show ((1190457 / 1000000) : ℝ) = ((1000000 / 1190457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52821347 / 250000000) ≤ -Real.log (809543 / 1000000) ∧
    -Real.log (809543 / 1000000) ≤ (211285389 / 1000000000) := by
  have h := checkLog_sound (w := (190457 / 1809543)) (n := 12)
    (lo := (52821347 / 250000000)) (hi := (211285389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809543) = 1/(809543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-211285389 / 1000000000) (-52821347 / 250000000) (Real.log (809543 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34920703 / 200000000) ≤ -Real.log (500000 / 595387) ∧
    -Real.log (500000 / 595387) ≤ (43650879 / 250000000) := by
  have h := checkLog_sound (w := (95387 / 1095387)) (n := 12)
    (lo := (34920703 / 200000000)) (hi := (43650879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595387 / 500000) = 1/(500000 / 595387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34920703 / 200000000) (43650879 / 250000000) (Real.log (595387 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (595387 / 500000) = -Real.log (500000 / 595387) := by
    rw [show ((595387 / 500000) : ℝ) = ((500000 / 595387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211677043 / 1000000000) ≤ -Real.log (404613 / 500000) ∧
    -Real.log (404613 / 500000) ≤ (52919261 / 250000000) := by
  have h := checkLog_sound (w := (95387 / 904613)) (n := 12)
    (lo := (211677043 / 1000000000)) (hi := (52919261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404613) = 1/(404613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-52919261 / 250000000) (-211677043 / 1000000000) (Real.log (404613 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155966981 / 200000000) ≤ -Real.log (250000000000 / 545278036657) ∧
    -Real.log (250000000000 / 545278036657) ≤ (779834907 / 1000000000) := by
  have h := checkLog_sound (w := (45278036657 / 1045278036657)) (n := 12)
    (lo := (3467509 / 40000000)) (hi := (43343863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545278036657 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(545278036657 / 500000000000) = 1/(250000000000 / 545278036657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155966981 / 200000000) (779834907 / 1000000000) (Real.log (545278036657 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (545278036657 / 250000000000) = -Real.log (250000000000 / 545278036657) := by
    rw [show ((545278036657 / 250000000000) : ℝ) = ((250000000000 / 545278036657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97649313 / 125000000) ≤ -Real.log (125000000000 / 273009950249) ∧
    -Real.log (125000000000 / 273009950249) ≤ (390597253 / 500000000) := by
  have h := checkLog_sound (w := (23009950249 / 523009950249)) (n := 12)
    (lo := (22011831 / 250000000)) (hi := (3521893 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273009950249 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273009950249 / 250000000000) = 1/(125000000000 / 273009950249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (97649313 / 125000000) (390597253 / 500000000) (Real.log (273009950249 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (273009950249 / 125000000000) = -Real.log (125000000000 / 273009950249) := by
    rw [show ((273009950249 / 125000000000) : ℝ) = ((125000000000 / 273009950249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (270554797 / 500000000) ≤ -Real.log (100000000000 / 171791199129) ∧
    -Real.log (100000000000 / 171791199129) ≤ (108221919 / 200000000) := by
  have h := checkLog_sound (w := (71791199129 / 271791199129)) (n := 12)
    (lo := (270554797 / 500000000)) (hi := (108221919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171791199129 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171791199129 / 100000000000) = 1/(100000000000 / 171791199129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (270554797 / 500000000) (108221919 / 200000000) (Real.log (171791199129 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (171791199129 / 100000000000) = -Real.log (100000000000 / 171791199129) := by
    rw [show ((171791199129 / 100000000000) : ℝ) = ((100000000000 / 171791199129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (542021307 / 1000000000) ≤ -Real.log (500000000000 / 859739473917) ∧
    -Real.log (500000000000 / 859739473917) ≤ (135505327 / 250000000) := by
  have h := checkLog_sound (w := (359739473917 / 1359739473917)) (n := 12)
    (lo := (542021307 / 1000000000)) (hi := (135505327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859739473917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859739473917 / 500000000000) = 1/(500000000000 / 859739473917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (542021307 / 1000000000) (135505327 / 250000000) (Real.log (859739473917 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (859739473917 / 500000000000) = -Real.log (500000000000 / 859739473917) := by
    rw [show ((859739473917 / 500000000000) : ℝ) = ((500000000000 / 859739473917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (77124531 / 200000000) ≤ -Real.log (125000000000 / 183816208651) ∧
    -Real.log (125000000000 / 183816208651) ≤ (3012677 / 7812500) := by
  have h := checkLog_sound (w := (58816208651 / 308816208651)) (n := 12)
    (lo := (77124531 / 200000000)) (hi := (3012677 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183816208651 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183816208651 / 125000000000) = 1/(125000000000 / 183816208651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77124531 / 200000000) (3012677 / 7812500) (Real.log (183816208651 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183816208651 / 125000000000) = -Real.log (125000000000 / 183816208651) := by
    rw [show ((183816208651 / 125000000000) : ℝ) = ((125000000000 / 183816208651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (386280559 / 1000000000) ≤ -Real.log (500000000000 / 735748727797) ∧
    -Real.log (500000000000 / 735748727797) ≤ (4828507 / 12500000) := by
  have h := checkLog_sound (w := (235748727797 / 1235748727797)) (n := 12)
    (lo := (386280559 / 1000000000)) (hi := (4828507 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735748727797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735748727797 / 500000000000) = 1/(500000000000 / 735748727797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (386280559 / 1000000000) (4828507 / 12500000) (Real.log (735748727797 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (735748727797 / 500000000000) = -Real.log (500000000000 / 735748727797) := by
    rw [show ((735748727797 / 500000000000) : ℝ) = ((500000000000 / 735748727797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37073527 / 1000000000) ≤ -Real.log (240901320231 / 250000000000) ∧
    -Real.log (240901320231 / 250000000000) ≤ (4634191 / 125000000) := by
  have h := checkLog_sound (w := (9098679769 / 490901320231)) (n := 12)
    (lo := (37073527 / 1000000000)) (hi := (4634191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240901320231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240901320231) = 1/(240901320231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4634191 / 125000000) (-37073527 / 1000000000) (Real.log (240901320231 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36948121 / 1000000000) ≤ -Real.log (963726131151 / 1000000000000) ∧
    -Real.log (963726131151 / 1000000000000) ≤ (18474061 / 500000000) := by
  have h := checkLog_sound (w := (36273868849 / 1963726131151)) (n := 12)
    (lo := (36948121 / 1000000000)) (hi := (18474061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963726131151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963726131151) = 1/(963726131151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18474061 / 500000000) (-36948121 / 1000000000) (Real.log (963726131151 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell207
