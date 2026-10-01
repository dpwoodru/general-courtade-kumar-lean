import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0104
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

theorem reflection_log_1_neg : (66006829 / 200000000) ≤ -Real.log (2560 / 3561) ∧
    -Real.log (2560 / 3561) ≤ (165017073 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 6121)) (n := 12)
    (lo := (66006829 / 200000000)) (hi := (165017073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 2560) = 1/(2560 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66006829 / 200000000) (165017073 / 500000000) (Real.log (3561 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3561 / 2560) = -Real.log (2560 / 3561) := by
    rw [show ((3561 / 2560) : ℝ) = ((2560 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (123990667 / 250000000) ≤ -Real.log (1559 / 2560) ∧
    -Real.log (1559 / 2560) ≤ (495962669 / 1000000000) := by
  have h := checkLog_sound (w := (1001 / 4119)) (n := 12)
    (lo := (123990667 / 250000000)) (hi := (495962669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1559) = 1/(1559 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-495962669 / 1000000000) (-123990667 / 250000000) (Real.log (1559 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32919133 / 100000000) ≤ -Real.log (1280 / 1779) ∧
    -Real.log (1280 / 1779) ≤ (329191331 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 3059)) (n := 12)
    (lo := (32919133 / 100000000)) (hi := (329191331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1280) = 1/(1280 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32919133 / 100000000) (329191331 / 1000000000) (Real.log (1779 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1779 / 1280) = -Real.log (1280 / 1779) := by
    rw [show ((1779 / 1280) : ℝ) = ((1280 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (494040207 / 1000000000) ≤ -Real.log (781 / 1280) ∧
    -Real.log (781 / 1280) ≤ (30877513 / 62500000) := by
  have h := checkLog_sound (w := (499 / 2061)) (n := 12)
    (lo := (494040207 / 1000000000)) (hi := (30877513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 781) = 1/(781 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30877513 / 62500000) (-494040207 / 1000000000) (Real.log (781 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115550773 / 200000000) ≤ -Real.log (1280 / 2281) ∧
    -Real.log (1280 / 2281) ≤ (288876933 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 3561)) (n := 12)
    (lo := (115550773 / 200000000)) (hi := (288876933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1280) = 1/(1280 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115550773 / 200000000) (288876933 / 500000000) (Real.log (2281 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2281 / 1280) = -Real.log (1280 / 2281) := by
    rw [show ((2281 / 1280) : ℝ) = ((1280 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1523403573 / 1000000000) ≤ -Real.log (279 / 1280) ∧
    -Real.log (279 / 1280) ≤ (190425447 / 125000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 279) = 1/(279 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190425447 / 125000000) (-1523403573 / 1000000000) (Real.log (279 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (576437787 / 1000000000) ≤ -Real.log (640 / 1139) ∧
    -Real.log (640 / 1139) ≤ (144109447 / 250000000) := by
  have h := checkLog_sound (w := (499 / 1779)) (n := 12)
    (lo := (576437787 / 1000000000)) (hi := (144109447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139 / 640) = 1/(640 / 1139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (576437787 / 1000000000) (144109447 / 250000000) (Real.log (1139 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1139 / 640) = -Real.log (640 / 1139) := by
    rw [show ((1139 / 640) : ℝ) = ((640 / 1139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (378177071 / 250000000) ≤ -Real.log (141 / 640) ∧
    -Real.log (141 / 640) ≤ (1512708287 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 141) = 1/(141 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1512708287 / 1000000000) (-378177071 / 250000000) (Real.log (141 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11289451 / 25000000) ≤ -Real.log (1000000 / 1570789) ∧
    -Real.log (1000000 / 1570789) ≤ (451578041 / 1000000000) := by
  have h := checkLog_sound (w := (570789 / 2570789)) (n := 12)
    (lo := (11289451 / 25000000)) (hi := (451578041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1570789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1570789 / 1000000) = 1/(1000000 / 1570789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11289451 / 25000000) (451578041 / 1000000000) (Real.log (1570789 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1570789 / 1000000) = -Real.log (1000000 / 1570789) := by
    rw [show ((1570789 / 1000000) : ℝ) = ((1000000 / 1570789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (422903319 / 500000000) ≤ -Real.log (429211 / 1000000) ∧
    -Real.log (429211 / 1000000) ≤ (10572583 / 12500000) := by
  have h := checkLog_sound (w := (70789 / 929211)) (n := 12)
    (lo := (76329729 / 500000000)) (hi := (152659459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 429211) = 1/(429211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10572583 / 12500000) (-422903319 / 500000000) (Real.log (429211 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (226390267 / 500000000) ≤ -Real.log (1000000 / 1572679) ∧
    -Real.log (1000000 / 1572679) ≤ (90556107 / 200000000) := by
  have h := checkLog_sound (w := (572679 / 2572679)) (n := 12)
    (lo := (226390267 / 500000000)) (hi := (90556107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1572679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1572679 / 1000000) = 1/(1000000 / 1572679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (226390267 / 500000000) (90556107 / 200000000) (Real.log (1572679 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1572679 / 1000000) = -Real.log (1000000 / 1572679) := by
    rw [show ((1572679 / 1000000) : ℝ) = ((1000000 / 1572679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (850219791 / 1000000000) ≤ -Real.log (427321 / 1000000) ∧
    -Real.log (427321 / 1000000) ≤ (850219793 / 1000000000) := by
  have h := checkLog_sound (w := (72679 / 927321)) (n := 12)
    (lo := (157072611 / 1000000000)) (hi := (39268153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 427321) = 1/(427321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-850219793 / 1000000000) (-850219791 / 1000000000) (Real.log (427321 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (917417 / 2500000) ≤ -Real.log (20000 / 28867) ∧
    -Real.log (20000 / 28867) ≤ (366966801 / 1000000000) := by
  have h := checkLog_sound (w := (8867 / 48867)) (n := 12)
    (lo := (917417 / 2500000)) (hi := (366966801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28867 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28867 / 20000) = 1/(20000 / 28867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (917417 / 2500000) (366966801 / 1000000000) (Real.log (28867 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (28867 / 20000) = -Real.log (20000 / 28867) := by
    rw [show ((28867 / 20000) : ℝ) = ((20000 / 28867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (292909301 / 500000000) ≤ -Real.log (11133 / 20000) ∧
    -Real.log (11133 / 20000) ≤ (585818603 / 1000000000) := by
  have h := checkLog_sound (w := (8867 / 31133)) (n := 12)
    (lo := (292909301 / 500000000)) (hi := (585818603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11133) = 1/(11133 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-585818603 / 1000000000) (-292909301 / 500000000) (Real.log (11133 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (368181983 / 1000000000) ≤ -Real.log (200000 / 289021) ∧
    -Real.log (200000 / 289021) ≤ (11505687 / 31250000) := by
  have h := checkLog_sound (w := (89021 / 489021)) (n := 12)
    (lo := (368181983 / 1000000000)) (hi := (11505687 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289021 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289021 / 200000) = 1/(200000 / 289021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (368181983 / 1000000000) (11505687 / 31250000) (Real.log (289021 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (289021 / 200000) = -Real.log (200000 / 289021) := by
    rw [show ((289021 / 200000) : ℝ) = ((200000 / 289021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (147244093 / 250000000) ≤ -Real.log (110979 / 200000) ∧
    -Real.log (110979 / 200000) ≤ (588976373 / 1000000000) := by
  have h := checkLog_sound (w := (89021 / 310979)) (n := 12)
    (lo := (147244093 / 250000000)) (hi := (588976373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110979) = 1/(110979 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-588976373 / 1000000000) (-147244093 / 250000000) (Real.log (110979 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1297384679 / 1000000000) ≤ -Real.log (500000000000 / 1829856410949) ∧
    -Real.log (500000000000 / 1829856410949) ≤ (1297384681 / 1000000000) := by
  have h := checkLog_sound (w := (829856410949 / 2829856410949)) (n := 12)
    (lo := (604237499 / 1000000000)) (hi := (48339 / 80000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829856410949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1829856410949 / 1000000000000) = 1/(500000000000 / 1829856410949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1297384679 / 1000000000) (1297384681 / 1000000000) (Real.log (1829856410949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1829856410949 / 500000000000) = -Real.log (500000000000 / 1829856410949) := by
    rw [show ((1829856410949 / 500000000000) : ℝ) = ((500000000000 / 1829856410949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52120013 / 40000000) ≤ -Real.log (500000000000 / 1840161143497) ∧
    -Real.log (500000000000 / 1840161143497) ≤ (1303000327 / 1000000000) := by
  have h := checkLog_sound (w := (840161143497 / 2840161143497)) (n := 12)
    (lo := (121970629 / 200000000)) (hi := (304926573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1840161143497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1840161143497 / 1000000000000) = 1/(500000000000 / 1840161143497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52120013 / 40000000) (1303000327 / 1000000000) (Real.log (1840161143497 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1840161143497 / 500000000000) = -Real.log (500000000000 / 1840161143497) := by
    rw [show ((1840161143497 / 500000000000) : ℝ) = ((500000000000 / 1840161143497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (476392701 / 500000000) ≤ -Real.log (100000000000 / 259292194377) ∧
    -Real.log (100000000000 / 259292194377) ≤ (238196351 / 250000000) := by
  have h := checkLog_sound (w := (59292194377 / 459292194377)) (n := 12)
    (lo := (129819111 / 500000000)) (hi := (259638223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259292194377 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259292194377 / 200000000000) = 1/(100000000000 / 259292194377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (476392701 / 500000000) (238196351 / 250000000) (Real.log (259292194377 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (259292194377 / 100000000000) = -Real.log (100000000000 / 259292194377) := by
    rw [show ((259292194377 / 100000000000) : ℝ) = ((100000000000 / 259292194377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (191431671 / 200000000) ≤ -Real.log (31250000000 / 81383921733) ∧
    -Real.log (31250000000 / 81383921733) ≤ (957158357 / 1000000000) := by
  have h := checkLog_sound (w := (18883921733 / 143883921733)) (n := 12)
    (lo := (10560447 / 40000000)) (hi := (33001397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81383921733 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(81383921733 / 62500000000) = 1/(31250000000 / 81383921733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (191431671 / 200000000) (957158357 / 1000000000) (Real.log (81383921733 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (81383921733 / 31250000000) = -Real.log (31250000000 / 81383921733) := by
    rw [show ((81383921733 / 31250000000) : ℝ) = ((31250000000 / 81383921733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0104
