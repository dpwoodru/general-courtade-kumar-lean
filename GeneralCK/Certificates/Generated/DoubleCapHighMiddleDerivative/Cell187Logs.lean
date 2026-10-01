import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell187
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

theorem reflection_log_1_neg : (153799791 / 500000000) ≤ -Real.log (1280 / 1741) ∧
    -Real.log (1280 / 1741) ≤ (307599583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3021)) (n := 12)
    (lo := (153799791 / 500000000)) (hi := (307599583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1741 / 1280) = 1/(1280 / 1741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153799791 / 500000000) (307599583 / 1000000000) (Real.log (1741 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1741 / 1280) = -Real.log (1280 / 1741) := by
    rw [show ((1741 / 1280) : ℝ) = ((1280 / 1741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (446531273 / 1000000000) ≤ -Real.log (819 / 1280) ∧
    -Real.log (819 / 1280) ≤ (223265637 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2099)) (n := 12)
    (lo := (446531273 / 1000000000)) (hi := (223265637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 819) = 1/(819 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223265637 / 500000000) (-446531273 / 1000000000) (Real.log (819 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (307168703 / 1000000000) ≤ -Real.log (5120 / 6961) ∧
    -Real.log (5120 / 6961) ≤ (4799511 / 15625000) := by
  have h := checkLog_sound (w := (1841 / 12081)) (n := 12)
    (lo := (307168703 / 1000000000)) (hi := (4799511 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6961 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6961 / 5120) = 1/(5120 / 6961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (307168703 / 1000000000) (4799511 / 15625000) (Real.log (6961 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6961 / 5120) = -Real.log (5120 / 6961) := by
    rw [show ((6961 / 5120) : ℝ) = ((5120 / 6961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445615941 / 1000000000) ≤ -Real.log (3279 / 5120) ∧
    -Real.log (3279 / 5120) ≤ (222807971 / 500000000) := by
  have h := checkLog_sound (w := (1841 / 8399)) (n := 12)
    (lo := (445615941 / 1000000000)) (hi := (222807971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3279) = 1/(3279 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-222807971 / 500000000) (-445615941 / 1000000000) (Real.log (3279 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9107823 / 40000000) ≤ -Real.log (1000000 / 1255703) ∧
    -Real.log (1000000 / 1255703) ≤ (28461947 / 125000000) := by
  have h := checkLog_sound (w := (255703 / 2255703)) (n := 12)
    (lo := (9107823 / 40000000)) (hi := (28461947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255703 / 1000000) = 1/(1000000 / 1255703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9107823 / 40000000) (28461947 / 125000000) (Real.log (1255703 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1255703 / 1000000) = -Real.log (1000000 / 1255703) := by
    rw [show ((1255703 / 1000000) : ℝ) = ((1000000 / 1255703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29531513 / 100000000) ≤ -Real.log (744297 / 1000000) ∧
    -Real.log (744297 / 1000000) ≤ (295315131 / 1000000000) := by
  have h := checkLog_sound (w := (255703 / 1744297)) (n := 12)
    (lo := (29531513 / 100000000)) (hi := (295315131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744297) = 1/(744297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-295315131 / 1000000000) (-29531513 / 100000000) (Real.log (744297 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45606317 / 200000000) ≤ -Real.log (8000 / 10049) ∧
    -Real.log (8000 / 10049) ≤ (114015793 / 500000000) := by
  have h := checkLog_sound (w := (2049 / 18049)) (n := 12)
    (lo := (45606317 / 200000000)) (hi := (114015793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10049 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10049 / 8000) = 1/(8000 / 10049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45606317 / 200000000) (114015793 / 500000000) (Real.log (10049 / 8000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (10049 / 8000) = -Real.log (8000 / 10049) := by
    rw [show ((10049 / 8000) : ℝ) = ((8000 / 10049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (295882269 / 1000000000) ≤ -Real.log (5951 / 8000) ∧
    -Real.log (5951 / 8000) ≤ (29588227 / 100000000) := by
  have h := checkLog_sound (w := (2049 / 13951)) (n := 12)
    (lo := (295882269 / 1000000000)) (hi := (29588227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5951) = 1/(5951 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29588227 / 100000000) (-295882269 / 1000000000) (Real.log (5951 / 8000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3380403 / 20000000) ≤ -Real.log (62500 / 74009) ∧
    -Real.log (62500 / 74009) ≤ (169020151 / 1000000000) := by
  have h := checkLog_sound (w := (11509 / 136509)) (n := 12)
    (lo := (3380403 / 20000000)) (hi := (169020151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74009 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74009 / 62500) = 1/(62500 / 74009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3380403 / 20000000) (169020151 / 1000000000) (Real.log (74009 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (74009 / 62500) = -Real.log (62500 / 74009) := by
    rw [show ((74009 / 62500) : ℝ) = ((62500 / 74009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20351741 / 100000000) ≤ -Real.log (50991 / 62500) ∧
    -Real.log (50991 / 62500) ≤ (203517411 / 1000000000) := by
  have h := checkLog_sound (w := (11509 / 113491)) (n := 12)
    (lo := (20351741 / 100000000)) (hi := (203517411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50991) = 1/(50991 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203517411 / 1000000000) (-20351741 / 100000000) (Real.log (50991 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84643487 / 500000000) ≤ -Real.log (50000 / 59223) ∧
    -Real.log (50000 / 59223) ≤ (6771479 / 40000000) := by
  have h := checkLog_sound (w := (9223 / 109223)) (n := 12)
    (lo := (84643487 / 500000000)) (hi := (6771479 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59223 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59223 / 50000) = 1/(50000 / 59223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84643487 / 500000000) (6771479 / 40000000) (Real.log (59223 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (59223 / 50000) = -Real.log (50000 / 59223) := by
    rw [show ((59223 / 50000) : ℝ) = ((50000 / 59223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (25488101 / 125000000) ≤ -Real.log (40777 / 50000) ∧
    -Real.log (40777 / 50000) ≤ (203904809 / 1000000000) := by
  have h := checkLog_sound (w := (9223 / 90777)) (n := 12)
    (lo := (25488101 / 125000000)) (hi := (203904809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40777) = 1/(40777 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-203904809 / 1000000000) (-25488101 / 125000000) (Real.log (40777 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (752784643 / 1000000000) ≤ -Real.log (125000000000 / 265362915523) ∧
    -Real.log (125000000000 / 265362915523) ≤ (150556929 / 200000000) := by
  have h := checkLog_sound (w := (15362915523 / 515362915523)) (n := 12)
    (lo := (59637463 / 1000000000)) (hi := (7454683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265362915523 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265362915523 / 250000000000) = 1/(125000000000 / 265362915523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (752784643 / 1000000000) (150556929 / 200000000) (Real.log (265362915523 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (265362915523 / 125000000000) = -Real.log (125000000000 / 265362915523) := by
    rw [show ((265362915523 / 125000000000) : ℝ) = ((125000000000 / 265362915523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150826171 / 200000000) ≤ -Real.log (250000000000 / 531440781441) ∧
    -Real.log (250000000000 / 531440781441) ≤ (754130857 / 1000000000) := by
  have h := checkLog_sound (w := (31440781441 / 1031440781441)) (n := 12)
    (lo := (2439347 / 40000000)) (hi := (15245919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531440781441 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(531440781441 / 500000000000) = 1/(250000000000 / 531440781441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (150826171 / 200000000) (754130857 / 1000000000) (Real.log (531440781441 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (531440781441 / 250000000000) = -Real.log (250000000000 / 531440781441) := by
    rw [show ((531440781441 / 250000000000) : ℝ) = ((250000000000 / 531440781441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (104602141 / 200000000) ≤ -Real.log (500000000000 / 843549685139) ∧
    -Real.log (500000000000 / 843549685139) ≤ (261505353 / 500000000) := by
  have h := checkLog_sound (w := (343549685139 / 1343549685139)) (n := 12)
    (lo := (104602141 / 200000000)) (hi := (261505353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843549685139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843549685139 / 500000000000) = 1/(500000000000 / 843549685139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (104602141 / 200000000) (261505353 / 500000000) (Real.log (843549685139 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (843549685139 / 500000000000) = -Real.log (500000000000 / 843549685139) := by
    rw [show ((843549685139 / 500000000000) : ℝ) = ((500000000000 / 843549685139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (261956927 / 500000000) ≤ -Real.log (500000000000 / 844311880357) ∧
    -Real.log (500000000000 / 844311880357) ≤ (104782771 / 200000000) := by
  have h := checkLog_sound (w := (344311880357 / 1344311880357)) (n := 12)
    (lo := (261956927 / 500000000)) (hi := (104782771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((844311880357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(844311880357 / 500000000000) = 1/(500000000000 / 844311880357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (261956927 / 500000000) (104782771 / 200000000) (Real.log (844311880357 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (844311880357 / 500000000000) = -Real.log (500000000000 / 844311880357) := by
    rw [show ((844311880357 / 500000000000) : ℝ) = ((500000000000 / 844311880357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9313439 / 25000000) ≤ -Real.log (20000000000 / 29028259889) ∧
    -Real.log (20000000000 / 29028259889) ≤ (372537561 / 1000000000) := by
  have h := checkLog_sound (w := (9028259889 / 49028259889)) (n := 12)
    (lo := (9313439 / 25000000)) (hi := (372537561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29028259889 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29028259889 / 20000000000) = 1/(20000000000 / 29028259889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9313439 / 25000000) (372537561 / 1000000000) (Real.log (29028259889 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (29028259889 / 20000000000) = -Real.log (20000000000 / 29028259889) := by
    rw [show ((29028259889 / 20000000000) : ℝ) = ((20000000000 / 29028259889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (186595891 / 500000000) ≤ -Real.log (125000000000 / 181545356451) ∧
    -Real.log (125000000000 / 181545356451) ≤ (373191783 / 1000000000) := by
  have h := checkLog_sound (w := (56545356451 / 306545356451)) (n := 12)
    (lo := (186595891 / 500000000)) (hi := (373191783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181545356451 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181545356451 / 125000000000) = 1/(125000000000 / 181545356451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (186595891 / 500000000) (373191783 / 1000000000) (Real.log (181545356451 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (181545356451 / 125000000000) = -Real.log (125000000000 / 181545356451) := by
    rw [show ((181545356451 / 125000000000) : ℝ) = ((125000000000 / 181545356451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34617833 / 1000000000) ≤ -Real.log (2414936271 / 2500000000) ∧
    -Real.log (2414936271 / 2500000000) ≤ (17308917 / 500000000) := by
  have h := checkLog_sound (w := (85063729 / 4914936271)) (n := 12)
    (lo := (34617833 / 1000000000)) (hi := (17308917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2414936271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2414936271) = 1/(2414936271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17308917 / 500000000) (-34617833 / 1000000000) (Real.log (2414936271 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34497259 / 1000000000) ≤ -Real.log (3773792919 / 3906250000) ∧
    -Real.log (3773792919 / 3906250000) ≤ (1724863 / 50000000) := by
  have h := checkLog_sound (w := (132457081 / 7680042919)) (n := 12)
    (lo := (34497259 / 1000000000)) (hi := (1724863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3773792919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3773792919) = 1/(3773792919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1724863 / 50000000) (-34497259 / 1000000000) (Real.log (3773792919 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell187
