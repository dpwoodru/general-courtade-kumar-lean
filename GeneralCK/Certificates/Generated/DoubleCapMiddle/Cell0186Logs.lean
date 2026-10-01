import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0186
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

theorem reflection_log_1_neg : (54386743 / 200000000) ≤ -Real.log (16 / 21) ∧
    -Real.log (16 / 21) ≤ (67983429 / 250000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 16) = 1/(16 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54386743 / 200000000) (67983429 / 250000000) (Real.log (21 / 16)) := by
  have h := reflection_log_1_neg
  have he : Real.log (21 / 16) = -Real.log (16 / 21) := by
    rw [show ((21 / 16) : ℝ) = ((16 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (374693449 / 1000000000) ≤ -Real.log (11 / 16) ∧
    -Real.log (11 / 16) ≤ (7493869 / 20000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 11) = 1/(11 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7493869 / 20000000) (-374693449 / 1000000000) (Real.log (11 / 16)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (271487187 / 1000000000) ≤ -Real.log (5120 / 6717) ∧
    -Real.log (5120 / 6717) ≤ (67871797 / 250000000) := by
  have h := checkLog_sound (w := (1597 / 11837)) (n := 12)
    (lo := (271487187 / 1000000000)) (hi := (67871797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6717 / 5120) = 1/(5120 / 6717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (271487187 / 1000000000) (67871797 / 250000000) (Real.log (6717 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6717 / 5120) = -Real.log (5120 / 6717) := by
    rw [show ((6717 / 5120) : ℝ) = ((5120 / 6717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (373841539 / 1000000000) ≤ -Real.log (3523 / 5120) ∧
    -Real.log (3523 / 5120) ≤ (18692077 / 50000000) := by
  have h := checkLog_sound (w := (1597 / 8643)) (n := 12)
    (lo := (373841539 / 1000000000)) (hi := (18692077 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3523) = 1/(3523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18692077 / 50000000) (-373841539 / 1000000000) (Real.log (3523 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97101563 / 200000000) ≤ -Real.log (8 / 13) ∧
    -Real.log (8 / 13) ≤ (60688477 / 125000000) := by
  have h := checkLog_sound (w := (5 / 21)) (n := 12)
    (lo := (97101563 / 200000000)) (hi := (60688477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 8) = 1/(8 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97101563 / 200000000) (60688477 / 125000000) (Real.log (13 / 8)) := by
  have h := reflection_log_5_neg
  have he : Real.log (13 / 8) = -Real.log (8 / 13) := by
    rw [show ((13 / 8) : ℝ) = ((8 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245207313 / 250000000) ≤ -Real.log (3 / 8) ∧
    -Real.log (3 / 8) ≤ (490414627 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4 / 3) = 1/(3 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-490414627 / 500000000) (-245207313 / 250000000) (Real.log (3 / 8)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (484786401 / 1000000000) ≤ -Real.log (2560 / 4157) ∧
    -Real.log (2560 / 4157) ≤ (242393201 / 500000000) := by
  have h := checkLog_sound (w := (1597 / 6717)) (n := 12)
    (lo := (484786401 / 1000000000)) (hi := (242393201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4157 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4157 / 2560) = 1/(2560 / 4157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (484786401 / 1000000000) (242393201 / 500000000) (Real.log (4157 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4157 / 2560) = -Real.log (2560 / 4157) := by
    rw [show ((4157 / 2560) : ℝ) = ((2560 / 4157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (7821673 / 8000000) ≤ -Real.log (963 / 2560) ∧
    -Real.log (963 / 2560) ≤ (977709127 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 2243)) (n := 12)
    (lo := (56912389 / 200000000)) (hi := (142280973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 963) = 1/(963 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-977709127 / 1000000000) (-7821673 / 8000000) (Real.log (963 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (23211773 / 62500000) ≤ -Real.log (500000 / 724873) ∧
    -Real.log (500000 / 724873) ≤ (371388369 / 1000000000) := by
  have h := checkLog_sound (w := (224873 / 1224873)) (n := 12)
    (lo := (23211773 / 62500000)) (hi := (371388369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724873 / 500000) = 1/(500000 / 724873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (23211773 / 62500000) (371388369 / 1000000000) (Real.log (724873 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (724873 / 500000) = -Real.log (500000 / 724873) := by
    rw [show ((724873 / 500000) : ℝ) = ((500000 / 724873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (597375289 / 1000000000) ≤ -Real.log (275127 / 500000) ∧
    -Real.log (275127 / 500000) ≤ (59737529 / 100000000) := by
  have h := checkLog_sound (w := (224873 / 775127)) (n := 12)
    (lo := (597375289 / 1000000000)) (hi := (59737529 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 275127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 275127) = 1/(275127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-59737529 / 100000000) (-597375289 / 1000000000) (Real.log (275127 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (371999323 / 1000000000) ≤ -Real.log (125000 / 181329) ∧
    -Real.log (125000 / 181329) ≤ (92999831 / 250000000) := by
  have h := checkLog_sound (w := (56329 / 306329)) (n := 12)
    (lo := (371999323 / 1000000000)) (hi := (92999831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181329 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181329 / 125000) = 1/(125000 / 181329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (371999323 / 1000000000) (92999831 / 250000000) (Real.log (181329 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (181329 / 125000) = -Real.log (125000 / 181329) := by
    rw [show ((181329 / 125000) : ℝ) = ((125000 / 181329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1169896 / 1953125) ≤ -Real.log (68671 / 125000) ∧
    -Real.log (68671 / 125000) ≤ (598986753 / 1000000000) := by
  have h := checkLog_sound (w := (56329 / 193671)) (n := 12)
    (lo := (1169896 / 1953125)) (hi := (598986753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 68671) = 1/(68671 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-598986753 / 1000000000) (-1169896 / 1953125) (Real.log (68671 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (290304131 / 1000000000) ≤ -Real.log (500000 / 668417) ∧
    -Real.log (500000 / 668417) ≤ (72576033 / 250000000) := by
  have h := checkLog_sound (w := (168417 / 1168417)) (n := 12)
    (lo := (290304131 / 1000000000)) (hi := (72576033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668417 / 500000) = 1/(500000 / 668417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (290304131 / 1000000000) (72576033 / 250000000) (Real.log (668417 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (668417 / 500000) = -Real.log (500000 / 668417) := by
    rw [show ((668417 / 500000) : ℝ) = ((500000 / 668417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (410729943 / 1000000000) ≤ -Real.log (331583 / 500000) ∧
    -Real.log (331583 / 500000) ≤ (51341243 / 125000000) := by
  have h := checkLog_sound (w := (168417 / 831583)) (n := 12)
    (lo := (410729943 / 1000000000)) (hi := (51341243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331583) = 1/(331583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-51341243 / 125000000) (-410729943 / 1000000000) (Real.log (331583 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14542951 / 50000000) ≤ -Real.log (125000 / 167197) ∧
    -Real.log (125000 / 167197) ≤ (290859021 / 1000000000) := by
  have h := checkLog_sound (w := (42197 / 292197)) (n := 12)
    (lo := (14542951 / 50000000)) (hi := (290859021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167197 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167197 / 125000) = 1/(125000 / 167197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14542951 / 50000000) (290859021 / 1000000000) (Real.log (167197 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (167197 / 125000) = -Real.log (125000 / 167197) := by
    rw [show ((167197 / 125000) : ℝ) = ((125000 / 167197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102962361 / 250000000) ≤ -Real.log (82803 / 125000) ∧
    -Real.log (82803 / 125000) ≤ (82369889 / 200000000) := by
  have h := checkLog_sound (w := (42197 / 207803)) (n := 12)
    (lo := (102962361 / 250000000)) (hi := (82369889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 82803) = 1/(82803 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-82369889 / 200000000) (-102962361 / 250000000) (Real.log (82803 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (968763657 / 1000000000) ≤ -Real.log (100000000000 / 263468507271) ∧
    -Real.log (100000000000 / 263468507271) ≤ (968763659 / 1000000000) := by
  have h := checkLog_sound (w := (63468507271 / 463468507271)) (n := 12)
    (lo := (275616477 / 1000000000)) (hi := (137808239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263468507271 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263468507271 / 200000000000) = 1/(100000000000 / 263468507271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (968763657 / 1000000000) (968763659 / 1000000000) (Real.log (263468507271 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (263468507271 / 100000000000) = -Real.log (100000000000 / 263468507271) := by
    rw [show ((263468507271 / 100000000000) : ℝ) = ((100000000000 / 263468507271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38839443 / 40000000) ≤ -Real.log (1953125000 / 5157318273) ∧
    -Real.log (1953125000 / 5157318273) ≤ (970986077 / 1000000000) := by
  have h := checkLog_sound (w := (1251068273 / 9063568273)) (n := 12)
    (lo := (55567779 / 200000000)) (hi := (17364931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5157318273 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5157318273 / 3906250000) = 1/(1953125000 / 5157318273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38839443 / 40000000) (970986077 / 1000000000) (Real.log (5157318273 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5157318273 / 1953125000) = -Real.log (1953125000 / 5157318273) := by
    rw [show ((5157318273 / 1953125000) : ℝ) = ((1953125000 / 5157318273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (350517037 / 500000000) ≤ -Real.log (250000000000 / 503959038913) ∧
    -Real.log (250000000000 / 503959038913) ≤ (175258519 / 250000000) := by
  have h := checkLog_sound (w := (3959038913 / 1003959038913)) (n := 12)
    (lo := (3943447 / 500000000)) (hi := (1577379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503959038913 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(503959038913 / 500000000000) = 1/(250000000000 / 503959038913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (350517037 / 500000000) (175258519 / 250000000) (Real.log (503959038913 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (503959038913 / 250000000000) = -Real.log (250000000000 / 503959038913) := by
    rw [show ((503959038913 / 250000000000) : ℝ) = ((250000000000 / 503959038913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (43919279 / 62500000) ≤ -Real.log (250000000000 / 504803569919) ∧
    -Real.log (250000000000 / 504803569919) ≤ (351354233 / 500000000) := by
  have h := checkLog_sound (w := (4803569919 / 1004803569919)) (n := 12)
    (lo := (2390321 / 250000000)) (hi := (1912257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((504803569919 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(504803569919 / 500000000000) = 1/(250000000000 / 504803569919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (43919279 / 62500000) (351354233 / 500000000) (Real.log (504803569919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (504803569919 / 250000000000) = -Real.log (250000000000 / 504803569919) := by
    rw [show ((504803569919 / 250000000000) : ℝ) = ((250000000000 / 504803569919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0186
