import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0130
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

theorem reflection_log_1_neg : (331132521 / 500000000) ≤ -Real.log (25600 / 49643) ∧
    -Real.log (25600 / 49643) ≤ (662265043 / 1000000000) := by
  have h := checkLog_sound (w := (24043 / 75243)) (n := 12)
    (lo := (331132521 / 500000000)) (hi := (662265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49643 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49643 / 25600) = 1/(25600 / 49643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331132521 / 500000000) (662265043 / 1000000000) (Real.log (49643 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49643 / 25600) = -Real.log (25600 / 49643) := by
    rw [show ((49643 / 25600) : ℝ) = ((25600 / 49643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (87494733 / 31250000) ≤ -Real.log (1557 / 25600) ∧
    -Real.log (1557 / 25600) ≤ (2799831461 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1557) = 1/(1557 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2799831461 / 1000000000) (-87494733 / 31250000) (Real.log (1557 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (165470559 / 250000000) ≤ -Real.log (3200 / 6203) ∧
    -Real.log (3200 / 6203) ≤ (661882237 / 1000000000) := by
  have h := checkLog_sound (w := (3003 / 9403)) (n := 12)
    (lo := (165470559 / 250000000)) (hi := (661882237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6203 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6203 / 3200) = 1/(3200 / 6203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (165470559 / 250000000) (661882237 / 1000000000) (Real.log (6203 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6203 / 3200) = -Real.log (3200 / 6203) := by
    rw [show ((6203 / 3200) : ℝ) = ((3200 / 6203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2787702357 / 1000000000) ≤ -Real.log (197 / 3200) ∧
    -Real.log (197 / 3200) ≤ (1393851181 / 500000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 197) = 1/(197 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1393851181 / 500000000) (-2787702357 / 1000000000) (Real.log (197 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (315199361 / 500000000) ≤ -Real.log (12800 / 24043) ∧
    -Real.log (12800 / 24043) ≤ (630398723 / 1000000000) := by
  have h := checkLog_sound (w := (11243 / 36843)) (n := 12)
    (lo := (315199361 / 500000000)) (hi := (630398723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24043 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24043 / 12800) = 1/(12800 / 24043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (315199361 / 500000000) (630398723 / 1000000000) (Real.log (24043 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24043 / 12800) = -Real.log (12800 / 24043) := by
    rw [show ((24043 / 12800) : ℝ) = ((12800 / 24043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (526671069 / 250000000) ≤ -Real.log (1557 / 12800) ∧
    -Real.log (1557 / 12800) ≤ (52667107 / 25000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1557) = 1/(1557 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52667107 / 25000000) (-526671069 / 250000000) (Real.log (1557 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (629608159 / 1000000000) ≤ -Real.log (1600 / 3003) ∧
    -Real.log (1600 / 3003) ≤ (3935051 / 6250000) := by
  have h := checkLog_sound (w := (1403 / 4603)) (n := 12)
    (lo := (629608159 / 1000000000)) (hi := (3935051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3003 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3003 / 1600) = 1/(1600 / 3003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (629608159 / 1000000000) (3935051 / 6250000) (Real.log (3003 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3003 / 1600) = -Real.log (1600 / 3003) := by
    rw [show ((3003 / 1600) : ℝ) = ((1600 / 3003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2094555177 / 1000000000) ≤ -Real.log (197 / 1600) ∧
    -Real.log (197 / 1600) ≤ (2094555181 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 397)) (n := 12)
    (lo := (15113637 / 1000000000)) (hi := (7556819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 197) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 197) = 1/(197 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2094555181 / 1000000000) (-2094555177 / 1000000000) (Real.log (197 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (668187769 / 1000000000) ≤ -Real.log (1000000 / 1950699) ∧
    -Real.log (1000000 / 1950699) ≤ (66818777 / 100000000) := by
  have h := checkLog_sound (w := (950699 / 2950699)) (n := 12)
    (lo := (668187769 / 1000000000)) (hi := (66818777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950699 / 1000000) = 1/(1000000 / 1950699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (668187769 / 1000000000) (66818777 / 100000000) (Real.log (1950699 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1950699 / 1000000) = -Real.log (1000000 / 1950699) := by
    rw [show ((1950699 / 1000000) : ℝ) = ((1000000 / 1950699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3009810911 / 1000000000) ≤ -Real.log (49301 / 1000000) ∧
    -Real.log (49301 / 1000000) ≤ (752452729 / 250000000) := by
  have h := checkLog_sound (w := (13199 / 111801)) (n := 12)
    (lo := (237222191 / 1000000000)) (hi := (14826387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49301) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49301) = 1/(49301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-752452729 / 250000000) (-3009810911 / 1000000000) (Real.log (49301 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41779387 / 62500000) ≤ -Real.log (800 / 1561) ∧
    -Real.log (800 / 1561) ≤ (668470193 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 2361)) (n := 12)
    (lo := (41779387 / 62500000)) (hi := (668470193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1561 / 800) = 1/(800 / 1561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41779387 / 62500000) (668470193 / 1000000000) (Real.log (1561 / 800)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1561 / 800) = -Real.log (800 / 1561) := by
    rw [show ((1561 / 800) : ℝ) = ((800 / 1561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3021050079 / 1000000000) ≤ -Real.log (39 / 800) ∧
    -Real.log (39 / 800) ≤ (755262521 / 250000000) := by
  have h := checkLog_sound (w := (11 / 89)) (n := 12)
    (lo := (248461359 / 1000000000)) (hi := (3105767 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(50 / 39) = 1/(39 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-755262521 / 250000000) (-3021050079 / 1000000000) (Real.log (39 / 800)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10434257 / 15625000) ≤ -Real.log (125000 / 243741) ∧
    -Real.log (125000 / 243741) ≤ (667792449 / 1000000000) := by
  have h := checkLog_sound (w := (118741 / 368741)) (n := 12)
    (lo := (10434257 / 15625000)) (hi := (667792449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243741 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243741 / 125000) = 1/(125000 / 243741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10434257 / 15625000) (667792449 / 1000000000) (Real.log (243741 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243741 / 125000) = -Real.log (125000 / 243741) := by
    rw [show ((243741 / 125000) : ℝ) = ((125000 / 243741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2994293307 / 1000000000) ≤ -Real.log (6259 / 125000) ∧
    -Real.log (6259 / 125000) ≤ (46785833 / 15625000) := by
  have h := checkLog_sound (w := (3107 / 28143)) (n := 12)
    (lo := (221704587 / 1000000000)) (hi := (55426147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12518) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12518) = 1/(6259 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46785833 / 15625000) (-2994293307 / 1000000000) (Real.log (6259 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (668085749 / 1000000000) ≤ -Real.log (2000 / 3901) ∧
    -Real.log (2000 / 3901) ≤ (2672343 / 4000000) := by
  have h := checkLog_sound (w := (1901 / 5901)) (n := 12)
    (lo := (668085749 / 1000000000)) (hi := (2672343 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3901 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3901 / 2000) = 1/(2000 / 3901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (668085749 / 1000000000) (2672343 / 4000000) (Real.log (3901 / 2000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (3901 / 2000) = -Real.log (2000 / 3901) := by
    rw [show ((3901 / 2000) : ℝ) = ((2000 / 3901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3005782607 / 1000000000) ≤ -Real.log (99 / 2000) ∧
    -Real.log (99 / 2000) ≤ (751445653 / 250000000) := by
  have h := checkLog_sound (w := (13 / 112)) (n := 12)
    (lo := (233193887 / 1000000000)) (hi := (7287309 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 99) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 99) = 1/(99 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-751445653 / 250000000) (-3005782607 / 1000000000) (Real.log (99 / 2000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3677998681 / 1000000000) ≤ -Real.log (250000000000 / 9891782113953) ∧
    -Real.log (250000000000 / 9891782113953) ≤ (3677998687 / 1000000000) := by
  have h := checkLog_sound (w := (1891782113953 / 17891782113953)) (n := 12)
    (lo := (212262781 / 1000000000)) (hi := (106131391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9891782113953 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9891782113953 / 8000000000000) = 1/(250000000000 / 9891782113953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3677998681 / 1000000000) (3677998687 / 1000000000) (Real.log (9891782113953 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9891782113953 / 250000000000) = -Real.log (250000000000 / 9891782113953) := by
    rw [show ((9891782113953 / 250000000000) : ℝ) = ((250000000000 / 9891782113953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3689520271 / 1000000000) ≤ -Real.log (500000000000 / 20012820512821) ∧
    -Real.log (500000000000 / 20012820512821) ≤ (3689520277 / 1000000000) := by
  have h := checkLog_sound (w := (4012820512821 / 36012820512821)) (n := 12)
    (lo := (223784371 / 1000000000)) (hi := (55946093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20012820512821 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20012820512821 / 16000000000000) = 1/(500000000000 / 20012820512821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3689520271 / 1000000000) (3689520277 / 1000000000) (Real.log (20012820512821 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20012820512821 / 500000000000) = -Real.log (500000000000 / 20012820512821) := by
    rw [show ((20012820512821 / 500000000000) : ℝ) = ((500000000000 / 20012820512821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (732417151 / 200000000) ≤ -Real.log (250000000000 / 9735620706183) ∧
    -Real.log (250000000000 / 9735620706183) ≤ (3662085761 / 1000000000) := by
  have h := checkLog_sound (w := (1735620706183 / 17735620706183)) (n := 12)
    (lo := (39269971 / 200000000)) (hi := (6135933 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9735620706183 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9735620706183 / 8000000000000) = 1/(250000000000 / 9735620706183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (732417151 / 200000000) (3662085761 / 1000000000) (Real.log (9735620706183 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9735620706183 / 250000000000) = -Real.log (250000000000 / 9735620706183) := by
    rw [show ((9735620706183 / 250000000000) : ℝ) = ((250000000000 / 9735620706183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (918467089 / 250000000) ≤ -Real.log (500000000000 / 19702020202021) ∧
    -Real.log (500000000000 / 19702020202021) ≤ (1836934181 / 500000000) := by
  have h := checkLog_sound (w := (3702020202021 / 35702020202021)) (n := 12)
    (lo := (26016557 / 125000000)) (hi := (208132457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19702020202021 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19702020202021 / 16000000000000) = 1/(500000000000 / 19702020202021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (918467089 / 250000000) (1836934181 / 500000000) (Real.log (19702020202021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19702020202021 / 500000000000) = -Real.log (500000000000 / 19702020202021) := by
    rw [show ((19702020202021 / 500000000000) : ℝ) = ((500000000000 / 19702020202021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0130
