import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0100
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

theorem reflection_log_1_neg : (83926087 / 125000000) ≤ -Real.log (25600 / 50099) ∧
    -Real.log (25600 / 50099) ≤ (671408697 / 1000000000) := by
  have h := checkLog_sound (w := (24499 / 75699)) (n := 12)
    (lo := (83926087 / 125000000)) (hi := (671408697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50099 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50099 / 25600) = 1/(25600 / 50099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83926087 / 125000000) (671408697 / 1000000000) (Real.log (50099 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50099 / 25600) = -Real.log (25600 / 50099) := by
    rw [show ((50099 / 25600) : ℝ) = ((25600 / 50099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3146373491 / 1000000000) ≤ -Real.log (1101 / 25600) ∧
    -Real.log (1101 / 25600) ≤ (393296687 / 125000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1101) = 1/(1101 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393296687 / 125000000) (-3146373491 / 1000000000) (Real.log (1101 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (671219053 / 1000000000) ≤ -Real.log (51200 / 100179) ∧
    -Real.log (51200 / 100179) ≤ (335609527 / 500000000) := by
  have h := checkLog_sound (w := (48979 / 151379)) (n := 12)
    (lo := (671219053 / 1000000000)) (hi := (335609527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100179 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100179 / 51200) = 1/(51200 / 100179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (671219053 / 1000000000) (335609527 / 500000000) (Real.log (100179 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100179 / 51200) = -Real.log (51200 / 100179) := by
    rw [show ((100179 / 51200) : ℝ) = ((51200 / 100179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (98055687 / 31250000) ≤ -Real.log (2221 / 51200) ∧
    -Real.log (2221 / 51200) ≤ (3137781989 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2221) = 1/(2221 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3137781989 / 1000000000) (-98055687 / 31250000) (Real.log (2221 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (649187129 / 1000000000) ≤ -Real.log (12800 / 24499) ∧
    -Real.log (12800 / 24499) ≤ (64918713 / 100000000) := by
  have h := checkLog_sound (w := (11699 / 37299)) (n := 12)
    (lo := (649187129 / 1000000000)) (hi := (64918713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24499 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24499 / 12800) = 1/(12800 / 24499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (649187129 / 1000000000) (64918713 / 100000000) (Real.log (24499 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24499 / 12800) = -Real.log (12800 / 24499) := by
    rw [show ((24499 / 12800) : ℝ) = ((12800 / 24499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2453226311 / 1000000000) ≤ -Real.log (1101 / 12800) ∧
    -Real.log (1101 / 12800) ≤ (490645263 / 200000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1101) = 1/(1101 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-490645263 / 200000000) (-2453226311 / 1000000000) (Real.log (1101 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (648799283 / 1000000000) ≤ -Real.log (25600 / 48979) ∧
    -Real.log (25600 / 48979) ≤ (162199821 / 250000000) := by
  have h := checkLog_sound (w := (23379 / 74579)) (n := 12)
    (lo := (648799283 / 1000000000)) (hi := (162199821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48979 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48979 / 25600) = 1/(25600 / 48979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (648799283 / 1000000000) (162199821 / 250000000) (Real.log (48979 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48979 / 25600) = -Real.log (25600 / 48979) := by
    rw [show ((48979 / 25600) : ℝ) = ((25600 / 48979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (611158701 / 250000000) ≤ -Real.log (2221 / 25600) ∧
    -Real.log (2221 / 25600) ≤ (305579351 / 125000000) := by
  have h := checkLog_sound (w := (979 / 5421)) (n := 12)
    (lo := (22824579 / 62500000)) (hi := (73038653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2221) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2221) = 1/(2221 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-305579351 / 125000000) (-611158701 / 250000000) (Real.log (2221 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168801677 / 250000000) ≤ -Real.log (1000000 / 1964439) ∧
    -Real.log (1000000 / 1964439) ≤ (675206709 / 1000000000) := by
  have h := checkLog_sound (w := (964439 / 2964439)) (n := 12)
    (lo := (168801677 / 250000000)) (hi := (675206709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964439 / 1000000) = 1/(1000000 / 1964439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168801677 / 250000000) (675206709 / 1000000000) (Real.log (1964439 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1964439 / 1000000) = -Real.log (1000000 / 1964439) := by
    rw [show ((1964439 / 1000000) : ℝ) = ((1000000 / 1964439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (667301149 / 200000000) ≤ -Real.log (35561 / 1000000) ∧
    -Real.log (35561 / 1000000) ≤ (13346023 / 4000000) := by
  have h := checkLog_sound (w := (26939 / 98061)) (n := 12)
    (lo := (22556681 / 40000000)) (hi := (281958513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35561) = 1/(35561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13346023 / 4000000) (-667301149 / 200000000) (Real.log (35561 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84419163 / 125000000) ≤ -Real.log (1000000 / 1964727) ∧
    -Real.log (1000000 / 1964727) ≤ (135070661 / 200000000) := by
  have h := checkLog_sound (w := (964727 / 2964727)) (n := 12)
    (lo := (84419163 / 125000000)) (hi := (135070661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964727 / 1000000) = 1/(1000000 / 1964727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84419163 / 125000000) (135070661 / 200000000) (Real.log (1964727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1964727 / 1000000) = -Real.log (1000000 / 1964727) := by
    rw [show ((1964727 / 1000000) : ℝ) = ((1000000 / 1964727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3344637477 / 1000000000) ≤ -Real.log (35273 / 1000000) ∧
    -Real.log (35273 / 1000000) ≤ (1672318741 / 500000000) := by
  have h := checkLog_sound (w := (27227 / 97773)) (n := 12)
    (lo := (572048757 / 1000000000)) (hi := (286024379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35273) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35273) = 1/(35273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1672318741 / 500000000) (-3344637477 / 1000000000) (Real.log (35273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337514771 / 500000000) ≤ -Real.log (1000000 / 1964091) ∧
    -Real.log (1000000 / 1964091) ≤ (675029543 / 1000000000) := by
  have h := checkLog_sound (w := (964091 / 2964091)) (n := 12)
    (lo := (337514771 / 500000000)) (hi := (675029543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964091 / 1000000) = 1/(1000000 / 1964091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337514771 / 500000000) (675029543 / 1000000000) (Real.log (1964091 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964091 / 1000000) = -Real.log (1000000 / 1964091) := by
    rw [show ((1964091 / 1000000) : ℝ) = ((1000000 / 1964091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (831691829 / 250000000) ≤ -Real.log (35909 / 1000000) ∧
    -Real.log (35909 / 1000000) ≤ (3326767321 / 1000000000) := by
  have h := checkLog_sound (w := (26591 / 98409)) (n := 12)
    (lo := (138544649 / 250000000)) (hi := (554178597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35909) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35909) = 1/(35909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3326767321 / 1000000000) (-831691829 / 250000000) (Real.log (35909 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675179219 / 1000000000) ≤ -Real.log (200000 / 392877) ∧
    -Real.log (200000 / 392877) ≤ (33758961 / 50000000) := by
  have h := checkLog_sound (w := (192877 / 592877)) (n := 12)
    (lo := (675179219 / 1000000000)) (hi := (33758961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392877 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392877 / 200000) = 1/(200000 / 392877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675179219 / 1000000000) (33758961 / 50000000) (Real.log (392877 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392877 / 200000) = -Real.log (200000 / 392877) := by
    rw [show ((392877 / 200000) : ℝ) = ((200000 / 392877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3334988379 / 1000000000) ≤ -Real.log (7123 / 200000) ∧
    -Real.log (7123 / 200000) ≤ (104218387 / 31250000) := by
  have h := checkLog_sound (w := (5377 / 19623)) (n := 12)
    (lo := (562399659 / 1000000000)) (hi := (28119983 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7123) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7123) = 1/(7123 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-104218387 / 31250000) (-3334988379 / 1000000000) (Real.log (7123 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1002928113 / 250000000) ≤ -Real.log (62500000000 / 3452586752341) ∧
    -Real.log (62500000000 / 3452586752341) ≤ (2005856229 / 500000000) := by
  have h := checkLog_sound (w := (1452586752341 / 5452586752341)) (n := 12)
    (lo := (68247069 / 125000000)) (hi := (545976553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3452586752341 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3452586752341 / 2000000000000) = 1/(62500000000 / 3452586752341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1002928113 / 250000000) (2005856229 / 500000000) (Real.log (3452586752341 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3452586752341 / 62500000000) = -Real.log (62500000000 / 3452586752341) := by
    rw [show ((3452586752341 / 62500000000) : ℝ) = ((62500000000 / 3452586752341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4019990781 / 1000000000) ≤ -Real.log (125000000000 / 6962574065149) ∧
    -Real.log (125000000000 / 6962574065149) ≤ (4019990787 / 1000000000) := by
  have h := checkLog_sound (w := (2962574065149 / 10962574065149)) (n := 12)
    (lo := (554254881 / 1000000000)) (hi := (277127441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6962574065149 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6962574065149 / 4000000000000) = 1/(125000000000 / 6962574065149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4019990781 / 1000000000) (4019990787 / 1000000000) (Real.log (6962574065149 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6962574065149 / 125000000000) = -Real.log (125000000000 / 6962574065149) := by
    rw [show ((6962574065149 / 125000000000) : ℝ) = ((125000000000 / 6962574065149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2000898429 / 500000000) ≤ -Real.log (500000000000 / 27348171767523) ∧
    -Real.log (500000000000 / 27348171767523) ≤ (15632019 / 3906250) := by
  have h := checkLog_sound (w := (11348171767523 / 43348171767523)) (n := 12)
    (lo := (268030479 / 500000000)) (hi := (536060959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27348171767523 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27348171767523 / 16000000000000) = 1/(500000000000 / 27348171767523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2000898429 / 500000000) (15632019 / 3906250) (Real.log (27348171767523 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27348171767523 / 500000000000) = -Real.log (500000000000 / 27348171767523) := by
    rw [show ((27348171767523 / 500000000000) : ℝ) = ((500000000000 / 27348171767523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4010167597 / 1000000000) ≤ -Real.log (62500000000 / 3447257124807) ∧
    -Real.log (62500000000 / 3447257124807) ≤ (4010167603 / 1000000000) := by
  have h := checkLog_sound (w := (1447257124807 / 5447257124807)) (n := 12)
    (lo := (544431697 / 1000000000)) (hi := (272215849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447257124807 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3447257124807 / 2000000000000) = 1/(62500000000 / 3447257124807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4010167597 / 1000000000) (4010167603 / 1000000000) (Real.log (3447257124807 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3447257124807 / 62500000000) = -Real.log (62500000000 / 3447257124807) := by
    rw [show ((3447257124807 / 62500000000) : ℝ) = ((62500000000 / 3447257124807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0100
