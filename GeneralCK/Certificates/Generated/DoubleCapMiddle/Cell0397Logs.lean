import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0397
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

theorem reflection_log_1_neg : (20094587 / 100000000) ≤ -Real.log (10240 / 12519) ∧
    -Real.log (10240 / 12519) ≤ (200945871 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 22759)) (n := 12)
    (lo := (20094587 / 100000000)) (hi := (200945871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12519 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12519 / 10240) = 1/(10240 / 12519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20094587 / 100000000) (200945871 / 1000000000) (Real.log (12519 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12519 / 10240) = -Real.log (10240 / 12519) := by
    rw [show ((12519 / 10240) : ℝ) = ((10240 / 12519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251746999 / 1000000000) ≤ -Real.log (7961 / 10240) ∧
    -Real.log (7961 / 10240) ≤ (251747 / 1000000) := by
  have h := checkLog_sound (w := (2279 / 18201)) (n := 12)
    (lo := (251746999 / 1000000000)) (hi := (251747 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7961) = 1/(7961 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) (Real.log (7961 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (100353103 / 500000000) ≤ -Real.log (2560 / 3129) ∧
    -Real.log (2560 / 3129) ≤ (200706207 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 5689)) (n := 12)
    (lo := (100353103 / 500000000)) (hi := (200706207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3129 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3129 / 2560) = 1/(2560 / 3129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (100353103 / 500000000) (200706207 / 1000000000) (Real.log (3129 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3129 / 2560) = -Real.log (2560 / 3129) := by
    rw [show ((3129 / 2560) : ℝ) = ((2560 / 3129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251370233 / 1000000000) ≤ -Real.log (1991 / 2560) ∧
    -Real.log (1991 / 2560) ≤ (125685117 / 500000000) := by
  have h := checkLog_sound (w := (569 / 4551)) (n := 12)
    (lo := (251370233 / 1000000000)) (hi := (125685117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1991) = 1/(1991 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) (Real.log (1991 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23011901 / 62500000) ≤ -Real.log (5120 / 7399) ∧
    -Real.log (5120 / 7399) ≤ (368190417 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 12519)) (n := 12)
    (lo := (23011901 / 62500000)) (hi := (368190417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7399 / 5120) = 1/(5120 / 7399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23011901 / 62500000) (368190417 / 1000000000) (Real.log (7399 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7399 / 5120) = -Real.log (5120 / 7399) := by
    rw [show ((7399 / 5120) : ℝ) = ((5120 / 7399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9203099 / 15625000) ≤ -Real.log (2841 / 5120) ∧
    -Real.log (2841 / 5120) ≤ (588998337 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 7961)) (n := 12)
    (lo := (9203099 / 15625000)) (hi := (588998337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2841) = 1/(2841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) (Real.log (2841 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183892437 / 500000000) ≤ -Real.log (1280 / 1849) ∧
    -Real.log (1280 / 1849) ≤ (2942279 / 8000000) := by
  have h := checkLog_sound (w := (569 / 3129)) (n := 12)
    (lo := (183892437 / 500000000)) (hi := (2942279 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1849 / 1280) = 1/(1280 / 1849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183892437 / 500000000) (2942279 / 8000000) (Real.log (1849 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1849 / 1280) = -Real.log (1280 / 1849) := by
    rw [show ((1849 / 1280) : ℝ) = ((1280 / 1849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (587942927 / 1000000000) ≤ -Real.log (711 / 1280) ∧
    -Real.log (711 / 1280) ≤ (36746433 / 62500000) := by
  have h := checkLog_sound (w := (569 / 1991)) (n := 12)
    (lo := (587942927 / 1000000000)) (hi := (36746433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 711) = 1/(711 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) (Real.log (711 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137737433 / 500000000) ≤ -Real.log (250000 / 329289) ∧
    -Real.log (250000 / 329289) ≤ (275474867 / 1000000000) := by
  have h := checkLog_sound (w := (79289 / 579289)) (n := 12)
    (lo := (137737433 / 500000000)) (hi := (275474867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329289 / 250000) = 1/(250000 / 329289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137737433 / 500000000) (275474867 / 1000000000) (Real.log (329289 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (329289 / 250000) = -Real.log (250000 / 329289) := by
    rw [show ((329289 / 250000) : ℝ) = ((250000 / 329289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (381488849 / 1000000000) ≤ -Real.log (170711 / 250000) ∧
    -Real.log (170711 / 250000) ≤ (7629777 / 20000000) := by
  have h := checkLog_sound (w := (79289 / 420711)) (n := 12)
    (lo := (381488849 / 1000000000)) (hi := (7629777 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170711) = 1/(170711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7629777 / 20000000) (-381488849 / 1000000000) (Real.log (170711 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (275798997 / 1000000000) ≤ -Real.log (1000000 / 1317583) ∧
    -Real.log (1000000 / 1317583) ≤ (137899499 / 500000000) := by
  have h := checkLog_sound (w := (317583 / 2317583)) (n := 12)
    (lo := (275798997 / 1000000000)) (hi := (137899499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317583 / 1000000) = 1/(1000000 / 1317583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (275798997 / 1000000000) (137899499 / 500000000) (Real.log (1317583 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1317583 / 1000000) = -Real.log (1000000 / 1317583) := by
    rw [show ((1317583 / 1000000) : ℝ) = ((1000000 / 1317583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (382114371 / 1000000000) ≤ -Real.log (682417 / 1000000) ∧
    -Real.log (682417 / 1000000) ≤ (95528593 / 250000000) := by
  have h := checkLog_sound (w := (317583 / 1682417)) (n := 12)
    (lo := (382114371 / 1000000000)) (hi := (95528593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682417) = 1/(682417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-95528593 / 250000000) (-382114371 / 1000000000) (Real.log (682417 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4151451 / 20000000) ≤ -Real.log (1000000 / 1230687) ∧
    -Real.log (1000000 / 1230687) ≤ (207572551 / 1000000000) := by
  have h := checkLog_sound (w := (230687 / 2230687)) (n := 12)
    (lo := (4151451 / 20000000)) (hi := (207572551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230687 / 1000000) = 1/(1000000 / 1230687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4151451 / 20000000) (207572551 / 1000000000) (Real.log (1230687 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230687 / 1000000) = -Real.log (1000000 / 1230687) := by
    rw [show ((1230687 / 1000000) : ℝ) = ((1000000 / 1230687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26225737 / 100000000) ≤ -Real.log (769313 / 1000000) ∧
    -Real.log (769313 / 1000000) ≤ (262257371 / 1000000000) := by
  have h := checkLog_sound (w := (230687 / 1769313)) (n := 12)
    (lo := (26225737 / 100000000)) (hi := (262257371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769313) = 1/(769313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-262257371 / 1000000000) (-26225737 / 100000000) (Real.log (769313 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (25979879 / 125000000) ≤ -Real.log (200000 / 246203) ∧
    -Real.log (200000 / 246203) ≤ (207839033 / 1000000000) := by
  have h := checkLog_sound (w := (46203 / 446203)) (n := 12)
    (lo := (25979879 / 125000000)) (hi := (207839033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246203 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246203 / 200000) = 1/(200000 / 246203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (25979879 / 125000000) (207839033 / 1000000000) (Real.log (246203 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (246203 / 200000) = -Real.log (200000 / 246203) := by
    rw [show ((246203 / 200000) : ℝ) = ((200000 / 246203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (52536763 / 200000000) ≤ -Real.log (153797 / 200000) ∧
    -Real.log (153797 / 200000) ≤ (32835477 / 125000000) := by
  have h := checkLog_sound (w := (46203 / 353797)) (n := 12)
    (lo := (52536763 / 200000000)) (hi := (32835477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153797) = 1/(153797 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32835477 / 125000000) (-52536763 / 200000000) (Real.log (153797 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (164240929 / 250000000) ≤ -Real.log (500000000000 / 964463332767) ∧
    -Real.log (500000000000 / 964463332767) ≤ (656963717 / 1000000000) := by
  have h := checkLog_sound (w := (464463332767 / 1464463332767)) (n := 12)
    (lo := (164240929 / 250000000)) (hi := (656963717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964463332767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964463332767 / 500000000000) = 1/(500000000000 / 964463332767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (164240929 / 250000000) (656963717 / 1000000000) (Real.log (964463332767 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (964463332767 / 500000000000) = -Real.log (500000000000 / 964463332767) := by
    rw [show ((964463332767 / 500000000000) : ℝ) = ((500000000000 / 964463332767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (82239171 / 125000000) ≤ -Real.log (500000000000 / 965379672547) ∧
    -Real.log (500000000000 / 965379672547) ≤ (657913369 / 1000000000) := by
  have h := checkLog_sound (w := (465379672547 / 1465379672547)) (n := 12)
    (lo := (82239171 / 125000000)) (hi := (657913369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965379672547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965379672547 / 500000000000) = 1/(500000000000 / 965379672547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (82239171 / 125000000) (657913369 / 1000000000) (Real.log (965379672547 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (965379672547 / 500000000000) = -Real.log (500000000000 / 965379672547) := by
    rw [show ((965379672547 / 500000000000) : ℝ) = ((500000000000 / 965379672547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2936437 / 6250000) ≤ -Real.log (250000000000 / 399930522427) ∧
    -Real.log (250000000000 / 399930522427) ≤ (469829921 / 1000000000) := by
  have h := checkLog_sound (w := (149930522427 / 649930522427)) (n := 12)
    (lo := (2936437 / 6250000)) (hi := (469829921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399930522427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399930522427 / 250000000000) = 1/(250000000000 / 399930522427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2936437 / 6250000) (469829921 / 1000000000) (Real.log (399930522427 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (399930522427 / 250000000000) = -Real.log (250000000000 / 399930522427) := by
    rw [show ((399930522427 / 250000000000) : ℝ) = ((250000000000 / 399930522427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (470522847 / 1000000000) ≤ -Real.log (500000000000 / 800415482747) ∧
    -Real.log (500000000000 / 800415482747) ≤ (14703839 / 31250000) := by
  have h := checkLog_sound (w := (300415482747 / 1300415482747)) (n := 12)
    (lo := (470522847 / 1000000000)) (hi := (14703839 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800415482747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800415482747 / 500000000000) = 1/(500000000000 / 800415482747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (470522847 / 1000000000) (14703839 / 31250000) (Real.log (800415482747 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (800415482747 / 500000000000) = -Real.log (500000000000 / 800415482747) := by
    rw [show ((800415482747 / 500000000000) : ℝ) = ((500000000000 / 800415482747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0397
