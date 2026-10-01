import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0046
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

theorem reflection_log_1_neg : (4721757 / 12500000) ≤ -Real.log (512 / 747) ∧
    -Real.log (512 / 747) ≤ (377740561 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 1259)) (n := 12)
    (lo := (4721757 / 12500000)) (hi := (377740561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 512) = 1/(512 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4721757 / 12500000) (377740561 / 1000000000) (Real.log (747 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (747 / 512) = -Real.log (512 / 747) := by
    rw [show ((747 / 512) : ℝ) = ((512 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307153559 / 500000000) ≤ -Real.log (277 / 512) ∧
    -Real.log (277 / 512) ≤ (614307119 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 789)) (n := 12)
    (lo := (307153559 / 500000000)) (hi := (614307119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 277) = 1/(277 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-614307119 / 1000000000) (-307153559 / 500000000) (Real.log (277 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5889641 / 15625000) ≤ -Real.log (640 / 933) ∧
    -Real.log (640 / 933) ≤ (15077481 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1573)) (n := 12)
    (lo := (5889641 / 15625000)) (hi := (15077481 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 640) = 1/(640 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5889641 / 15625000) (15077481 / 40000000) (Real.log (933 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (933 / 640) = -Real.log (640 / 933) := by
    rw [show ((933 / 640) : ℝ) = ((640 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (153035849 / 250000000) ≤ -Real.log (347 / 640) ∧
    -Real.log (347 / 640) ≤ (612143397 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 987)) (n := 12)
    (lo := (153035849 / 250000000)) (hi := (612143397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 347) = 1/(347 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-612143397 / 1000000000) (-153035849 / 250000000) (Real.log (347 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (651266683 / 1000000000) ≤ -Real.log (256 / 491) ∧
    -Real.log (256 / 491) ≤ (162816671 / 250000000) := by
  have h := checkLog_sound (w := (235 / 747)) (n := 12)
    (lo := (651266683 / 1000000000)) (hi := (162816671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 256) = 1/(256 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (651266683 / 1000000000) (162816671 / 250000000) (Real.log (491 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (491 / 256) = -Real.log (256 / 491) := by
    rw [show ((491 / 256) : ℝ) = ((256 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (500131001 / 200000000) ≤ -Real.log (21 / 256) ∧
    -Real.log (21 / 256) ≤ (2500655009 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 21) = 1/(21 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2500655009 / 1000000000) (-500131001 / 200000000) (Real.log (21 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (32502197 / 50000000) ≤ -Real.log (320 / 613) ∧
    -Real.log (320 / 613) ≤ (650043941 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 933)) (n := 12)
    (lo := (32502197 / 50000000)) (hi := (650043941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 320) = 1/(320 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (32502197 / 50000000) (650043941 / 1000000000) (Real.log (613 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (613 / 320) = -Real.log (320 / 613) := by
    rw [show ((613 / 320) : ℝ) = ((320 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77265129 / 31250000) ≤ -Real.log (27 / 320) ∧
    -Real.log (27 / 320) ≤ (618121033 / 250000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 27) = 1/(27 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-618121033 / 250000000) (-77265129 / 31250000) (Real.log (27 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65353933 / 125000000) ≤ -Real.log (1000000 / 1686797) ∧
    -Real.log (1000000 / 1686797) ≤ (104566293 / 200000000) := by
  have h := checkLog_sound (w := (686797 / 2686797)) (n := 12)
    (lo := (65353933 / 125000000)) (hi := (104566293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1686797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1686797 / 1000000) = 1/(1000000 / 1686797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65353933 / 125000000) (104566293 / 200000000) (Real.log (1686797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1686797 / 1000000) = -Real.log (1000000 / 1686797) := by
    rw [show ((1686797 / 1000000) : ℝ) = ((1000000 / 1686797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (232180747 / 200000000) ≤ -Real.log (313203 / 1000000) ∧
    -Real.log (313203 / 1000000) ≤ (1160903737 / 1000000000) := by
  have h := checkLog_sound (w := (186797 / 813203)) (n := 12)
    (lo := (93551311 / 200000000)) (hi := (116939139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 313203) = 1/(313203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1160903737 / 1000000000) (-232180747 / 200000000) (Real.log (313203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131030607 / 250000000) ≤ -Real.log (62500 / 105561) ∧
    -Real.log (62500 / 105561) ≤ (524122429 / 1000000000) := by
  have h := checkLog_sound (w := (43061 / 168061)) (n := 12)
    (lo := (131030607 / 250000000)) (hi := (524122429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105561 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105561 / 62500) = 1/(62500 / 105561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131030607 / 250000000) (524122429 / 1000000000) (Real.log (105561 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (105561 / 62500) = -Real.log (62500 / 105561) := by
    rw [show ((105561 / 62500) : ℝ) = ((62500 / 105561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (583942599 / 500000000) ≤ -Real.log (19439 / 62500) ∧
    -Real.log (19439 / 62500) ≤ (2919713 / 2500000) := by
  have h := checkLog_sound (w := (11811 / 50689)) (n := 12)
    (lo := (237369009 / 500000000)) (hi := (474738019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 19439) = 1/(19439 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2919713 / 2500000) (-583942599 / 500000000) (Real.log (19439 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (443079403 / 1000000000) ≤ -Real.log (125000 / 194687) ∧
    -Real.log (125000 / 194687) ≤ (110769851 / 250000000) := by
  have h := checkLog_sound (w := (69687 / 319687)) (n := 12)
    (lo := (443079403 / 1000000000)) (hi := (110769851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194687 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194687 / 125000) = 1/(125000 / 194687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (443079403 / 1000000000) (110769851 / 250000000) (Real.log (194687 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (194687 / 125000) = -Real.log (125000 / 194687) := by
    rw [show ((194687 / 125000) : ℝ) = ((125000 / 194687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (407652887 / 500000000) ≤ -Real.log (55313 / 125000) ∧
    -Real.log (55313 / 125000) ≤ (50956611 / 62500000) := by
  have h := checkLog_sound (w := (7187 / 117813)) (n := 12)
    (lo := (61079297 / 500000000)) (hi := (24431719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55313) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 55313) = 1/(55313 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-50956611 / 62500000) (-407652887 / 500000000) (Real.log (55313 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22227079 / 50000000) ≤ -Real.log (40000 / 62391) ∧
    -Real.log (40000 / 62391) ≤ (444541581 / 1000000000) := by
  have h := checkLog_sound (w := (22391 / 102391)) (n := 12)
    (lo := (22227079 / 50000000)) (hi := (444541581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62391 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62391 / 40000) = 1/(40000 / 62391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22227079 / 50000000) (444541581 / 1000000000) (Real.log (62391 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (62391 / 40000) = -Real.log (40000 / 62391) := by
    rw [show ((62391 / 40000) : ℝ) = ((40000 / 62391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (410234659 / 500000000) ≤ -Real.log (17609 / 40000) ∧
    -Real.log (17609 / 40000) ≤ (20511733 / 25000000) := by
  have h := checkLog_sound (w := (2391 / 37609)) (n := 12)
    (lo := (63661069 / 500000000)) (hi := (127322139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 17609) = 1/(17609 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-20511733 / 25000000) (-410234659 / 500000000) (Real.log (17609 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1683735199 / 1000000000) ≤ -Real.log (500000000000 / 2692817437891) ∧
    -Real.log (500000000000 / 2692817437891) ≤ (841867601 / 500000000) := by
  have h := checkLog_sound (w := (692817437891 / 4692817437891)) (n := 12)
    (lo := (297440839 / 1000000000)) (hi := (7436021 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2692817437891 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2692817437891 / 2000000000000) = 1/(500000000000 / 2692817437891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1683735199 / 1000000000) (841867601 / 500000000) (Real.log (2692817437891 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2692817437891 / 500000000000) = -Real.log (500000000000 / 2692817437891) := by
    rw [show ((2692817437891 / 500000000000) : ℝ) = ((500000000000 / 2692817437891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (846003813 / 500000000) ≤ -Real.log (500000000000 / 2715185966357) ∧
    -Real.log (500000000000 / 2715185966357) ≤ (1692007629 / 1000000000) := by
  have h := checkLog_sound (w := (715185966357 / 4715185966357)) (n := 12)
    (lo := (152856633 / 500000000)) (hi := (305713267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2715185966357 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2715185966357 / 2000000000000) = 1/(500000000000 / 2715185966357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (846003813 / 500000000) (1692007629 / 1000000000) (Real.log (2715185966357 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2715185966357 / 500000000000) = -Real.log (500000000000 / 2715185966357) := by
    rw [show ((2715185966357 / 500000000000) : ℝ) = ((500000000000 / 2715185966357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1258385177 / 1000000000) ≤ -Real.log (500000000000 / 1759866577477) ∧
    -Real.log (500000000000 / 1759866577477) ≤ (1258385179 / 1000000000) := by
  have h := checkLog_sound (w := (759866577477 / 2759866577477)) (n := 12)
    (lo := (565237997 / 1000000000)) (hi := (282618999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759866577477 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1759866577477 / 1000000000000) = 1/(500000000000 / 1759866577477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1258385177 / 1000000000) (1258385179 / 1000000000) (Real.log (1759866577477 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1759866577477 / 500000000000) = -Real.log (500000000000 / 1759866577477) := by
    rw [show ((1759866577477 / 500000000000) : ℝ) = ((500000000000 / 1759866577477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (632505449 / 500000000) ≤ -Real.log (500000000000 / 1771565676643) ∧
    -Real.log (500000000000 / 1771565676643) ≤ (12650109 / 10000000) := by
  have h := checkLog_sound (w := (771565676643 / 2771565676643)) (n := 12)
    (lo := (285931859 / 500000000)) (hi := (571863719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771565676643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1771565676643 / 1000000000000) = 1/(500000000000 / 1771565676643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (632505449 / 500000000) (12650109 / 10000000) (Real.log (1771565676643 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1771565676643 / 500000000000) = -Real.log (500000000000 / 1771565676643) := by
    rw [show ((1771565676643 / 500000000000) : ℝ) = ((500000000000 / 1771565676643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0046
