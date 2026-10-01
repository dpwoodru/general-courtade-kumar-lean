import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0367
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

theorem reflection_log_1_neg : (8324369 / 40000000) ≤ -Real.log (10240 / 12609) ∧
    -Real.log (10240 / 12609) ≤ (104054613 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 22849)) (n := 12)
    (lo := (8324369 / 40000000)) (hi := (104054613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12609 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12609 / 10240) = 1/(10240 / 12609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8324369 / 40000000) (104054613 / 500000000) (Real.log (12609 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12609 / 10240) = -Real.log (10240 / 12609) := by
    rw [show ((12609 / 10240) : ℝ) = ((10240 / 12609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (526233 / 2000000) ≤ -Real.log (7871 / 10240) ∧
    -Real.log (7871 / 10240) ≤ (263116501 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 18111)) (n := 12)
    (lo := (526233 / 2000000)) (hi := (263116501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7871) = 1/(7871 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-263116501 / 1000000000) (-526233 / 2000000) (Real.log (7871 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (207871271 / 1000000000) ≤ -Real.log (5120 / 6303) ∧
    -Real.log (5120 / 6303) ≤ (25983909 / 125000000) := by
  have h := checkLog_sound (w := (1183 / 11423)) (n := 12)
    (lo := (207871271 / 1000000000)) (hi := (25983909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6303 / 5120) = 1/(5120 / 6303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (207871271 / 1000000000) (25983909 / 125000000) (Real.log (6303 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6303 / 5120) = -Real.log (5120 / 6303) := by
    rw [show ((6303 / 5120) : ℝ) = ((5120 / 6303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (262735427 / 1000000000) ≤ -Real.log (3937 / 5120) ∧
    -Real.log (3937 / 5120) ≤ (65683857 / 250000000) := by
  have h := checkLog_sound (w := (1183 / 9057)) (n := 12)
    (lo := (262735427 / 1000000000)) (hi := (65683857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3937) = 1/(3937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65683857 / 250000000) (-262735427 / 1000000000) (Real.log (3937 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190140419 / 500000000) ≤ -Real.log (5120 / 7489) ∧
    -Real.log (5120 / 7489) ≤ (380280839 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 12609)) (n := 12)
    (lo := (190140419 / 500000000)) (hi := (380280839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7489 / 5120) = 1/(5120 / 7489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190140419 / 500000000) (380280839 / 1000000000) (Real.log (7489 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7489 / 5120) = -Real.log (5120 / 7489) := by
    rw [show ((7489 / 5120) : ℝ) = ((5120 / 7489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (621189957 / 1000000000) ≤ -Real.log (2751 / 5120) ∧
    -Real.log (2751 / 5120) ≤ (310594979 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 7871)) (n := 12)
    (lo := (621189957 / 1000000000)) (hi := (310594979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2751) = 1/(2751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-310594979 / 500000000) (-621189957 / 1000000000) (Real.log (2751 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37988017 / 100000000) ≤ -Real.log (2560 / 3743) ∧
    -Real.log (2560 / 3743) ≤ (379880171 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 6303)) (n := 12)
    (lo := (37988017 / 100000000)) (hi := (379880171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3743 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3743 / 2560) = 1/(2560 / 3743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37988017 / 100000000) (379880171 / 1000000000) (Real.log (3743 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3743 / 2560) = -Real.log (2560 / 3743) := by
    rw [show ((3743 / 2560) : ℝ) = ((2560 / 3743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (310050019 / 500000000) ≤ -Real.log (1377 / 2560) ∧
    -Real.log (1377 / 2560) ≤ (620100039 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 3937)) (n := 12)
    (lo := (310050019 / 500000000)) (hi := (620100039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1377) = 1/(1377 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-620100039 / 1000000000) (-310050019 / 500000000) (Real.log (1377 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142574057 / 500000000) ≤ -Real.log (1000000 / 1329959) ∧
    -Real.log (1000000 / 1329959) ≤ (57029623 / 200000000) := by
  have h := checkLog_sound (w := (329959 / 2329959)) (n := 12)
    (lo := (142574057 / 500000000)) (hi := (57029623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329959 / 1000000) = 1/(1000000 / 1329959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142574057 / 500000000) (57029623 / 200000000) (Real.log (1329959 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1329959 / 1000000) = -Real.log (1000000 / 1329959) := by
    rw [show ((1329959 / 1000000) : ℝ) = ((1000000 / 1329959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (200208187 / 500000000) ≤ -Real.log (670041 / 1000000) ∧
    -Real.log (670041 / 1000000) ≤ (3203331 / 8000000) := by
  have h := checkLog_sound (w := (329959 / 1670041)) (n := 12)
    (lo := (200208187 / 500000000)) (hi := (3203331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670041) = 1/(670041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3203331 / 8000000) (-200208187 / 500000000) (Real.log (670041 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (285469877 / 1000000000) ≤ -Real.log (1000000 / 1330387) ∧
    -Real.log (1000000 / 1330387) ≤ (142734939 / 500000000) := by
  have h := checkLog_sound (w := (330387 / 2330387)) (n := 12)
    (lo := (285469877 / 1000000000)) (hi := (142734939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330387 / 1000000) = 1/(1000000 / 1330387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (285469877 / 1000000000) (142734939 / 500000000) (Real.log (1330387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1330387 / 1000000) = -Real.log (1000000 / 1330387) := by
    rw [show ((1330387 / 1000000) : ℝ) = ((1000000 / 1330387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80211069 / 200000000) ≤ -Real.log (669613 / 1000000) ∧
    -Real.log (669613 / 1000000) ≤ (200527673 / 500000000) := by
  have h := checkLog_sound (w := (330387 / 1669613)) (n := 12)
    (lo := (80211069 / 200000000)) (hi := (200527673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669613) = 1/(669613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200527673 / 500000000) (-80211069 / 200000000) (Real.log (669613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215566921 / 1000000000) ≤ -Real.log (200000 / 248113) ∧
    -Real.log (200000 / 248113) ≤ (107783461 / 500000000) := by
  have h := checkLog_sound (w := (48113 / 448113)) (n := 12)
    (lo := (215566921 / 1000000000)) (hi := (107783461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248113 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248113 / 200000) = 1/(200000 / 248113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215566921 / 1000000000) (107783461 / 500000000) (Real.log (248113 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (248113 / 200000) = -Real.log (200000 / 248113) := by
    rw [show ((248113 / 200000) : ℝ) = ((200000 / 248113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (275180543 / 1000000000) ≤ -Real.log (151887 / 200000) ∧
    -Real.log (151887 / 200000) ≤ (537462 / 1953125) := by
  have h := checkLog_sound (w := (48113 / 351887)) (n := 12)
    (lo := (275180543 / 1000000000)) (hi := (537462 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151887) = 1/(151887 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-537462 / 1953125) (-275180543 / 1000000000) (Real.log (151887 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (43166901 / 200000000) ≤ -Real.log (1000000 / 1240897) ∧
    -Real.log (1000000 / 1240897) ≤ (107917253 / 500000000) := by
  have h := checkLog_sound (w := (240897 / 2240897)) (n := 12)
    (lo := (43166901 / 200000000)) (hi := (107917253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240897 / 1000000) = 1/(1000000 / 1240897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43166901 / 200000000) (107917253 / 500000000) (Real.log (1240897 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1240897 / 1000000) = -Real.log (1000000 / 1240897) := by
    rw [show ((1240897 / 1000000) : ℝ) = ((1000000 / 1240897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55123561 / 200000000) ≤ -Real.log (759103 / 1000000) ∧
    -Real.log (759103 / 1000000) ≤ (137808903 / 500000000) := by
  have h := checkLog_sound (w := (240897 / 1759103)) (n := 12)
    (lo := (55123561 / 200000000)) (hi := (137808903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759103) = 1/(759103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-137808903 / 500000000) (-55123561 / 200000000) (Real.log (759103 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (685564489 / 1000000000) ≤ -Real.log (62500000000 / 124055748081) ∧
    -Real.log (62500000000 / 124055748081) ≤ (68556449 / 100000000) := by
  have h := checkLog_sound (w := (61555748081 / 186555748081)) (n := 12)
    (lo := (685564489 / 1000000000)) (hi := (68556449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124055748081 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124055748081 / 62500000000) = 1/(62500000000 / 124055748081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (685564489 / 1000000000) (68556449 / 100000000) (Real.log (124055748081 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (124055748081 / 62500000000) = -Real.log (62500000000 / 124055748081) := by
    rw [show ((124055748081 / 62500000000) : ℝ) = ((62500000000 / 124055748081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (343262611 / 500000000) ≤ -Real.log (250000000000 / 496699959529) ∧
    -Real.log (250000000000 / 496699959529) ≤ (686525223 / 1000000000) := by
  have h := checkLog_sound (w := (246699959529 / 746699959529)) (n := 12)
    (lo := (343262611 / 500000000)) (hi := (686525223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496699959529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496699959529 / 250000000000) = 1/(250000000000 / 496699959529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (343262611 / 500000000) (686525223 / 1000000000) (Real.log (496699959529 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (496699959529 / 250000000000) = -Real.log (250000000000 / 496699959529) := by
    rw [show ((496699959529 / 250000000000) : ℝ) = ((250000000000 / 496699959529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (61343433 / 125000000) ≤ -Real.log (31250000000 / 51048024189) ∧
    -Real.log (31250000000 / 51048024189) ≤ (98149493 / 200000000) := by
  have h := checkLog_sound (w := (19798024189 / 82298024189)) (n := 12)
    (lo := (61343433 / 125000000)) (hi := (98149493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51048024189 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51048024189 / 31250000000) = 1/(31250000000 / 51048024189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (61343433 / 125000000) (98149493 / 200000000) (Real.log (51048024189 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51048024189 / 31250000000) = -Real.log (31250000000 / 51048024189) := by
    rw [show ((51048024189 / 31250000000) : ℝ) = ((31250000000 / 51048024189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (491452311 / 1000000000) ≤ -Real.log (125000000000 / 204336071653) ∧
    -Real.log (125000000000 / 204336071653) ≤ (61431539 / 125000000) := by
  have h := checkLog_sound (w := (79336071653 / 329336071653)) (n := 12)
    (lo := (491452311 / 1000000000)) (hi := (61431539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204336071653 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204336071653 / 125000000000) = 1/(125000000000 / 204336071653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (491452311 / 1000000000) (61431539 / 125000000) (Real.log (204336071653 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (204336071653 / 125000000000) = -Real.log (125000000000 / 204336071653) := by
    rw [show ((204336071653 / 125000000000) : ℝ) = ((125000000000 / 204336071653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0367
