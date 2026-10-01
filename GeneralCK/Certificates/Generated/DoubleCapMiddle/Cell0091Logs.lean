import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0091
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

theorem reflection_log_1_neg : (170463293 / 500000000) ≤ -Real.log (32 / 45) ∧
    -Real.log (32 / 45) ≤ (340926587 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 77)) (n := 12)
    (lo := (170463293 / 500000000)) (hi := (340926587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45 / 32) = 1/(32 / 45) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170463293 / 500000000) (340926587 / 1000000000) (Real.log (45 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (45 / 32) = -Real.log (32 / 45) := by
    rw [show ((45 / 32) : ℝ) = ((32 / 45) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (521296923 / 1000000000) ≤ -Real.log (19 / 32) ∧
    -Real.log (19 / 32) ≤ (130324231 / 250000000) := by
  have h := checkLog_sound (w := (13 / 51)) (n := 12)
    (lo := (521296923 / 1000000000)) (hi := (130324231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 19) = 1/(19 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-130324231 / 250000000) (-521296923 / 1000000000) (Real.log (19 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170046453 / 500000000) ≤ -Real.log (2560 / 3597) ∧
    -Real.log (2560 / 3597) ≤ (340092907 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 6157)) (n := 12)
    (lo := (170046453 / 500000000)) (hi := (340092907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3597 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3597 / 2560) = 1/(2560 / 3597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170046453 / 500000000) (340092907 / 1000000000) (Real.log (3597 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3597 / 2560) = -Real.log (2560 / 3597) := by
    rw [show ((3597 / 2560) : ℝ) = ((2560 / 3597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1014307 / 1953125) ≤ -Real.log (1523 / 2560) ∧
    -Real.log (1523 / 2560) ≤ (103865037 / 200000000) := by
  have h := checkLog_sound (w := (1037 / 4083)) (n := 12)
    (lo := (1014307 / 1953125)) (hi := (103865037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1523) = 1/(1523 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-103865037 / 200000000) (-1014307 / 1953125) (Real.log (1523 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (594707107 / 1000000000) ≤ -Real.log (16 / 29) ∧
    -Real.log (16 / 29) ≤ (148676777 / 250000000) := by
  have h := checkLog_sound (w := (13 / 45)) (n := 12)
    (lo := (594707107 / 1000000000)) (hi := (148676777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 16) = 1/(16 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (594707107 / 1000000000) (148676777 / 250000000) (Real.log (29 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29 / 16) = -Real.log (16 / 29) := by
    rw [show ((29 / 16) : ℝ) = ((16 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104623527 / 62500000) ≤ -Real.log (3 / 16) ∧
    -Real.log (3 / 16) ≤ (334795287 / 200000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(4 / 3) = 1/(3 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-334795287 / 200000000) (-104623527 / 62500000) (Real.log (3 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (593413167 / 1000000000) ≤ -Real.log (1280 / 2317) ∧
    -Real.log (1280 / 2317) ≤ (37088323 / 62500000) := by
  have h := checkLog_sound (w := (1037 / 3597)) (n := 12)
    (lo := (593413167 / 1000000000)) (hi := (37088323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 1280) = 1/(1280 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (593413167 / 1000000000) (37088323 / 62500000) (Real.log (2317 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2317 / 1280) = -Real.log (1280 / 2317) := by
    rw [show ((2317 / 1280) : ℝ) = ((1280 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (207694239 / 125000000) ≤ -Real.log (243 / 1280) ∧
    -Real.log (243 / 1280) ≤ (332310783 / 200000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 243) = 1/(243 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-332310783 / 200000000) (-207694239 / 125000000) (Real.log (243 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (233612699 / 500000000) ≤ -Real.log (1000000 / 1595561) ∧
    -Real.log (1000000 / 1595561) ≤ (467225399 / 1000000000) := by
  have h := checkLog_sound (w := (595561 / 2595561)) (n := 12)
    (lo := (233612699 / 500000000)) (hi := (467225399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1595561 / 1000000) = 1/(1000000 / 1595561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (233612699 / 500000000) (467225399 / 1000000000) (Real.log (1595561 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1595561 / 1000000) = -Real.log (1000000 / 1595561) := by
    rw [show ((1595561 / 1000000) : ℝ) = ((1000000 / 1595561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226313589 / 250000000) ≤ -Real.log (404439 / 1000000) ∧
    -Real.log (404439 / 1000000) ≤ (452627179 / 500000000) := by
  have h := checkLog_sound (w := (95561 / 904439)) (n := 12)
    (lo := (26513397 / 125000000)) (hi := (212107177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 404439) = 1/(404439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452627179 / 500000000) (-226313589 / 250000000) (Real.log (404439 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (468433021 / 1000000000) ≤ -Real.log (1000000 / 1597489) ∧
    -Real.log (1000000 / 1597489) ≤ (234216511 / 500000000) := by
  have h := checkLog_sound (w := (597489 / 2597489)) (n := 12)
    (lo := (468433021 / 1000000000)) (hi := (234216511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1597489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1597489 / 1000000) = 1/(1000000 / 1597489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (468433021 / 1000000000) (234216511 / 500000000) (Real.log (1597489 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1597489 / 1000000) = -Real.log (1000000 / 1597489) := by
    rw [show ((1597489 / 1000000) : ℝ) = ((1000000 / 1597489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (227508213 / 250000000) ≤ -Real.log (402511 / 1000000) ∧
    -Real.log (402511 / 1000000) ≤ (455016427 / 500000000) := by
  have h := checkLog_sound (w := (97489 / 902511)) (n := 12)
    (lo := (27110709 / 125000000)) (hi := (216885673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 402511) = 1/(402511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-455016427 / 500000000) (-227508213 / 250000000) (Real.log (402511 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (191477489 / 500000000) ≤ -Real.log (250000 / 366653) ∧
    -Real.log (250000 / 366653) ≤ (382954979 / 1000000000) := by
  have h := checkLog_sound (w := (116653 / 616653)) (n := 12)
    (lo := (191477489 / 500000000)) (hi := (382954979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366653 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366653 / 250000) = 1/(250000 / 366653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (191477489 / 500000000) (382954979 / 1000000000) (Real.log (366653 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (366653 / 250000) = -Real.log (250000 / 366653) := by
    rw [show ((366653 / 250000) : ℝ) = ((250000 / 366653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (157126541 / 250000000) ≤ -Real.log (133347 / 250000) ∧
    -Real.log (133347 / 250000) ≤ (125701233 / 200000000) := by
  have h := checkLog_sound (w := (116653 / 383347)) (n := 12)
    (lo := (157126541 / 250000000)) (hi := (125701233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 133347) = 1/(133347 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125701233 / 200000000) (-157126541 / 250000000) (Real.log (133347 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192102349 / 500000000) ≤ -Real.log (500000 / 734223) ∧
    -Real.log (500000 / 734223) ≤ (384204699 / 1000000000) := by
  have h := checkLog_sound (w := (234223 / 1234223)) (n := 12)
    (lo := (192102349 / 500000000)) (hi := (384204699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734223 / 500000) = 1/(500000 / 734223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192102349 / 500000000) (384204699 / 1000000000) (Real.log (734223 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734223 / 500000) = -Real.log (500000 / 734223) := by
    rw [show ((734223 / 500000) : ℝ) = ((500000 / 734223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (631950487 / 1000000000) ≤ -Real.log (265777 / 500000) ∧
    -Real.log (265777 / 500000) ≤ (78993811 / 125000000) := by
  have h := checkLog_sound (w := (234223 / 765777)) (n := 12)
    (lo := (631950487 / 1000000000)) (hi := (78993811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 265777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 265777) = 1/(265777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78993811 / 125000000) (-631950487 / 1000000000) (Real.log (265777 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (274495951 / 200000000) ≤ -Real.log (500000000000 / 1972560756999) ∧
    -Real.log (500000000000 / 1972560756999) ≤ (1372479757 / 1000000000) := by
  have h := checkLog_sound (w := (972560756999 / 2972560756999)) (n := 12)
    (lo := (27173303 / 40000000)) (hi := (21229143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972560756999 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1972560756999 / 1000000000000) = 1/(500000000000 / 1972560756999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (274495951 / 200000000) (1372479757 / 1000000000) (Real.log (1972560756999 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1972560756999 / 500000000000) = -Real.log (500000000000 / 1972560756999) := by
    rw [show ((1972560756999 / 500000000000) : ℝ) = ((500000000000 / 1972560756999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (689232937 / 500000000) ≤ -Real.log (50000000000 / 198440415293) ∧
    -Real.log (50000000000 / 198440415293) ≤ (344616469 / 250000000) := by
  have h := checkLog_sound (w := (98440415293 / 298440415293)) (n := 12)
    (lo := (342659347 / 500000000)) (hi := (137063739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198440415293 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(198440415293 / 100000000000) = 1/(50000000000 / 198440415293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (689232937 / 500000000) (344616469 / 250000000) (Real.log (198440415293 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (198440415293 / 50000000000) = -Real.log (50000000000 / 198440415293) := by
    rw [show ((198440415293 / 50000000000) : ℝ) = ((50000000000 / 198440415293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (505730571 / 500000000) ≤ -Real.log (500000000000 / 1374807832197) ∧
    -Real.log (500000000000 / 1374807832197) ≤ (126432643 / 125000000) := by
  have h := checkLog_sound (w := (374807832197 / 2374807832197)) (n := 12)
    (lo := (159156981 / 500000000)) (hi := (318313963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374807832197 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1374807832197 / 1000000000000) = 1/(500000000000 / 1374807832197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (505730571 / 500000000) (126432643 / 125000000) (Real.log (1374807832197 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1374807832197 / 500000000000) = -Real.log (500000000000 / 1374807832197) := by
    rw [show ((1374807832197 / 500000000000) : ℝ) = ((500000000000 / 1374807832197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (203231037 / 200000000) ≤ -Real.log (250000000000 / 690638204209) ∧
    -Real.log (250000000000 / 690638204209) ≤ (1016155187 / 1000000000) := by
  have h := checkLog_sound (w := (190638204209 / 1190638204209)) (n := 12)
    (lo := (64601601 / 200000000)) (hi := (161504003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690638204209 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(690638204209 / 500000000000) = 1/(250000000000 / 690638204209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (203231037 / 200000000) (1016155187 / 1000000000) (Real.log (690638204209 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (690638204209 / 250000000000) = -Real.log (250000000000 / 690638204209) := by
    rw [show ((690638204209 / 250000000000) : ℝ) = ((250000000000 / 690638204209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0091
