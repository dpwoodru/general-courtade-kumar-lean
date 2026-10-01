import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0187
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

theorem reflection_log_1_neg : (271487187 / 1000000000) ≤ -Real.log (5120 / 6717) ∧
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


theorem reflection_log_1 : Bounds (271487187 / 1000000000) (67871797 / 250000000) (Real.log (6717 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6717 / 5120) = -Real.log (5120 / 6717) := by
    rw [show ((6717 / 5120) : ℝ) = ((5120 / 6717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (373841539 / 1000000000) ≤ -Real.log (3523 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-18692077 / 50000000) (-373841539 / 1000000000) (Real.log (3523 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (271040459 / 1000000000) ≤ -Real.log (2560 / 3357) ∧
    -Real.log (2560 / 3357) ≤ (13552023 / 50000000) := by
  have h := checkLog_sound (w := (797 / 5917)) (n := 12)
    (lo := (271040459 / 1000000000)) (hi := (13552023 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3357 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3357 / 2560) = 1/(2560 / 3357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (271040459 / 1000000000) (13552023 / 50000000) (Real.log (3357 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3357 / 2560) = -Real.log (2560 / 3357) := by
    rw [show ((3357 / 2560) : ℝ) = ((2560 / 3357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74598071 / 200000000) ≤ -Real.log (1763 / 2560) ∧
    -Real.log (1763 / 2560) ≤ (93247589 / 250000000) := by
  have h := checkLog_sound (w := (797 / 4323)) (n := 12)
    (lo := (74598071 / 200000000)) (hi := (93247589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1763) = 1/(1763 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-93247589 / 250000000) (-74598071 / 200000000) (Real.log (1763 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (484786401 / 1000000000) ≤ -Real.log (2560 / 4157) ∧
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


theorem reflection_log_5 : Bounds (484786401 / 1000000000) (242393201 / 500000000) (Real.log (4157 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4157 / 2560) = -Real.log (2560 / 4157) := by
    rw [show ((4157 / 2560) : ℝ) = ((2560 / 4157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7821673 / 8000000) ≤ -Real.log (963 / 2560) ∧
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


theorem reflection_log_6 : Bounds (-977709127 / 1000000000) (-7821673 / 8000000) (Real.log (963 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (242032233 / 500000000) ≤ -Real.log (1280 / 2077) ∧
    -Real.log (1280 / 2077) ≤ (484064467 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 3357)) (n := 12)
    (lo := (242032233 / 500000000)) (hi := (484064467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2077 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2077 / 1280) = 1/(1280 / 2077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (242032233 / 500000000) (484064467 / 1000000000) (Real.log (2077 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2077 / 1280) = -Real.log (1280 / 2077) := by
    rw [show ((2077 / 1280) : ℝ) = ((1280 / 2077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (487299351 / 500000000) ≤ -Real.log (483 / 1280) ∧
    -Real.log (483 / 1280) ≤ (60912419 / 62500000) := by
  have h := checkLog_sound (w := (157 / 1123)) (n := 12)
    (lo := (140725761 / 500000000)) (hi := (281451523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 483) = 1/(483 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-60912419 / 62500000) (-487299351 / 500000000) (Real.log (483 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18538921 / 50000000) ≤ -Real.log (500000 / 724431) ∧
    -Real.log (500000 / 724431) ≤ (370778421 / 1000000000) := by
  have h := checkLog_sound (w := (224431 / 1224431)) (n := 12)
    (lo := (18538921 / 50000000)) (hi := (370778421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724431 / 500000) = 1/(500000 / 724431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18538921 / 50000000) (370778421 / 1000000000) (Real.log (724431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (724431 / 500000) = -Real.log (500000 / 724431) := by
    rw [show ((724431 / 500000) : ℝ) = ((500000 / 724431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (595770047 / 1000000000) ≤ -Real.log (275569 / 500000) ∧
    -Real.log (275569 / 500000) ≤ (9308907 / 15625000) := by
  have h := checkLog_sound (w := (224431 / 775569)) (n := 12)
    (lo := (595770047 / 1000000000)) (hi := (9308907 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 275569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 275569) = 1/(275569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9308907 / 15625000) (-595770047 / 1000000000) (Real.log (275569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (185694529 / 500000000) ≤ -Real.log (1000000 / 1449747) ∧
    -Real.log (1000000 / 1449747) ≤ (371389059 / 1000000000) := by
  have h := checkLog_sound (w := (449747 / 2449747)) (n := 12)
    (lo := (185694529 / 500000000)) (hi := (371389059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449747 / 1000000) = 1/(1000000 / 1449747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (185694529 / 500000000) (371389059 / 1000000000) (Real.log (1449747 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1449747 / 1000000) = -Real.log (1000000 / 1449747) := by
    rw [show ((1449747 / 1000000) : ℝ) = ((1000000 / 1449747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (298688553 / 500000000) ≤ -Real.log (550253 / 1000000) ∧
    -Real.log (550253 / 1000000) ≤ (597377107 / 1000000000) := by
  have h := checkLog_sound (w := (449747 / 1550253)) (n := 12)
    (lo := (298688553 / 500000000)) (hi := (597377107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 550253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 550253) = 1/(550253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-597377107 / 1000000000) (-298688553 / 500000000) (Real.log (550253 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (289750431 / 1000000000) ≤ -Real.log (500000 / 668047) ∧
    -Real.log (500000 / 668047) ≤ (9054701 / 31250000) := by
  have h := checkLog_sound (w := (168047 / 1168047)) (n := 12)
    (lo := (289750431 / 1000000000)) (hi := (9054701 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668047 / 500000) = 1/(500000 / 668047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (289750431 / 1000000000) (9054701 / 31250000) (Real.log (668047 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (668047 / 500000) = -Real.log (500000 / 668047) := by
    rw [show ((668047 / 500000) : ℝ) = ((500000 / 668047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (81922941 / 200000000) ≤ -Real.log (331953 / 500000) ∧
    -Real.log (331953 / 500000) ≤ (204807353 / 500000000) := by
  have h := checkLog_sound (w := (168047 / 831953)) (n := 12)
    (lo := (81922941 / 200000000)) (hi := (204807353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331953) = 1/(331953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-204807353 / 500000000) (-81922941 / 200000000) (Real.log (331953 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (290304879 / 1000000000) ≤ -Real.log (200000 / 267367) ∧
    -Real.log (200000 / 267367) ≤ (3628811 / 12500000) := by
  have h := checkLog_sound (w := (67367 / 467367)) (n := 12)
    (lo := (290304879 / 1000000000)) (hi := (3628811 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267367 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267367 / 200000) = 1/(200000 / 267367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (290304879 / 1000000000) (3628811 / 12500000) (Real.log (267367 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (267367 / 200000) = -Real.log (200000 / 267367) := by
    rw [show ((267367 / 200000) : ℝ) = ((200000 / 267367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (8214629 / 20000000) ≤ -Real.log (132633 / 200000) ∧
    -Real.log (132633 / 200000) ≤ (410731451 / 1000000000) := by
  have h := checkLog_sound (w := (67367 / 332633)) (n := 12)
    (lo := (8214629 / 20000000)) (hi := (410731451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132633) = 1/(132633 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-410731451 / 1000000000) (-8214629 / 20000000) (Real.log (132633 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (966548467 / 1000000000) ≤ -Real.log (125000000000 / 328606900631) ∧
    -Real.log (125000000000 / 328606900631) ≤ (966548469 / 1000000000) := by
  have h := checkLog_sound (w := (78606900631 / 578606900631)) (n := 12)
    (lo := (273401287 / 1000000000)) (hi := (34175161 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328606900631 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328606900631 / 250000000000) = 1/(125000000000 / 328606900631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (966548467 / 1000000000) (966548469 / 1000000000) (Real.log (328606900631 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (328606900631 / 125000000000) = -Real.log (125000000000 / 328606900631) := by
    rw [show ((328606900631 / 125000000000) : ℝ) = ((125000000000 / 328606900631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (242191541 / 250000000) ≤ -Real.log (62500000000 / 164668229887) ∧
    -Real.log (62500000000 / 164668229887) ≤ (484383083 / 500000000) := by
  have h := checkLog_sound (w := (39668229887 / 289668229887)) (n := 12)
    (lo := (34452373 / 125000000)) (hi := (55123797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164668229887 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(164668229887 / 125000000000) = 1/(62500000000 / 164668229887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (242191541 / 250000000) (484383083 / 500000000) (Real.log (164668229887 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164668229887 / 62500000000) = -Real.log (62500000000 / 164668229887) := by
    rw [show ((164668229887 / 62500000000) : ℝ) = ((62500000000 / 164668229887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (699365137 / 1000000000) ≤ -Real.log (250000000000 / 503118664389) ∧
    -Real.log (250000000000 / 503118664389) ≤ (699365139 / 1000000000) := by
  have h := checkLog_sound (w := (3118664389 / 1003118664389)) (n := 12)
    (lo := (6217957 / 1000000000)) (hi := (3108979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503118664389 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(503118664389 / 500000000000) = 1/(250000000000 / 503118664389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (699365137 / 1000000000) (699365139 / 1000000000) (Real.log (503118664389 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (503118664389 / 250000000000) = -Real.log (250000000000 / 503118664389) := by
    rw [show ((503118664389 / 250000000000) : ℝ) = ((250000000000 / 503118664389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (70103633 / 100000000) ≤ -Real.log (15625000000 / 31497510989) ∧
    -Real.log (15625000000 / 31497510989) ≤ (175259083 / 250000000) := by
  have h := checkLog_sound (w := (247510989 / 62747510989)) (n := 12)
    (lo := (157783 / 20000000)) (hi := (7889151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31497510989 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31497510989 / 31250000000) = 1/(15625000000 / 31497510989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (70103633 / 100000000) (175259083 / 250000000) (Real.log (31497510989 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31497510989 / 15625000000) = -Real.log (15625000000 / 31497510989) := by
    rw [show ((31497510989 / 15625000000) : ℝ) = ((15625000000 / 31497510989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0187
