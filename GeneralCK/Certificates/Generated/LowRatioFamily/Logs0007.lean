import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_448_neg : (166645077 / 1000000000) ≤ -Real.log (1693 / 2000) ∧
    -Real.log (1693 / 2000) ≤ (83322539 / 500000000) := by
  have h := checkLog_sound (w := (307 / 3693)) (n := 12)
    (lo := (166645077 / 1000000000)) (hi := (83322539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1693) = 1/(1693 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_448 : Bounds (-83322539 / 500000000) (-166645077 / 1000000000) (Real.log (1693 / 2000)) := by
  have h := reflection_log_448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_449_neg : (9593 / 62500000) ≤ -Real.log (2000000 / 2000307) ∧
    -Real.log (2000000 / 2000307) ≤ (153489 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 4000307)) (n := 12)
    (lo := (9593 / 62500000)) (hi := (153489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000307 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000307 / 2000000) = 1/(2000000 / 2000307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_449 : Bounds (9593 / 62500000) (153489 / 1000000000) (Real.log (2000307 / 2000000)) := by
  have h := reflection_log_449_neg
  have he : Real.log (2000307 / 2000000) = -Real.log (2000000 / 2000307) := by
    rw [show ((2000307 / 2000000) : ℝ) = ((2000000 / 2000307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_450_neg : (153511 / 1000000000) ≤ -Real.log (1999693 / 2000000) ∧
    -Real.log (1999693 / 2000000) ≤ (19189 / 125000000) := by
  have h := checkLog_sound (w := (307 / 3999693)) (n := 12)
    (lo := (153511 / 1000000000)) (hi := (19189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999693) = 1/(1999693 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_450 : Bounds (-19189 / 125000000) (-153511 / 1000000000) (Real.log (1999693 / 2000000)) := by
  have h := reflection_log_450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_451_neg : (741339 / 10000000) ≤ -Real.log (1000000 / 1076951) ∧
    -Real.log (1000000 / 1076951) ≤ (74133901 / 1000000000) := by
  have h := checkLog_sound (w := (76951 / 2076951)) (n := 12)
    (lo := (741339 / 10000000)) (hi := (74133901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076951 / 1000000) = 1/(1000000 / 1076951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_451 : Bounds (741339 / 10000000) (74133901 / 1000000000) (Real.log (1076951 / 1000000)) := by
  have h := reflection_log_451_neg
  have he : Real.log (1076951 / 1000000) = -Real.log (1000000 / 1076951) := by
    rw [show ((1076951 / 1000000) : ℝ) = ((1000000 / 1076951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_452_neg : (40036479 / 500000000) ≤ -Real.log (923049 / 1000000) ∧
    -Real.log (923049 / 1000000) ≤ (80072959 / 1000000000) := by
  have h := checkLog_sound (w := (76951 / 1923049)) (n := 12)
    (lo := (40036479 / 500000000)) (hi := (80072959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923049) = 1/(923049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_452 : Bounds (-80072959 / 1000000000) (-40036479 / 500000000) (Real.log (923049 / 1000000)) := by
  have h := reflection_log_452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_453_neg : (37161653 / 500000000) ≤ -Real.log (200000 / 215431) ∧
    -Real.log (200000 / 215431) ≤ (74323307 / 1000000000) := by
  have h := checkLog_sound (w := (15431 / 415431)) (n := 12)
    (lo := (37161653 / 500000000)) (hi := (74323307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215431 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215431 / 200000) = 1/(200000 / 215431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_453 : Bounds (37161653 / 500000000) (74323307 / 1000000000) (Real.log (215431 / 200000)) := by
  have h := reflection_log_453_neg
  have he : Real.log (215431 / 200000) = -Real.log (200000 / 215431) := by
    rw [show ((215431 / 200000) : ℝ) = ((200000 / 215431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_454_neg : (80293989 / 1000000000) ≤ -Real.log (184569 / 200000) ∧
    -Real.log (184569 / 200000) ≤ (8029399 / 100000000) := by
  have h := checkLog_sound (w := (15431 / 384569)) (n := 12)
    (lo := (80293989 / 1000000000)) (hi := (8029399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184569) = 1/(184569 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_454 : Bounds (-8029399 / 100000000) (-80293989 / 1000000000) (Real.log (184569 / 200000)) := by
  have h := reflection_log_454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_455_neg : (5970683 / 1000000000) ≤ -Real.log (39761884239 / 40000000000) ∧
    -Real.log (39761884239 / 40000000000) ≤ (1492671 / 250000000) := by
  have h := checkLog_sound (w := (238115761 / 79761884239)) (n := 12)
    (lo := (5970683 / 1000000000)) (hi := (1492671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39761884239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39761884239) = 1/(39761884239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_455 : Bounds (-1492671 / 250000000) (-5970683 / 1000000000) (Real.log (39761884239 / 40000000000)) := by
  have h := reflection_log_455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_456_neg : (5939057 / 1000000000) ≤ -Real.log (994078543599 / 1000000000000) ∧
    -Real.log (994078543599 / 1000000000000) ≤ (2969529 / 500000000) := by
  have h := checkLog_sound (w := (5921456401 / 1994078543599)) (n := 12)
    (lo := (5939057 / 1000000000)) (hi := (2969529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994078543599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994078543599) = 1/(994078543599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_456 : Bounds (-2969529 / 500000000) (-5939057 / 1000000000) (Real.log (994078543599 / 1000000000000)) := by
  have h := reflection_log_456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_457_neg : (77103429 / 500000000) ≤ -Real.log (250000000000 / 291683052579) ∧
    -Real.log (250000000000 / 291683052579) ≤ (154206859 / 1000000000) := by
  have h := checkLog_sound (w := (41683052579 / 541683052579)) (n := 12)
    (lo := (77103429 / 500000000)) (hi := (154206859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291683052579 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291683052579 / 250000000000) = 1/(250000000000 / 291683052579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_457 : Bounds (77103429 / 500000000) (154206859 / 1000000000) (Real.log (291683052579 / 250000000000)) := by
  have h := reflection_log_457_neg
  have he : Real.log (291683052579 / 250000000000) = -Real.log (250000000000 / 291683052579) := by
    rw [show ((291683052579 / 250000000000) : ℝ) = ((250000000000 / 291683052579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_458_neg : (30923459 / 200000000) ≤ -Real.log (250000000000 / 291802794619) ∧
    -Real.log (250000000000 / 291802794619) ≤ (9663581 / 62500000) := by
  have h := checkLog_sound (w := (41802794619 / 541802794619)) (n := 12)
    (lo := (30923459 / 200000000)) (hi := (9663581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291802794619 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291802794619 / 250000000000) = 1/(250000000000 / 291802794619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_458 : Bounds (30923459 / 200000000) (9663581 / 62500000) (Real.log (291802794619 / 250000000000)) := by
  have h := reflection_log_458_neg
  have he : Real.log (291802794619 / 250000000000) = -Real.log (250000000000 / 291802794619) := by
    rw [show ((291802794619 / 250000000000) : ℝ) = ((250000000000 / 291802794619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_459_neg : (309241053 / 1000000000) ≤ -Real.log (250000000000 / 340597684857) ∧
    -Real.log (250000000000 / 340597684857) ≤ (154620527 / 500000000) := by
  have h := checkLog_sound (w := (90597684857 / 590597684857)) (n := 12)
    (lo := (309241053 / 1000000000)) (hi := (154620527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340597684857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340597684857 / 250000000000) = 1/(250000000000 / 340597684857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_459 : Bounds (309241053 / 1000000000) (154620527 / 500000000) (Real.log (340597684857 / 250000000000)) := by
  have h := reflection_log_459_neg
  have he : Real.log (340597684857 / 250000000000) = -Real.log (250000000000 / 340597684857) := by
    rw [show ((340597684857 / 250000000000) : ℝ) = ((250000000000 / 340597684857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_460_neg : (77361469 / 250000000) ≤ -Real.log (500000000000 / 681334908447) ∧
    -Real.log (500000000000 / 681334908447) ≤ (309445877 / 1000000000) := by
  have h := checkLog_sound (w := (181334908447 / 1181334908447)) (n := 12)
    (lo := (77361469 / 250000000)) (hi := (309445877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681334908447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681334908447 / 500000000000) = 1/(500000000000 / 681334908447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_460 : Bounds (77361469 / 250000000) (309445877 / 1000000000) (Real.log (681334908447 / 500000000000)) := by
  have h := reflection_log_460_neg
  have he : Real.log (681334908447 / 500000000000) = -Real.log (500000000000 / 681334908447) := by
    rw [show ((681334908447 / 500000000000) : ℝ) = ((500000000000 / 681334908447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_461_neg : (142887487 / 1000000000) ≤ -Real.log (625 / 721) ∧
    -Real.log (625 / 721) ≤ (2232617 / 15625000) := by
  have h := checkLog_sound (w := (48 / 673)) (n := 12)
    (lo := (142887487 / 1000000000)) (hi := (2232617 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 625) = 1/(625 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_461 : Bounds (142887487 / 1000000000) (2232617 / 15625000) (Real.log (721 / 625)) := by
  have h := reflection_log_461_neg
  have he : Real.log (721 / 625) = -Real.log (625 / 721) := by
    rw [show ((721 / 625) : ℝ) = ((625 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_462_neg : (166763217 / 1000000000) ≤ -Real.log (529 / 625) ∧
    -Real.log (529 / 625) ≤ (83381609 / 500000000) := by
  have h := checkLog_sound (w := (48 / 577)) (n := 12)
    (lo := (166763217 / 1000000000)) (hi := (83381609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 529) = 1/(529 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_462 : Bounds (-83381609 / 500000000) (-166763217 / 1000000000) (Real.log (529 / 625)) := by
  have h := reflection_log_462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_463_neg : (38397 / 250000000) ≤ -Real.log (78125 / 78137) ∧
    -Real.log (78125 / 78137) ≤ (153589 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 78131)) (n := 12)
    (lo := (38397 / 250000000)) (hi := (153589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78137 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78137 / 78125) = 1/(78125 / 78137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_463 : Bounds (38397 / 250000000) (153589 / 1000000000) (Real.log (78137 / 78125)) := by
  have h := reflection_log_463_neg
  have he : Real.log (78137 / 78125) = -Real.log (78125 / 78137) := by
    rw [show ((78137 / 78125) : ℝ) = ((78125 / 78137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_464_neg : (153611 / 1000000000) ≤ -Real.log (78113 / 78125) ∧
    -Real.log (78113 / 78125) ≤ (38403 / 250000000) := by
  have h := checkLog_sound (w := (6 / 78119)) (n := 12)
    (lo := (153611 / 1000000000)) (hi := (38403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78113) = 1/(78113 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_464 : Bounds (-38403 / 250000000) (-153611 / 1000000000) (Real.log (78113 / 78125)) := by
  have h := reflection_log_464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_465_neg : (37090163 / 500000000) ≤ -Real.log (1000000 / 1077001) ∧
    -Real.log (1000000 / 1077001) ≤ (74180327 / 1000000000) := by
  have h := checkLog_sound (w := (77001 / 2077001)) (n := 12)
    (lo := (37090163 / 500000000)) (hi := (74180327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077001 / 1000000) = 1/(1000000 / 1077001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_465 : Bounds (37090163 / 500000000) (74180327 / 1000000000) (Real.log (1077001 / 1000000)) := by
  have h := reflection_log_465_neg
  have he : Real.log (1077001 / 1000000) = -Real.log (1000000 / 1077001) := by
    rw [show ((1077001 / 1000000) : ℝ) = ((1000000 / 1077001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_466_neg : (80127127 / 1000000000) ≤ -Real.log (922999 / 1000000) ∧
    -Real.log (922999 / 1000000) ≤ (10015891 / 125000000) := by
  have h := checkLog_sound (w := (77001 / 1922999)) (n := 12)
    (lo := (80127127 / 1000000000)) (hi := (10015891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922999) = 1/(922999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_466 : Bounds (-10015891 / 125000000) (-80127127 / 1000000000) (Real.log (922999 / 1000000)) := by
  have h := reflection_log_466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_467_neg : (74370651 / 1000000000) ≤ -Real.log (500000 / 538603) ∧
    -Real.log (500000 / 538603) ≤ (18592663 / 250000000) := by
  have h := checkLog_sound (w := (38603 / 1038603)) (n := 12)
    (lo := (74370651 / 1000000000)) (hi := (18592663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538603 / 500000) = 1/(500000 / 538603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_467 : Bounds (74370651 / 1000000000) (18592663 / 250000000) (Real.log (538603 / 500000)) := by
  have h := reflection_log_467_neg
  have he : Real.log (538603 / 500000) = -Real.log (500000 / 538603) := by
    rw [show ((538603 / 500000) : ℝ) = ((500000 / 538603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_468_neg : (40174627 / 500000000) ≤ -Real.log (461397 / 500000) ∧
    -Real.log (461397 / 500000) ≤ (16069851 / 200000000) := by
  have h := checkLog_sound (w := (38603 / 961397)) (n := 12)
    (lo := (40174627 / 500000000)) (hi := (16069851 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461397) = 1/(461397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_468 : Bounds (-16069851 / 200000000) (-40174627 / 500000000) (Real.log (461397 / 500000)) := by
  have h := reflection_log_468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_469_neg : (2989301 / 500000000) ≤ -Real.log (248509808391 / 250000000000) ∧
    -Real.log (248509808391 / 250000000000) ≤ (5978603 / 1000000000) := by
  have h := checkLog_sound (w := (1490191609 / 498509808391)) (n := 12)
    (lo := (2989301 / 500000000)) (hi := (5978603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248509808391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248509808391) = 1/(248509808391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_469 : Bounds (-5978603 / 1000000000) (-2989301 / 500000000) (Real.log (248509808391 / 250000000000)) := by
  have h := reflection_log_469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_470_neg : (5946801 / 1000000000) ≤ -Real.log (994070845999 / 1000000000000) ∧
    -Real.log (994070845999 / 1000000000000) ≤ (2973401 / 500000000) := by
  have h := checkLog_sound (w := (5929154001 / 1994070845999)) (n := 12)
    (lo := (5946801 / 1000000000)) (hi := (2973401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994070845999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994070845999) = 1/(994070845999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_470 : Bounds (-2973401 / 500000000) (-5946801 / 1000000000) (Real.log (994070845999 / 1000000000000)) := by
  have h := reflection_log_470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_471_neg : (77153727 / 500000000) ≤ -Real.log (250000000000 / 291712396221) ∧
    -Real.log (250000000000 / 291712396221) ≤ (30861491 / 200000000) := by
  have h := checkLog_sound (w := (41712396221 / 541712396221)) (n := 12)
    (lo := (77153727 / 500000000)) (hi := (30861491 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291712396221 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291712396221 / 250000000000) = 1/(250000000000 / 291712396221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_471 : Bounds (77153727 / 500000000) (30861491 / 200000000) (Real.log (291712396221 / 250000000000)) := by
  have h := reflection_log_471_neg
  have he : Real.log (291712396221 / 250000000000) = -Real.log (250000000000 / 291712396221) := by
    rw [show ((291712396221 / 250000000000) : ℝ) = ((250000000000 / 291712396221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_472_neg : (77359953 / 500000000) ≤ -Real.log (250000000000 / 291832738401) ∧
    -Real.log (250000000000 / 291832738401) ≤ (154719907 / 1000000000) := by
  have h := checkLog_sound (w := (41832738401 / 541832738401)) (n := 12)
    (lo := (77359953 / 500000000)) (hi := (154719907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291832738401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291832738401 / 250000000000) = 1/(250000000000 / 291832738401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_472 : Bounds (77359953 / 500000000) (154719907 / 1000000000) (Real.log (291832738401 / 250000000000)) := by
  have h := reflection_log_472_neg
  have he : Real.log (291832738401 / 250000000000) = -Real.log (250000000000 / 291832738401) := by
    rw [show ((291832738401 / 250000000000) : ℝ) = ((250000000000 / 291832738401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_473_neg : (77361469 / 250000000) ≤ -Real.log (250000000000 / 340667454223) ∧
    -Real.log (250000000000 / 340667454223) ≤ (309445877 / 1000000000) := by
  have h := checkLog_sound (w := (90667454223 / 590667454223)) (n := 12)
    (lo := (77361469 / 250000000)) (hi := (309445877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340667454223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340667454223 / 250000000000) = 1/(250000000000 / 340667454223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_473 : Bounds (77361469 / 250000000) (309445877 / 1000000000) (Real.log (340667454223 / 250000000000)) := by
  have h := reflection_log_473_neg
  have he : Real.log (340667454223 / 250000000000) = -Real.log (250000000000 / 340667454223) := by
    rw [show ((340667454223 / 250000000000) : ℝ) = ((250000000000 / 340667454223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_474_neg : (61930141 / 200000000) ≤ -Real.log (62500000000 / 85184310019) ∧
    -Real.log (62500000000 / 85184310019) ≤ (154825353 / 500000000) := by
  have h := checkLog_sound (w := (22684310019 / 147684310019)) (n := 12)
    (lo := (61930141 / 200000000)) (hi := (154825353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85184310019 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85184310019 / 62500000000) = 1/(62500000000 / 85184310019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_474 : Bounds (61930141 / 200000000) (154825353 / 500000000) (Real.log (85184310019 / 62500000000)) := by
  have h := reflection_log_474_neg
  have he : Real.log (85184310019 / 62500000000) = -Real.log (62500000000 / 85184310019) := by
    rw [show ((85184310019 / 62500000000) : ℝ) = ((62500000000 / 85184310019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_475_neg : (17871771 / 125000000) ≤ -Real.log (10000 / 11537) ∧
    -Real.log (10000 / 11537) ≤ (142974169 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 21537)) (n := 12)
    (lo := (17871771 / 125000000)) (hi := (142974169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 10000) = 1/(10000 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_475 : Bounds (17871771 / 125000000) (142974169 / 1000000000) (Real.log (11537 / 10000)) := by
  have h := reflection_log_475_neg
  have he : Real.log (11537 / 10000) = -Real.log (10000 / 11537) := by
    rw [show ((11537 / 10000) : ℝ) = ((10000 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_476_neg : (41720343 / 250000000) ≤ -Real.log (8463 / 10000) ∧
    -Real.log (8463 / 10000) ≤ (166881373 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 18463)) (n := 12)
    (lo := (41720343 / 250000000)) (hi := (166881373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8463) = 1/(8463 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_476 : Bounds (-166881373 / 1000000000) (-41720343 / 250000000) (Real.log (8463 / 10000)) := by
  have h := reflection_log_476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_477_neg : (19211 / 125000000) ≤ -Real.log (10000000 / 10001537) ∧
    -Real.log (10000000 / 10001537) ≤ (153689 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 20001537)) (n := 12)
    (lo := (19211 / 125000000)) (hi := (153689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001537 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001537 / 10000000) = 1/(10000000 / 10001537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_477 : Bounds (19211 / 125000000) (153689 / 1000000000) (Real.log (10001537 / 10000000)) := by
  have h := reflection_log_477_neg
  have he : Real.log (10001537 / 10000000) = -Real.log (10000000 / 10001537) := by
    rw [show ((10001537 / 10000000) : ℝ) = ((10000000 / 10001537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_478_neg : (153711 / 1000000000) ≤ -Real.log (9998463 / 10000000) ∧
    -Real.log (9998463 / 10000000) ≤ (9607 / 62500000) := by
  have h := checkLog_sound (w := (1537 / 19998463)) (n := 12)
    (lo := (153711 / 1000000000)) (hi := (9607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998463) = 1/(9998463 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_478 : Bounds (-9607 / 62500000) (-153711 / 1000000000) (Real.log (9998463 / 10000000)) := by
  have h := reflection_log_478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_479_neg : (74227679 / 1000000000) ≤ -Real.log (250000 / 269263) ∧
    -Real.log (250000 / 269263) ≤ (463923 / 6250000) := by
  have h := checkLog_sound (w := (19263 / 519263)) (n := 12)
    (lo := (74227679 / 1000000000)) (hi := (463923 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269263 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269263 / 250000) = 1/(250000 / 269263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_479 : Bounds (74227679 / 1000000000) (463923 / 6250000) (Real.log (269263 / 250000)) := by
  have h := reflection_log_479_neg
  have he : Real.log (269263 / 250000) = -Real.log (250000 / 269263) := by
    rw [show ((269263 / 250000) : ℝ) = ((250000 / 269263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_480_neg : (5011399 / 62500000) ≤ -Real.log (230737 / 250000) ∧
    -Real.log (230737 / 250000) ≤ (16036477 / 200000000) := by
  have h := checkLog_sound (w := (19263 / 480737)) (n := 12)
    (lo := (5011399 / 62500000)) (hi := (16036477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230737) = 1/(230737 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_480 : Bounds (-16036477 / 200000000) (-5011399 / 62500000) (Real.log (230737 / 250000)) := by
  have h := reflection_log_480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_481_neg : (14883599 / 200000000) ≤ -Real.log (1000000 / 1077257) ∧
    -Real.log (1000000 / 1077257) ≤ (18604499 / 250000000) := by
  have h := checkLog_sound (w := (77257 / 2077257)) (n := 12)
    (lo := (14883599 / 200000000)) (hi := (18604499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077257 / 1000000) = 1/(1000000 / 1077257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_481 : Bounds (14883599 / 200000000) (18604499 / 250000000) (Real.log (1077257 / 1000000)) := by
  have h := reflection_log_481_neg
  have he : Real.log (1077257 / 1000000) = -Real.log (1000000 / 1077257) := by
    rw [show ((1077257 / 1000000) : ℝ) = ((1000000 / 1077257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_482_neg : (80404523 / 1000000000) ≤ -Real.log (922743 / 1000000) ∧
    -Real.log (922743 / 1000000) ≤ (20101131 / 250000000) := by
  have h := checkLog_sound (w := (77257 / 1922743)) (n := 12)
    (lo := (80404523 / 1000000000)) (hi := (20101131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922743) = 1/(922743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_482 : Bounds (-20101131 / 250000000) (-80404523 / 1000000000) (Real.log (922743 / 1000000)) := by
  have h := reflection_log_482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_483_neg : (5986527 / 1000000000) ≤ -Real.log (994031355951 / 1000000000000) ∧
    -Real.log (994031355951 / 1000000000000) ≤ (187079 / 31250000) := by
  have h := checkLog_sound (w := (5968644049 / 1994031355951)) (n := 12)
    (lo := (5986527 / 1000000000)) (hi := (187079 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994031355951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994031355951) = 1/(994031355951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_483 : Bounds (-187079 / 31250000) (-5986527 / 1000000000) (Real.log (994031355951 / 1000000000000)) := by
  have h := reflection_log_483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_484_neg : (372169 / 62500000) ≤ -Real.log (62128936831 / 62500000000) ∧
    -Real.log (62128936831 / 62500000000) ≤ (1190941 / 200000000) := by
  have h := checkLog_sound (w := (371063169 / 124628936831)) (n := 12)
    (lo := (372169 / 62500000)) (hi := (1190941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62128936831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62128936831) = 1/(62128936831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_484 : Bounds (-1190941 / 200000000) (-372169 / 62500000) (Real.log (62128936831 / 62500000000)) := by
  have h := reflection_log_484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_485_neg : (154410063 / 1000000000) ≤ -Real.log (62500000000 / 72935582503) ∧
    -Real.log (62500000000 / 72935582503) ≤ (9650629 / 62500000) := by
  have h := checkLog_sound (w := (10435582503 / 135435582503)) (n := 12)
    (lo := (154410063 / 1000000000)) (hi := (9650629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72935582503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72935582503 / 62500000000) = 1/(62500000000 / 72935582503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_485 : Bounds (154410063 / 1000000000) (9650629 / 62500000) (Real.log (72935582503 / 62500000000)) := by
  have h := reflection_log_485_neg
  have he : Real.log (72935582503 / 62500000000) = -Real.log (62500000000 / 72935582503) := by
    rw [show ((72935582503 / 62500000000) : ℝ) = ((62500000000 / 72935582503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_486_neg : (77411259 / 500000000) ≤ -Real.log (500000000000 / 583725370987) ∧
    -Real.log (500000000000 / 583725370987) ≤ (154822519 / 1000000000) := by
  have h := checkLog_sound (w := (83725370987 / 1083725370987)) (n := 12)
    (lo := (77411259 / 500000000)) (hi := (154822519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583725370987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583725370987 / 500000000000) = 1/(500000000000 / 583725370987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_486 : Bounds (77411259 / 500000000) (154822519 / 1000000000) (Real.log (583725370987 / 500000000000)) := by
  have h := reflection_log_486_neg
  have he : Real.log (583725370987 / 500000000000) = -Real.log (500000000000 / 583725370987) := by
    rw [show ((583725370987 / 500000000000) : ℝ) = ((500000000000 / 583725370987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_487_neg : (61930141 / 200000000) ≤ -Real.log (500000000000 / 681474480151) ∧
    -Real.log (500000000000 / 681474480151) ≤ (154825353 / 500000000) := by
  have h := checkLog_sound (w := (181474480151 / 1181474480151)) (n := 12)
    (lo := (61930141 / 200000000)) (hi := (154825353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681474480151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681474480151 / 500000000000) = 1/(500000000000 / 681474480151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_487 : Bounds (61930141 / 200000000) (154825353 / 500000000) (Real.log (681474480151 / 500000000000)) := by
  have h := reflection_log_487_neg
  have he : Real.log (681474480151 / 500000000000) = -Real.log (500000000000 / 681474480151) := by
    rw [show ((681474480151 / 500000000000) : ℝ) = ((500000000000 / 681474480151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_488_neg : (309855541 / 1000000000) ≤ -Real.log (12500000000 / 17040352121) ∧
    -Real.log (12500000000 / 17040352121) ≤ (154927771 / 500000000) := by
  have h := checkLog_sound (w := (4540352121 / 29540352121)) (n := 12)
    (lo := (309855541 / 1000000000)) (hi := (154927771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17040352121 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17040352121 / 12500000000) = 1/(12500000000 / 17040352121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_488 : Bounds (309855541 / 1000000000) (154927771 / 500000000) (Real.log (17040352121 / 12500000000)) := by
  have h := reflection_log_488_neg
  have he : Real.log (17040352121 / 12500000000) = -Real.log (12500000000 / 17040352121) := by
    rw [show ((17040352121 / 12500000000) : ℝ) = ((12500000000 / 17040352121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_489_neg : (71530421 / 500000000) ≤ -Real.log (5000 / 5769) ∧
    -Real.log (5000 / 5769) ≤ (143060843 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 10769)) (n := 12)
    (lo := (71530421 / 500000000)) (hi := (143060843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5769 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5769 / 5000) = 1/(5000 / 5769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_489 : Bounds (71530421 / 500000000) (143060843 / 1000000000) (Real.log (5769 / 5000)) := by
  have h := reflection_log_489_neg
  have he : Real.log (5769 / 5000) = -Real.log (5000 / 5769) := by
    rw [show ((5769 / 5000) : ℝ) = ((5000 / 5769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_490_neg : (8349977 / 50000000) ≤ -Real.log (4231 / 5000) ∧
    -Real.log (4231 / 5000) ≤ (166999541 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 9231)) (n := 12)
    (lo := (8349977 / 50000000)) (hi := (166999541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4231) = 1/(4231 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_490 : Bounds (-166999541 / 1000000000) (-8349977 / 50000000) (Real.log (4231 / 5000)) := by
  have h := reflection_log_490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_491_neg : (38447 / 250000000) ≤ -Real.log (5000000 / 5000769) ∧
    -Real.log (5000000 / 5000769) ≤ (153789 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 10000769)) (n := 12)
    (lo := (38447 / 250000000)) (hi := (153789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000769 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000769 / 5000000) = 1/(5000000 / 5000769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_491 : Bounds (38447 / 250000000) (153789 / 1000000000) (Real.log (5000769 / 5000000)) := by
  have h := reflection_log_491_neg
  have he : Real.log (5000769 / 5000000) = -Real.log (5000000 / 5000769) := by
    rw [show ((5000769 / 5000000) : ℝ) = ((5000000 / 5000769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_492_neg : (153811 / 1000000000) ≤ -Real.log (4999231 / 5000000) ∧
    -Real.log (4999231 / 5000000) ≤ (38453 / 250000000) := by
  have h := checkLog_sound (w := (769 / 9999231)) (n := 12)
    (lo := (153811 / 1000000000)) (hi := (38453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999231) = 1/(4999231 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_492 : Bounds (-38453 / 250000000) (-153811 / 1000000000) (Real.log (4999231 / 5000000)) := by
  have h := reflection_log_492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_493_neg : (74275029 / 1000000000) ≤ -Real.log (1000000 / 1077103) ∧
    -Real.log (1000000 / 1077103) ≤ (7427503 / 100000000) := by
  have h := checkLog_sound (w := (77103 / 2077103)) (n := 12)
    (lo := (74275029 / 1000000000)) (hi := (7427503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077103 / 1000000) = 1/(1000000 / 1077103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_493 : Bounds (74275029 / 1000000000) (7427503 / 100000000) (Real.log (1077103 / 1000000)) := by
  have h := reflection_log_493_neg
  have he : Real.log (1077103 / 1000000) = -Real.log (1000000 / 1077103) := by
    rw [show ((1077103 / 1000000) : ℝ) = ((1000000 / 1077103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_494_neg : (80237643 / 1000000000) ≤ -Real.log (922897 / 1000000) ∧
    -Real.log (922897 / 1000000) ≤ (20059411 / 250000000) := by
  have h := checkLog_sound (w := (77103 / 1922897)) (n := 12)
    (lo := (80237643 / 1000000000)) (hi := (20059411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922897) = 1/(922897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_494 : Bounds (-20059411 / 250000000) (-80237643 / 1000000000) (Real.log (922897 / 1000000)) := by
  have h := reflection_log_494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_495_neg : (9308051 / 125000000) ≤ -Real.log (1000000 / 1077307) ∧
    -Real.log (1000000 / 1077307) ≤ (74464409 / 1000000000) := by
  have h := checkLog_sound (w := (77307 / 2077307)) (n := 12)
    (lo := (9308051 / 125000000)) (hi := (74464409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077307 / 1000000) = 1/(1000000 / 1077307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_495 : Bounds (9308051 / 125000000) (74464409 / 1000000000) (Real.log (1077307 / 1000000)) := by
  have h := reflection_log_495_neg
  have he : Real.log (1077307 / 1000000) = -Real.log (1000000 / 1077307) := by
    rw [show ((1077307 / 1000000) : ℝ) = ((1000000 / 1077307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_496_neg : (8045871 / 100000000) ≤ -Real.log (922693 / 1000000) ∧
    -Real.log (922693 / 1000000) ≤ (80458711 / 1000000000) := by
  have h := checkLog_sound (w := (77307 / 1922693)) (n := 12)
    (lo := (8045871 / 100000000)) (hi := (80458711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922693) = 1/(922693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_496 : Bounds (-80458711 / 1000000000) (-8045871 / 100000000) (Real.log (922693 / 1000000)) := by
  have h := reflection_log_496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_497_neg : (2997151 / 500000000) ≤ -Real.log (994023627751 / 1000000000000) ∧
    -Real.log (994023627751 / 1000000000000) ≤ (5994303 / 1000000000) := by
  have h := checkLog_sound (w := (5976372249 / 1994023627751)) (n := 12)
    (lo := (2997151 / 500000000)) (hi := (5994303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994023627751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994023627751) = 1/(994023627751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_497 : Bounds (-5994303 / 1000000000) (-2997151 / 500000000) (Real.log (994023627751 / 1000000000000)) := by
  have h := reflection_log_497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_498_neg : (5962613 / 1000000000) ≤ -Real.log (994055127391 / 1000000000000) ∧
    -Real.log (994055127391 / 1000000000000) ≤ (2981307 / 500000000) := by
  have h := checkLog_sound (w := (5944872609 / 1994055127391)) (n := 12)
    (lo := (5962613 / 1000000000)) (hi := (2981307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994055127391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994055127391) = 1/(994055127391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_498 : Bounds (-2981307 / 500000000) (-5962613 / 1000000000) (Real.log (994055127391 / 1000000000000)) := by
  have h := reflection_log_498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_499_neg : (4828521 / 31250000) ≤ -Real.log (250000000000 / 291772267111) ∧
    -Real.log (250000000000 / 291772267111) ≤ (154512673 / 1000000000) := by
  have h := checkLog_sound (w := (41772267111 / 541772267111)) (n := 12)
    (lo := (4828521 / 31250000)) (hi := (154512673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291772267111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291772267111 / 250000000000) = 1/(250000000000 / 291772267111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_499 : Bounds (4828521 / 31250000) (154512673 / 1000000000) (Real.log (291772267111 / 250000000000)) := by
  have h := reflection_log_499_neg
  have he : Real.log (291772267111 / 250000000000) = -Real.log (250000000000 / 291772267111) := by
    rw [show ((291772267111 / 250000000000) : ℝ) = ((250000000000 / 291772267111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_500_neg : (154923119 / 1000000000) ≤ -Real.log (500000000000 / 583784097203) ∧
    -Real.log (500000000000 / 583784097203) ≤ (1936539 / 12500000) := by
  have h := checkLog_sound (w := (83784097203 / 1083784097203)) (n := 12)
    (lo := (154923119 / 1000000000)) (hi := (1936539 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583784097203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583784097203 / 500000000000) = 1/(500000000000 / 583784097203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_500 : Bounds (154923119 / 1000000000) (1936539 / 12500000) (Real.log (583784097203 / 500000000000)) := by
  have h := reflection_log_500_neg
  have he : Real.log (583784097203 / 500000000000) = -Real.log (500000000000 / 583784097203) := by
    rw [show ((583784097203 / 500000000000) : ℝ) = ((500000000000 / 583784097203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_501_neg : (309855541 / 1000000000) ≤ -Real.log (500000000000 / 681614084839) ∧
    -Real.log (500000000000 / 681614084839) ≤ (154927771 / 500000000) := by
  have h := checkLog_sound (w := (181614084839 / 1181614084839)) (n := 12)
    (lo := (309855541 / 1000000000)) (hi := (154927771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681614084839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681614084839 / 500000000000) = 1/(500000000000 / 681614084839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_501 : Bounds (309855541 / 1000000000) (154927771 / 500000000) (Real.log (681614084839 / 500000000000)) := by
  have h := reflection_log_501_neg
  have he : Real.log (681614084839 / 500000000000) = -Real.log (500000000000 / 681614084839) := by
    rw [show ((681614084839 / 500000000000) : ℝ) = ((500000000000 / 681614084839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_502_neg : (310060383 / 1000000000) ≤ -Real.log (20000000000 / 27270148901) ∧
    -Real.log (20000000000 / 27270148901) ≤ (9689387 / 31250000) := by
  have h := checkLog_sound (w := (7270148901 / 47270148901)) (n := 12)
    (lo := (310060383 / 1000000000)) (hi := (9689387 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27270148901 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27270148901 / 20000000000) = 1/(20000000000 / 27270148901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_502 : Bounds (310060383 / 1000000000) (9689387 / 31250000) (Real.log (27270148901 / 20000000000)) := by
  have h := reflection_log_502_neg
  have he : Real.log (27270148901 / 20000000000) = -Real.log (20000000000 / 27270148901) := by
    rw [show ((27270148901 / 20000000000) : ℝ) = ((20000000000 / 27270148901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_503_neg : (143147509 / 1000000000) ≤ -Real.log (10000 / 11539) ∧
    -Real.log (10000 / 11539) ≤ (14314751 / 100000000) := by
  have h := checkLog_sound (w := (1539 / 21539)) (n := 12)
    (lo := (143147509 / 1000000000)) (hi := (14314751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11539 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11539 / 10000) = 1/(10000 / 11539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_503 : Bounds (143147509 / 1000000000) (14314751 / 100000000) (Real.log (11539 / 10000)) := by
  have h := reflection_log_503_neg
  have he : Real.log (11539 / 10000) = -Real.log (10000 / 11539) := by
    rw [show ((11539 / 10000) : ℝ) = ((10000 / 11539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_504_neg : (167117723 / 1000000000) ≤ -Real.log (8461 / 10000) ∧
    -Real.log (8461 / 10000) ≤ (41779431 / 250000000) := by
  have h := checkLog_sound (w := (1539 / 18461)) (n := 12)
    (lo := (167117723 / 1000000000)) (hi := (41779431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8461) = 1/(8461 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_504 : Bounds (-41779431 / 250000000) (-167117723 / 1000000000) (Real.log (8461 / 10000)) := by
  have h := reflection_log_504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_505_neg : (4809 / 31250000) ≤ -Real.log (10000000 / 10001539) ∧
    -Real.log (10000000 / 10001539) ≤ (153889 / 1000000000) := by
  have h := checkLog_sound (w := (1539 / 20001539)) (n := 12)
    (lo := (4809 / 31250000)) (hi := (153889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001539 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001539 / 10000000) = 1/(10000000 / 10001539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_505 : Bounds (4809 / 31250000) (153889 / 1000000000) (Real.log (10001539 / 10000000)) := by
  have h := reflection_log_505_neg
  have he : Real.log (10001539 / 10000000) = -Real.log (10000000 / 10001539) := by
    rw [show ((10001539 / 10000000) : ℝ) = ((10000000 / 10001539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_506_neg : (153911 / 1000000000) ≤ -Real.log (9998461 / 10000000) ∧
    -Real.log (9998461 / 10000000) ≤ (19239 / 125000000) := by
  have h := checkLog_sound (w := (1539 / 19998461)) (n := 12)
    (lo := (153911 / 1000000000)) (hi := (19239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998461) = 1/(9998461 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_506 : Bounds (-19239 / 125000000) (-153911 / 1000000000) (Real.log (9998461 / 10000000)) := by
  have h := reflection_log_506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_507_neg : (74321449 / 1000000000) ≤ -Real.log (1000000 / 1077153) ∧
    -Real.log (1000000 / 1077153) ≤ (1486429 / 20000000) := by
  have h := checkLog_sound (w := (77153 / 2077153)) (n := 12)
    (lo := (74321449 / 1000000000)) (hi := (1486429 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077153 / 1000000) = 1/(1000000 / 1077153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_507 : Bounds (74321449 / 1000000000) (1486429 / 20000000) (Real.log (1077153 / 1000000)) := by
  have h := reflection_log_507_neg
  have he : Real.log (1077153 / 1000000) = -Real.log (1000000 / 1077153) := by
    rw [show ((1077153 / 1000000) : ℝ) = ((1000000 / 1077153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_508_neg : (40145911 / 500000000) ≤ -Real.log (922847 / 1000000) ∧
    -Real.log (922847 / 1000000) ≤ (80291823 / 1000000000) := by
  have h := checkLog_sound (w := (77153 / 1922847)) (n := 12)
    (lo := (40145911 / 500000000)) (hi := (80291823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922847) = 1/(922847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_508 : Bounds (-80291823 / 1000000000) (-40145911 / 500000000) (Real.log (922847 / 1000000)) := by
  have h := reflection_log_508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_509_neg : (74511747 / 1000000000) ≤ -Real.log (500000 / 538679) ∧
    -Real.log (500000 / 538679) ≤ (18627937 / 250000000) := by
  have h := checkLog_sound (w := (38679 / 1038679)) (n := 12)
    (lo := (74511747 / 1000000000)) (hi := (18627937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538679 / 500000) = 1/(500000 / 538679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_509 : Bounds (74511747 / 1000000000) (18627937 / 250000000) (Real.log (538679 / 500000)) := by
  have h := reflection_log_509_neg
  have he : Real.log (538679 / 500000) = -Real.log (500000 / 538679) := by
    rw [show ((538679 / 500000) : ℝ) = ((500000 / 538679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_510_neg : (16102797 / 200000000) ≤ -Real.log (461321 / 500000) ∧
    -Real.log (461321 / 500000) ≤ (40256993 / 500000000) := by
  have h := checkLog_sound (w := (38679 / 961321)) (n := 12)
    (lo := (16102797 / 200000000)) (hi := (40256993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461321) = 1/(461321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_510 : Bounds (-40256993 / 500000000) (-16102797 / 200000000) (Real.log (461321 / 500000)) := by
  have h := reflection_log_510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_511_neg : (6002237 / 1000000000) ≤ -Real.log (248503934959 / 250000000000) ∧
    -Real.log (248503934959 / 250000000000) ≤ (3001119 / 500000000) := by
  have h := checkLog_sound (w := (1496065041 / 498503934959)) (n := 12)
    (lo := (6002237 / 1000000000)) (hi := (3001119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248503934959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248503934959) = 1/(248503934959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_511 : Bounds (-3001119 / 500000000) (-6002237 / 1000000000) (Real.log (248503934959 / 250000000000)) := by
  have h := reflection_log_511_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
