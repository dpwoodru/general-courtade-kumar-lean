import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0415
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

theorem reflection_log_1_neg : (196623097 / 1000000000) ≤ -Real.log (2048 / 2493) ∧
    -Real.log (2048 / 2493) ≤ (98311549 / 500000000) := by
  have h := checkLog_sound (w := (445 / 4541)) (n := 12)
    (lo := (196623097 / 1000000000)) (hi := (98311549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2048) = 1/(2048 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (196623097 / 1000000000) (98311549 / 500000000) (Real.log (2493 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2493 / 2048) = -Real.log (2048 / 2493) := by
    rw [show ((2493 / 2048) : ℝ) = ((2048 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244986833 / 1000000000) ≤ -Real.log (1603 / 2048) ∧
    -Real.log (1603 / 2048) ≤ (122493417 / 500000000) := by
  have h := checkLog_sound (w := (445 / 3651)) (n := 12)
    (lo := (244986833 / 1000000000)) (hi := (122493417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1603) = 1/(1603 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122493417 / 500000000) (-244986833 / 1000000000) (Real.log (1603 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98191197 / 500000000) ≤ -Real.log (5120 / 6231) ∧
    -Real.log (5120 / 6231) ≤ (39276479 / 200000000) := by
  have h := checkLog_sound (w := (1111 / 11351)) (n := 12)
    (lo := (98191197 / 500000000)) (hi := (39276479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6231 / 5120) = 1/(5120 / 6231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98191197 / 500000000) (39276479 / 200000000) (Real.log (6231 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6231 / 5120) = -Real.log (5120 / 6231) := by
    rw [show ((6231 / 5120) : ℝ) = ((5120 / 6231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (48922521 / 200000000) ≤ -Real.log (4009 / 5120) ∧
    -Real.log (4009 / 5120) ≤ (122306303 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 9129)) (n := 12)
    (lo := (48922521 / 200000000)) (hi := (122306303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4009) = 1/(4009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122306303 / 500000000) (-48922521 / 200000000) (Real.log (4009 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36086537 / 100000000) ≤ -Real.log (1024 / 1469) ∧
    -Real.log (1024 / 1469) ≤ (360865371 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 2493)) (n := 12)
    (lo := (36086537 / 100000000)) (hi := (360865371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1024) = 1/(1024 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36086537 / 100000000) (360865371 / 1000000000) (Real.log (1469 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1469 / 1024) = -Real.log (1024 / 1469) := by
    rw [show ((1469 / 1024) : ℝ) = ((1024 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35635583 / 62500000) ≤ -Real.log (579 / 1024) ∧
    -Real.log (579 / 1024) ≤ (570169329 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 1603)) (n := 12)
    (lo := (35635583 / 62500000)) (hi := (570169329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 579) = 1/(579 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-570169329 / 1000000000) (-35635583 / 62500000) (Real.log (579 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180228423 / 500000000) ≤ -Real.log (2560 / 3671) ∧
    -Real.log (2560 / 3671) ≤ (360456847 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 6231)) (n := 12)
    (lo := (180228423 / 500000000)) (hi := (360456847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3671 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3671 / 2560) = 1/(2560 / 3671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (180228423 / 500000000) (360456847 / 1000000000) (Real.log (3671 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3671 / 2560) = -Real.log (2560 / 3671) := by
    rw [show ((3671 / 2560) : ℝ) = ((2560 / 3671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (113826719 / 200000000) ≤ -Real.log (1449 / 2560) ∧
    -Real.log (1449 / 2560) ≤ (142283399 / 250000000) := by
  have h := checkLog_sound (w := (1111 / 4009)) (n := 12)
    (lo := (113826719 / 200000000)) (hi := (142283399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1449) = 1/(1449 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142283399 / 250000000) (-113826719 / 200000000) (Real.log (1449 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67409437 / 250000000) ≤ -Real.log (100000 / 130949) ∧
    -Real.log (100000 / 130949) ≤ (269637749 / 1000000000) := by
  have h := checkLog_sound (w := (30949 / 230949)) (n := 12)
    (lo := (67409437 / 250000000)) (hi := (269637749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130949 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130949 / 100000) = 1/(100000 / 130949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67409437 / 250000000) (269637749 / 1000000000) (Real.log (130949 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (130949 / 100000) = -Real.log (100000 / 130949) := by
    rw [show ((130949 / 100000) : ℝ) = ((100000 / 130949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (370324823 / 1000000000) ≤ -Real.log (69051 / 100000) ∧
    -Real.log (69051 / 100000) ≤ (46290603 / 125000000) := by
  have h := checkLog_sound (w := (30949 / 169051)) (n := 12)
    (lo := (370324823 / 1000000000)) (hi := (46290603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69051) = 1/(69051 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46290603 / 125000000) (-370324823 / 1000000000) (Real.log (69051 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (527273 / 1953125) ≤ -Real.log (1000000 / 1309917) ∧
    -Real.log (1000000 / 1309917) ≤ (269963777 / 1000000000) := by
  have h := checkLog_sound (w := (309917 / 2309917)) (n := 12)
    (lo := (527273 / 1953125)) (hi := (269963777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309917 / 1000000) = 1/(1000000 / 1309917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (527273 / 1953125) (269963777 / 1000000000) (Real.log (1309917 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1309917 / 1000000) = -Real.log (1000000 / 1309917) := by
    rw [show ((1309917 / 1000000) : ℝ) = ((1000000 / 1309917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (185471699 / 500000000) ≤ -Real.log (690083 / 1000000) ∧
    -Real.log (690083 / 1000000) ≤ (370943399 / 1000000000) := by
  have h := checkLog_sound (w := (309917 / 1690083)) (n := 12)
    (lo := (185471699 / 500000000)) (hi := (370943399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690083) = 1/(690083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-370943399 / 1000000000) (-185471699 / 500000000) (Real.log (690083 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202780831 / 1000000000) ≤ -Real.log (250000 / 306201) ∧
    -Real.log (250000 / 306201) ≤ (6336901 / 31250000) := by
  have h := checkLog_sound (w := (56201 / 556201)) (n := 12)
    (lo := (202780831 / 1000000000)) (hi := (6336901 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306201 / 250000) = 1/(250000 / 306201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202780831 / 1000000000) (6336901 / 31250000) (Real.log (306201 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (306201 / 250000) = -Real.log (250000 / 306201) := by
    rw [show ((306201 / 250000) : ℝ) = ((250000 / 306201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (127319689 / 500000000) ≤ -Real.log (193799 / 250000) ∧
    -Real.log (193799 / 250000) ≤ (254639379 / 1000000000) := by
  have h := checkLog_sound (w := (56201 / 443799)) (n := 12)
    (lo := (127319689 / 500000000)) (hi := (254639379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193799) = 1/(193799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-254639379 / 1000000000) (-127319689 / 500000000) (Real.log (193799 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203047777 / 1000000000) ≤ -Real.log (1000000 / 1225131) ∧
    -Real.log (1000000 / 1225131) ≤ (101523889 / 500000000) := by
  have h := checkLog_sound (w := (225131 / 2225131)) (n := 12)
    (lo := (203047777 / 1000000000)) (hi := (101523889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225131 / 1000000) = 1/(1000000 / 1225131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203047777 / 1000000000) (101523889 / 500000000) (Real.log (1225131 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225131 / 1000000) = -Real.log (1000000 / 1225131) := by
    rw [show ((1225131 / 1000000) : ℝ) = ((1000000 / 1225131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15941331 / 62500000) ≤ -Real.log (774869 / 1000000) ∧
    -Real.log (774869 / 1000000) ≤ (255061297 / 1000000000) := by
  have h := checkLog_sound (w := (225131 / 1774869)) (n := 12)
    (lo := (15941331 / 62500000)) (hi := (255061297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774869) = 1/(774869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255061297 / 1000000000) (-15941331 / 62500000) (Real.log (774869 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159990643 / 250000000) ≤ -Real.log (125000000000 / 237051237491) ∧
    -Real.log (125000000000 / 237051237491) ≤ (639962573 / 1000000000) := by
  have h := checkLog_sound (w := (112051237491 / 362051237491)) (n := 12)
    (lo := (159990643 / 250000000)) (hi := (639962573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237051237491 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237051237491 / 125000000000) = 1/(125000000000 / 237051237491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159990643 / 250000000) (639962573 / 1000000000) (Real.log (237051237491 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (237051237491 / 125000000000) = -Real.log (125000000000 / 237051237491) := by
    rw [show ((237051237491 / 125000000000) : ℝ) = ((125000000000 / 237051237491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (25636287 / 40000000) ≤ -Real.log (125000000000 / 237275262541) ∧
    -Real.log (125000000000 / 237275262541) ≤ (80113397 / 125000000) := by
  have h := checkLog_sound (w := (112275262541 / 362275262541)) (n := 12)
    (lo := (25636287 / 40000000)) (hi := (80113397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237275262541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237275262541 / 125000000000) = 1/(125000000000 / 237275262541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (25636287 / 40000000) (80113397 / 125000000) (Real.log (237275262541 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (237275262541 / 125000000000) = -Real.log (125000000000 / 237275262541) := by
    rw [show ((237275262541 / 125000000000) : ℝ) = ((125000000000 / 237275262541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (457420209 / 1000000000) ≤ -Real.log (50000000000 / 78999633641) ∧
    -Real.log (50000000000 / 78999633641) ≤ (45742021 / 100000000) := by
  have h := checkLog_sound (w := (28999633641 / 128999633641)) (n := 12)
    (lo := (457420209 / 1000000000)) (hi := (45742021 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78999633641 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78999633641 / 50000000000) = 1/(50000000000 / 78999633641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (457420209 / 1000000000) (45742021 / 100000000) (Real.log (78999633641 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (78999633641 / 50000000000) = -Real.log (50000000000 / 78999633641) := by
    rw [show ((78999633641 / 50000000000) : ℝ) = ((50000000000 / 78999633641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (458109073 / 1000000000) ≤ -Real.log (250000000000 / 395270361829) ∧
    -Real.log (250000000000 / 395270361829) ≤ (229054537 / 500000000) := by
  have h := checkLog_sound (w := (145270361829 / 645270361829)) (n := 12)
    (lo := (458109073 / 1000000000)) (hi := (229054537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395270361829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395270361829 / 250000000000) = 1/(250000000000 / 395270361829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (458109073 / 1000000000) (229054537 / 500000000) (Real.log (395270361829 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (395270361829 / 250000000000) = -Real.log (250000000000 / 395270361829) := by
    rw [show ((395270361829 / 250000000000) : ℝ) = ((250000000000 / 395270361829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0415
