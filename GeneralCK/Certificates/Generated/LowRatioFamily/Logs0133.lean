import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8512_neg : (63883 / 250000000) ≤ -Real.log (1999489 / 2000000) ∧
    -Real.log (1999489 / 2000000) ≤ (255533 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3999489)) (n := 12)
    (lo := (63883 / 250000000)) (hi := (255533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999489) = 1/(1999489 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8512 : Bounds (-255533 / 1000000000) (-63883 / 250000000) (Real.log (1999489 / 2000000)) := by
  have h := reflection_log_8512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8513_neg : (24248387 / 200000000) ≤ -Real.log (500000 / 564449) ∧
    -Real.log (500000 / 564449) ≤ (7577621 / 62500000) := by
  have h := checkLog_sound (w := (64449 / 1064449)) (n := 12)
    (lo := (24248387 / 200000000)) (hi := (7577621 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564449 / 500000) = 1/(500000 / 564449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8513 : Bounds (24248387 / 200000000) (7577621 / 62500000) (Real.log (564449 / 500000)) := by
  have h := reflection_log_8513_neg
  have he : Real.log (564449 / 500000) = -Real.log (500000 / 564449) := by
    rw [show ((564449 / 500000) : ℝ) = ((500000 / 564449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8514_neg : (68998101 / 500000000) ≤ -Real.log (435551 / 500000) ∧
    -Real.log (435551 / 500000) ≤ (137996203 / 1000000000) := by
  have h := checkLog_sound (w := (64449 / 935551)) (n := 12)
    (lo := (68998101 / 500000000)) (hi := (137996203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435551) = 1/(435551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8514 : Bounds (-137996203 / 1000000000) (-68998101 / 500000000) (Real.log (435551 / 500000)) := by
  have h := reflection_log_8514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8515_neg : (30423843 / 250000000) ≤ -Real.log (100000 / 112941) ∧
    -Real.log (100000 / 112941) ≤ (121695373 / 1000000000) := by
  have h := checkLog_sound (w := (12941 / 212941)) (n := 12)
    (lo := (30423843 / 250000000)) (hi := (121695373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112941 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112941 / 100000) = 1/(100000 / 112941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8515 : Bounds (30423843 / 250000000) (121695373 / 1000000000) (Real.log (112941 / 100000)) := by
  have h := reflection_log_8515_neg
  have he : Real.log (112941 / 100000) = -Real.log (100000 / 112941) := by
    rw [show ((112941 / 100000) : ℝ) = ((100000 / 112941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8516_neg : (17323017 / 125000000) ≤ -Real.log (87059 / 100000) ∧
    -Real.log (87059 / 100000) ≤ (138584137 / 1000000000) := by
  have h := checkLog_sound (w := (12941 / 187059)) (n := 12)
    (lo := (17323017 / 125000000)) (hi := (138584137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87059) = 1/(87059 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8516 : Bounds (-138584137 / 1000000000) (-17323017 / 125000000) (Real.log (87059 / 100000)) := by
  have h := reflection_log_8516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8517_neg : (16888763 / 1000000000) ≤ -Real.log (9832530519 / 10000000000) ∧
    -Real.log (9832530519 / 10000000000) ≤ (4222191 / 250000000) := by
  have h := checkLog_sound (w := (167469481 / 19832530519)) (n := 12)
    (lo := (16888763 / 1000000000)) (hi := (4222191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9832530519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9832530519) = 1/(9832530519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8517 : Bounds (-4222191 / 250000000) (-16888763 / 1000000000) (Real.log (9832530519 / 10000000000)) := by
  have h := reflection_log_8517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8518_neg : (8377133 / 500000000) ≤ -Real.log (245846326399 / 250000000000) ∧
    -Real.log (245846326399 / 250000000000) ≤ (16754267 / 1000000000) := by
  have h := checkLog_sound (w := (4153673601 / 495846326399)) (n := 12)
    (lo := (8377133 / 500000000)) (hi := (16754267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245846326399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245846326399) = 1/(245846326399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8518 : Bounds (-16754267 / 1000000000) (-8377133 / 500000000) (Real.log (245846326399 / 250000000000)) := by
  have h := reflection_log_8518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8519_neg : (259238137 / 1000000000) ≤ -Real.log (100000000000 / 129594238103) ∧
    -Real.log (100000000000 / 129594238103) ≤ (129619069 / 500000000) := by
  have h := checkLog_sound (w := (29594238103 / 229594238103)) (n := 12)
    (lo := (259238137 / 1000000000)) (hi := (129619069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129594238103 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129594238103 / 100000000000) = 1/(100000000000 / 129594238103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8519 : Bounds (259238137 / 1000000000) (129619069 / 500000000) (Real.log (129594238103 / 100000000000)) := by
  have h := reflection_log_8519_neg
  have he : Real.log (129594238103 / 100000000000) = -Real.log (100000000000 / 129594238103) := by
    rw [show ((129594238103 / 100000000000) : ℝ) = ((100000000000 / 129594238103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8520_neg : (65069877 / 250000000) ≤ -Real.log (62500000000 / 81080790039) ∧
    -Real.log (62500000000 / 81080790039) ≤ (260279509 / 1000000000) := by
  have h := checkLog_sound (w := (18580790039 / 143580790039)) (n := 12)
    (lo := (65069877 / 250000000)) (hi := (260279509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81080790039 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81080790039 / 62500000000) = 1/(62500000000 / 81080790039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8520 : Bounds (65069877 / 250000000) (260279509 / 1000000000) (Real.log (81080790039 / 62500000000)) := by
  have h := reflection_log_8520_neg
  have he : Real.log (81080790039 / 62500000000) = -Real.log (62500000000 / 81080790039) := by
    rw [show ((81080790039 / 62500000000) : ℝ) = ((62500000000 / 81080790039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8521_neg : (521506633 / 1000000000) ≤ -Real.log (250000000000 / 421140939597) ∧
    -Real.log (250000000000 / 421140939597) ≤ (260753317 / 500000000) := by
  have h := checkLog_sound (w := (171140939597 / 671140939597)) (n := 12)
    (lo := (521506633 / 1000000000)) (hi := (260753317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421140939597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421140939597 / 250000000000) = 1/(250000000000 / 421140939597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8521 : Bounds (521506633 / 1000000000) (260753317 / 500000000) (Real.log (421140939597 / 250000000000)) := by
  have h := reflection_log_8521_neg
  have he : Real.log (421140939597 / 250000000000) = -Real.log (250000000000 / 421140939597) := by
    rw [show ((421140939597 / 250000000000) : ℝ) = ((250000000000 / 421140939597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8522_neg : (261288163 / 500000000) ≤ -Real.log (500000000000 / 843183344527) ∧
    -Real.log (500000000000 / 843183344527) ≤ (522576327 / 1000000000) := by
  have h := checkLog_sound (w := (343183344527 / 1343183344527)) (n := 12)
    (lo := (261288163 / 500000000)) (hi := (522576327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843183344527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843183344527 / 500000000000) = 1/(500000000000 / 843183344527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8522 : Bounds (261288163 / 500000000) (522576327 / 1000000000) (Real.log (843183344527 / 500000000000)) := by
  have h := reflection_log_8522_neg
  have he : Real.log (843183344527 / 500000000000) = -Real.log (500000000000 / 843183344527) := by
    rw [show ((843183344527 / 500000000000) : ℝ) = ((500000000000 / 843183344527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8523_neg : (56983017 / 250000000) ≤ -Real.log (125 / 157) ∧
    -Real.log (125 / 157) ≤ (227932069 / 1000000000) := by
  have h := checkLog_sound (w := (16 / 141)) (n := 12)
    (lo := (56983017 / 250000000)) (hi := (227932069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 125) = 1/(125 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8523 : Bounds (56983017 / 250000000) (227932069 / 1000000000) (Real.log (157 / 125)) := by
  have h := reflection_log_8523_neg
  have he : Real.log (157 / 125) = -Real.log (125 / 157) := by
    rw [show ((157 / 125) : ℝ) = ((125 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8524_neg : (73928561 / 250000000) ≤ -Real.log (93 / 125) ∧
    -Real.log (93 / 125) ≤ (59142849 / 200000000) := by
  have h := checkLog_sound (w := (16 / 109)) (n := 12)
    (lo := (73928561 / 250000000)) (hi := (59142849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 93) = 1/(93 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8524 : Bounds (-59142849 / 200000000) (-73928561 / 250000000) (Real.log (93 / 125)) := by
  have h := reflection_log_8524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8525_neg : (255967 / 1000000000) ≤ -Real.log (15625 / 15629) ∧
    -Real.log (15625 / 15629) ≤ (7999 / 31250000) := by
  have h := checkLog_sound (w := (2 / 15627)) (n := 12)
    (lo := (255967 / 1000000000)) (hi := (7999 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15629 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15629 / 15625) = 1/(15625 / 15629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8525 : Bounds (255967 / 1000000000) (7999 / 31250000) (Real.log (15629 / 15625)) := by
  have h := reflection_log_8525_neg
  have he : Real.log (15629 / 15625) = -Real.log (15625 / 15629) := by
    rw [show ((15629 / 15625) : ℝ) = ((15625 / 15629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8526_neg : (8001 / 31250000) ≤ -Real.log (15621 / 15625) ∧
    -Real.log (15621 / 15625) ≤ (256033 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 15623)) (n := 12)
    (lo := (8001 / 31250000)) (hi := (256033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15621) = 1/(15621 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8526 : Bounds (-256033 / 1000000000) (-8001 / 31250000) (Real.log (15621 / 15625)) := by
  have h := reflection_log_8526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8527_neg : (15183917 / 125000000) ≤ -Real.log (1000000 / 1129157) ∧
    -Real.log (1000000 / 1129157) ≤ (121471337 / 1000000000) := by
  have h := checkLog_sound (w := (129157 / 2129157)) (n := 12)
    (lo := (15183917 / 125000000)) (hi := (121471337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129157 / 1000000) = 1/(1000000 / 1129157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8527 : Bounds (15183917 / 125000000) (121471337 / 1000000000) (Real.log (1129157 / 1000000)) := by
  have h := reflection_log_8527_neg
  have he : Real.log (1129157 / 1000000) = -Real.log (1000000 / 1129157) := by
    rw [show ((1129157 / 1000000) : ℝ) = ((1000000 / 1129157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8528_neg : (13829357 / 100000000) ≤ -Real.log (870843 / 1000000) ∧
    -Real.log (870843 / 1000000) ≤ (138293571 / 1000000000) := by
  have h := checkLog_sound (w := (129157 / 1870843)) (n := 12)
    (lo := (13829357 / 100000000)) (hi := (138293571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870843) = 1/(870843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8528 : Bounds (-138293571 / 1000000000) (-13829357 / 100000000) (Real.log (870843 / 1000000)) := by
  have h := reflection_log_8528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8529_neg : (121924669 / 1000000000) ≤ -Real.log (1000000 / 1129669) ∧
    -Real.log (1000000 / 1129669) ≤ (12192467 / 100000000) := by
  have h := checkLog_sound (w := (129669 / 2129669)) (n := 12)
    (lo := (121924669 / 1000000000)) (hi := (12192467 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129669 / 1000000) = 1/(1000000 / 1129669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8529 : Bounds (121924669 / 1000000000) (12192467 / 100000000) (Real.log (1129669 / 1000000)) := by
  have h := reflection_log_8529_neg
  have he : Real.log (1129669 / 1000000) = -Real.log (1000000 / 1129669) := by
    rw [show ((1129669 / 1000000) : ℝ) = ((1000000 / 1129669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8530_neg : (138881679 / 1000000000) ≤ -Real.log (870331 / 1000000) ∧
    -Real.log (870331 / 1000000) ≤ (1736021 / 12500000) := by
  have h := checkLog_sound (w := (129669 / 1870331)) (n := 12)
    (lo := (138881679 / 1000000000)) (hi := (1736021 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870331) = 1/(870331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8530 : Bounds (-1736021 / 12500000) (-138881679 / 1000000000) (Real.log (870331 / 1000000)) := by
  have h := reflection_log_8530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8531_neg : (1695701 / 100000000) ≤ -Real.log (983185950439 / 1000000000000) ∧
    -Real.log (983185950439 / 1000000000000) ≤ (16957011 / 1000000000) := by
  have h := checkLog_sound (w := (16814049561 / 1983185950439)) (n := 12)
    (lo := (1695701 / 100000000)) (hi := (16957011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983185950439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983185950439) = 1/(983185950439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8531 : Bounds (-16957011 / 1000000000) (-1695701 / 100000000) (Real.log (983185950439 / 1000000000000)) := by
  have h := reflection_log_8531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8532_neg : (8411117 / 500000000) ≤ -Real.log (983318469351 / 1000000000000) ∧
    -Real.log (983318469351 / 1000000000000) ≤ (3364447 / 200000000) := by
  have h := checkLog_sound (w := (16681530649 / 1983318469351)) (n := 12)
    (lo := (8411117 / 500000000)) (hi := (3364447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983318469351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983318469351) = 1/(983318469351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8532 : Bounds (-3364447 / 200000000) (-8411117 / 500000000) (Real.log (983318469351 / 1000000000000)) := by
  have h := reflection_log_8532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8533_neg : (259764907 / 1000000000) ≤ -Real.log (7812500000 / 10129884563) ∧
    -Real.log (7812500000 / 10129884563) ≤ (64941227 / 250000000) := by
  have h := checkLog_sound (w := (2317384563 / 17942384563)) (n := 12)
    (lo := (259764907 / 1000000000)) (hi := (64941227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10129884563 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10129884563 / 7812500000) = 1/(7812500000 / 10129884563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8533 : Bounds (259764907 / 1000000000) (64941227 / 250000000) (Real.log (10129884563 / 7812500000)) := by
  have h := reflection_log_8533_neg
  have he : Real.log (10129884563 / 7812500000) = -Real.log (7812500000 / 10129884563) := by
    rw [show ((10129884563 / 7812500000) : ℝ) = ((7812500000 / 10129884563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8534_neg : (260806349 / 1000000000) ≤ -Real.log (62500000000 / 81123517949) ∧
    -Real.log (62500000000 / 81123517949) ≤ (5216127 / 20000000) := by
  have h := checkLog_sound (w := (18623517949 / 143623517949)) (n := 12)
    (lo := (260806349 / 1000000000)) (hi := (5216127 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81123517949 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81123517949 / 62500000000) = 1/(62500000000 / 81123517949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8534 : Bounds (260806349 / 1000000000) (5216127 / 20000000) (Real.log (81123517949 / 62500000000)) := by
  have h := reflection_log_8534_neg
  have he : Real.log (81123517949 / 62500000000) = -Real.log (62500000000 / 81123517949) := by
    rw [show ((81123517949 / 62500000000) : ℝ) = ((62500000000 / 81123517949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8535_neg : (261288163 / 500000000) ≤ -Real.log (250000000000 / 421591672263) ∧
    -Real.log (250000000000 / 421591672263) ≤ (522576327 / 1000000000) := by
  have h := checkLog_sound (w := (171591672263 / 671591672263)) (n := 12)
    (lo := (261288163 / 500000000)) (hi := (522576327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421591672263 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421591672263 / 250000000000) = 1/(250000000000 / 421591672263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8535 : Bounds (261288163 / 500000000) (522576327 / 1000000000) (Real.log (421591672263 / 250000000000)) := by
  have h := reflection_log_8535_neg
  have he : Real.log (421591672263 / 250000000000) = -Real.log (250000000000 / 421591672263) := by
    rw [show ((421591672263 / 250000000000) : ℝ) = ((250000000000 / 421591672263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8536_neg : (65455789 / 125000000) ≤ -Real.log (250000000000 / 422043010753) ∧
    -Real.log (250000000000 / 422043010753) ≤ (523646313 / 1000000000) := by
  have h := checkLog_sound (w := (172043010753 / 672043010753)) (n := 12)
    (lo := (65455789 / 125000000)) (hi := (523646313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422043010753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422043010753 / 250000000000) = 1/(250000000000 / 422043010753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8536 : Bounds (65455789 / 125000000) (523646313 / 1000000000) (Real.log (422043010753 / 250000000000)) := by
  have h := reflection_log_8536_neg
  have he : Real.log (422043010753 / 250000000000) = -Real.log (250000000000 / 422043010753) := by
    rw [show ((422043010753 / 250000000000) : ℝ) = ((250000000000 / 422043010753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8537_neg : (114165039 / 500000000) ≤ -Real.log (2000 / 2513) ∧
    -Real.log (2000 / 2513) ≤ (228330079 / 1000000000) := by
  have h := checkLog_sound (w := (513 / 4513)) (n := 12)
    (lo := (114165039 / 500000000)) (hi := (228330079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2513 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2513 / 2000) = 1/(2000 / 2513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8537 : Bounds (114165039 / 500000000) (228330079 / 1000000000) (Real.log (2513 / 2000)) := by
  have h := reflection_log_8537_neg
  have he : Real.log (2513 / 2000) = -Real.log (2000 / 2513) := by
    rw [show ((2513 / 2000) : ℝ) = ((2000 / 2513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8538_neg : (296386513 / 1000000000) ≤ -Real.log (1487 / 2000) ∧
    -Real.log (1487 / 2000) ≤ (148193257 / 500000000) := by
  have h := checkLog_sound (w := (513 / 3487)) (n := 12)
    (lo := (296386513 / 1000000000)) (hi := (148193257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1487) = 1/(1487 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8538 : Bounds (-148193257 / 500000000) (-296386513 / 1000000000) (Real.log (1487 / 2000)) := by
  have h := reflection_log_8538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8539_neg : (256467 / 1000000000) ≤ -Real.log (2000000 / 2000513) ∧
    -Real.log (2000000 / 2000513) ≤ (64117 / 250000000) := by
  have h := checkLog_sound (w := (513 / 4000513)) (n := 12)
    (lo := (256467 / 1000000000)) (hi := (64117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000513 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000513 / 2000000) = 1/(2000000 / 2000513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8539 : Bounds (256467 / 1000000000) (64117 / 250000000) (Real.log (2000513 / 2000000)) := by
  have h := reflection_log_8539_neg
  have he : Real.log (2000513 / 2000000) = -Real.log (2000000 / 2000513) := by
    rw [show ((2000513 / 2000000) : ℝ) = ((2000000 / 2000513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8540_neg : (64133 / 250000000) ≤ -Real.log (1999487 / 2000000) ∧
    -Real.log (1999487 / 2000000) ≤ (256533 / 1000000000) := by
  have h := checkLog_sound (w := (513 / 3999487)) (n := 12)
    (lo := (64133 / 250000000)) (hi := (256533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999487) = 1/(1999487 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8540 : Bounds (-256533 / 1000000000) (-64133 / 250000000) (Real.log (1999487 / 2000000)) := by
  have h := reflection_log_8540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8541_neg : (30425171 / 250000000) ≤ -Real.log (125000 / 141177) ∧
    -Real.log (125000 / 141177) ≤ (24340137 / 200000000) := by
  have h := checkLog_sound (w := (16177 / 266177)) (n := 12)
    (lo := (30425171 / 250000000)) (hi := (24340137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141177 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141177 / 125000) = 1/(125000 / 141177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8541 : Bounds (30425171 / 250000000) (24340137 / 200000000) (Real.log (141177 / 125000)) := by
  have h := reflection_log_8541_neg
  have he : Real.log (141177 / 125000) = -Real.log (125000 / 141177) := by
    rw [show ((141177 / 125000) : ℝ) = ((125000 / 141177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8542_neg : (34647757 / 250000000) ≤ -Real.log (108823 / 125000) ∧
    -Real.log (108823 / 125000) ≤ (138591029 / 1000000000) := by
  have h := checkLog_sound (w := (16177 / 233823)) (n := 12)
    (lo := (34647757 / 250000000)) (hi := (138591029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 108823) = 1/(108823 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8542 : Bounds (-138591029 / 1000000000) (-34647757 / 250000000) (Real.log (108823 / 125000)) := by
  have h := reflection_log_8542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8543_neg : (61077399 / 500000000) ≤ -Real.log (1000000 / 1129929) ∧
    -Real.log (1000000 / 1129929) ≤ (122154799 / 1000000000) := by
  have h := checkLog_sound (w := (129929 / 2129929)) (n := 12)
    (lo := (61077399 / 500000000)) (hi := (122154799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129929 / 1000000) = 1/(1000000 / 1129929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8543 : Bounds (61077399 / 500000000) (122154799 / 1000000000) (Real.log (1129929 / 1000000)) := by
  have h := reflection_log_8543_neg
  have he : Real.log (1129929 / 1000000) = -Real.log (1000000 / 1129929) := by
    rw [show ((1129929 / 1000000) : ℝ) = ((1000000 / 1129929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8544_neg : (139180461 / 1000000000) ≤ -Real.log (870071 / 1000000) ∧
    -Real.log (870071 / 1000000) ≤ (69590231 / 500000000) := by
  have h := checkLog_sound (w := (129929 / 1870071)) (n := 12)
    (lo := (139180461 / 1000000000)) (hi := (69590231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870071) = 1/(870071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8544 : Bounds (-69590231 / 500000000) (-139180461 / 1000000000) (Real.log (870071 / 1000000)) := by
  have h := reflection_log_8544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8545_neg : (8512831 / 500000000) ≤ -Real.log (983118454959 / 1000000000000) ∧
    -Real.log (983118454959 / 1000000000000) ≤ (17025663 / 1000000000) := by
  have h := checkLog_sound (w := (16881545041 / 1983118454959)) (n := 12)
    (lo := (8512831 / 500000000)) (hi := (17025663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983118454959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983118454959) = 1/(983118454959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8545 : Bounds (-17025663 / 1000000000) (-8512831 / 500000000) (Real.log (983118454959 / 1000000000000)) := by
  have h := reflection_log_8545_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8546_neg : (16890343 / 1000000000) ≤ -Real.log (15363304671 / 15625000000) ∧
    -Real.log (15363304671 / 15625000000) ≤ (2111293 / 125000000) := by
  have h := checkLog_sound (w := (261695329 / 30988304671)) (n := 12)
    (lo := (16890343 / 1000000000)) (hi := (2111293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15363304671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15363304671) = 1/(15363304671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8546 : Bounds (-2111293 / 125000000) (-16890343 / 1000000000) (Real.log (15363304671 / 15625000000)) := by
  have h := reflection_log_8546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8547_neg : (260291713 / 1000000000) ≤ -Real.log (62500000000 / 81081779587) ∧
    -Real.log (62500000000 / 81081779587) ≤ (130145857 / 500000000) := by
  have h := checkLog_sound (w := (18581779587 / 143581779587)) (n := 12)
    (lo := (260291713 / 1000000000)) (hi := (130145857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81081779587 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81081779587 / 62500000000) = 1/(62500000000 / 81081779587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8547 : Bounds (260291713 / 1000000000) (130145857 / 500000000) (Real.log (81081779587 / 62500000000)) := by
  have h := reflection_log_8547_neg
  have he : Real.log (81081779587 / 62500000000) = -Real.log (62500000000 / 81081779587) := by
    rw [show ((81081779587 / 62500000000) : ℝ) = ((62500000000 / 81081779587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8548_neg : (13066763 / 50000000) ≤ -Real.log (500000000000 / 649331491339) ∧
    -Real.log (500000000000 / 649331491339) ≤ (261335261 / 1000000000) := by
  have h := checkLog_sound (w := (149331491339 / 1149331491339)) (n := 12)
    (lo := (13066763 / 50000000)) (hi := (261335261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649331491339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649331491339 / 500000000000) = 1/(500000000000 / 649331491339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8548 : Bounds (13066763 / 50000000) (261335261 / 1000000000) (Real.log (649331491339 / 500000000000)) := by
  have h := reflection_log_8548_neg
  have he : Real.log (649331491339 / 500000000000) = -Real.log (500000000000 / 649331491339) := by
    rw [show ((649331491339 / 500000000000) : ℝ) = ((500000000000 / 649331491339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8549_neg : (65455789 / 125000000) ≤ -Real.log (100000000000 / 168817204301) ∧
    -Real.log (100000000000 / 168817204301) ≤ (523646313 / 1000000000) := by
  have h := checkLog_sound (w := (68817204301 / 268817204301)) (n := 12)
    (lo := (65455789 / 125000000)) (hi := (523646313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168817204301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168817204301 / 100000000000) = 1/(100000000000 / 168817204301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8549 : Bounds (65455789 / 125000000) (523646313 / 1000000000) (Real.log (168817204301 / 100000000000)) := by
  have h := reflection_log_8549_neg
  have he : Real.log (168817204301 / 100000000000) = -Real.log (100000000000 / 168817204301) := by
    rw [show ((168817204301 / 100000000000) : ℝ) = ((100000000000 / 168817204301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8550_neg : (524716591 / 1000000000) ≤ -Real.log (976562500 / 1650370923) ∧
    -Real.log (976562500 / 1650370923) ≤ (32794787 / 62500000) := by
  have h := checkLog_sound (w := (673808423 / 2626933423)) (n := 12)
    (lo := (524716591 / 1000000000)) (hi := (32794787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650370923 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650370923 / 976562500) = 1/(976562500 / 1650370923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8550 : Bounds (524716591 / 1000000000) (32794787 / 62500000) (Real.log (1650370923 / 976562500)) := by
  have h := reflection_log_8550_neg
  have he : Real.log (1650370923 / 976562500) = -Real.log (976562500 / 1650370923) := by
    rw [show ((1650370923 / 976562500) : ℝ) = ((976562500 / 1650370923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8551_neg : (228727929 / 1000000000) ≤ -Real.log (1000 / 1257) ∧
    -Real.log (1000 / 1257) ≤ (22872793 / 100000000) := by
  have h := checkLog_sound (w := (257 / 2257)) (n := 12)
    (lo := (228727929 / 1000000000)) (hi := (22872793 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1000) = 1/(1000 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8551 : Bounds (228727929 / 1000000000) (22872793 / 100000000) (Real.log (1257 / 1000)) := by
  have h := reflection_log_8551_neg
  have he : Real.log (1257 / 1000) = -Real.log (1000 / 1257) := by
    rw [show ((1257 / 1000) : ℝ) = ((1000 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8552_neg : (148529617 / 500000000) ≤ -Real.log (743 / 1000) ∧
    -Real.log (743 / 1000) ≤ (59411847 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1743)) (n := 12)
    (lo := (148529617 / 500000000)) (hi := (59411847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 743) = 1/(743 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8552 : Bounds (-59411847 / 200000000) (-148529617 / 500000000) (Real.log (743 / 1000)) := by
  have h := reflection_log_8552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8553_neg : (128483 / 500000000) ≤ -Real.log (1000000 / 1000257) ∧
    -Real.log (1000000 / 1000257) ≤ (256967 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2000257)) (n := 12)
    (lo := (128483 / 500000000)) (hi := (256967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000257 / 1000000) = 1/(1000000 / 1000257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8553 : Bounds (128483 / 500000000) (256967 / 1000000000) (Real.log (1000257 / 1000000)) := by
  have h := reflection_log_8553_neg
  have he : Real.log (1000257 / 1000000) = -Real.log (1000000 / 1000257) := by
    rw [show ((1000257 / 1000000) : ℝ) = ((1000000 / 1000257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8554_neg : (257033 / 1000000000) ≤ -Real.log (999743 / 1000000) ∧
    -Real.log (999743 / 1000000) ≤ (128517 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1999743)) (n := 12)
    (lo := (257033 / 1000000000)) (hi := (128517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999743) = 1/(999743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8554 : Bounds (-128517 / 500000000) (-257033 / 1000000000) (Real.log (999743 / 1000000)) := by
  have h := reflection_log_8554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8555_neg : (6096499 / 50000000) ≤ -Real.log (40000 / 45187) ∧
    -Real.log (40000 / 45187) ≤ (121929981 / 1000000000) := by
  have h := checkLog_sound (w := (5187 / 85187)) (n := 12)
    (lo := (6096499 / 50000000)) (hi := (121929981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45187 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45187 / 40000) = 1/(40000 / 45187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8555 : Bounds (6096499 / 50000000) (121929981 / 1000000000) (Real.log (45187 / 40000)) := by
  have h := reflection_log_8555_neg
  have he : Real.log (45187 / 40000) = -Real.log (40000 / 45187) := by
    rw [show ((45187 / 40000) : ℝ) = ((40000 / 45187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8556_neg : (138888573 / 1000000000) ≤ -Real.log (34813 / 40000) ∧
    -Real.log (34813 / 40000) ≤ (69444287 / 500000000) := by
  have h := checkLog_sound (w := (5187 / 74813)) (n := 12)
    (lo := (138888573 / 1000000000)) (hi := (69444287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34813) = 1/(34813 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8556 : Bounds (-69444287 / 500000000) (-138888573 / 1000000000) (Real.log (34813 / 40000)) := by
  have h := reflection_log_8556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8557_neg : (12238399 / 100000000) ≤ -Real.log (250000 / 282547) ∧
    -Real.log (250000 / 282547) ≤ (122383991 / 1000000000) := by
  have h := checkLog_sound (w := (32547 / 532547)) (n := 12)
    (lo := (12238399 / 100000000)) (hi := (122383991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282547 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282547 / 250000) = 1/(250000 / 282547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8557 : Bounds (12238399 / 100000000) (122383991 / 1000000000) (Real.log (282547 / 250000)) := by
  have h := reflection_log_8557_neg
  have he : Real.log (282547 / 250000) = -Real.log (250000 / 282547) := by
    rw [show ((282547 / 250000) : ℝ) = ((250000 / 282547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8558_neg : (69739091 / 500000000) ≤ -Real.log (217453 / 250000) ∧
    -Real.log (217453 / 250000) ≤ (139478183 / 1000000000) := by
  have h := checkLog_sound (w := (32547 / 467453)) (n := 12)
    (lo := (69739091 / 500000000)) (hi := (139478183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217453) = 1/(217453 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8558 : Bounds (-139478183 / 1000000000) (-69739091 / 500000000) (Real.log (217453 / 250000)) := by
  have h := reflection_log_8558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8559_neg : (1068387 / 62500000) ≤ -Real.log (61440692791 / 62500000000) ∧
    -Real.log (61440692791 / 62500000000) ≤ (17094193 / 1000000000) := by
  have h := checkLog_sound (w := (1059307209 / 123940692791)) (n := 12)
    (lo := (1068387 / 62500000)) (hi := (17094193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61440692791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61440692791) = 1/(61440692791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8559 : Bounds (-17094193 / 1000000000) (-1068387 / 62500000) (Real.log (61440692791 / 62500000000)) := by
  have h := reflection_log_8559_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8560_neg : (16958593 / 1000000000) ≤ -Real.log (1573095031 / 1600000000) ∧
    -Real.log (1573095031 / 1600000000) ≤ (8479297 / 500000000) := by
  have h := checkLog_sound (w := (26904969 / 3173095031)) (n := 12)
    (lo := (16958593 / 1000000000)) (hi := (8479297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1573095031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1573095031) = 1/(1573095031 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8560 : Bounds (-8479297 / 500000000) (-16958593 / 1000000000) (Real.log (1573095031 / 1600000000)) := by
  have h := reflection_log_8560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8561_neg : (130409277 / 500000000) ≤ -Real.log (31250000000 / 40562254043) ∧
    -Real.log (31250000000 / 40562254043) ≤ (52163711 / 200000000) := by
  have h := checkLog_sound (w := (9312254043 / 71812254043)) (n := 12)
    (lo := (130409277 / 500000000)) (hi := (52163711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40562254043 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40562254043 / 31250000000) = 1/(31250000000 / 40562254043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8561 : Bounds (130409277 / 500000000) (52163711 / 200000000) (Real.log (40562254043 / 31250000000)) := by
  have h := reflection_log_8561_neg
  have he : Real.log (40562254043 / 31250000000) = -Real.log (31250000000 / 40562254043) := by
    rw [show ((40562254043 / 31250000000) : ℝ) = ((31250000000 / 40562254043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8562_neg : (261862173 / 1000000000) ≤ -Real.log (250000000000 / 324836861299) ∧
    -Real.log (250000000000 / 324836861299) ≤ (130931087 / 500000000) := by
  have h := checkLog_sound (w := (74836861299 / 574836861299)) (n := 12)
    (lo := (261862173 / 1000000000)) (hi := (130931087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324836861299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324836861299 / 250000000000) = 1/(250000000000 / 324836861299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8562 : Bounds (261862173 / 1000000000) (130931087 / 500000000) (Real.log (324836861299 / 250000000000)) := by
  have h := reflection_log_8562_neg
  have he : Real.log (324836861299 / 250000000000) = -Real.log (250000000000 / 324836861299) := by
    rw [show ((324836861299 / 250000000000) : ℝ) = ((250000000000 / 324836861299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8563_neg : (524716591 / 1000000000) ≤ -Real.log (20000000000 / 33799596503) ∧
    -Real.log (20000000000 / 33799596503) ≤ (32794787 / 62500000) := by
  have h := checkLog_sound (w := (13799596503 / 53799596503)) (n := 12)
    (lo := (524716591 / 1000000000)) (hi := (32794787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33799596503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33799596503 / 20000000000) = 1/(20000000000 / 33799596503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8563 : Bounds (524716591 / 1000000000) (32794787 / 62500000) (Real.log (33799596503 / 20000000000)) := by
  have h := reflection_log_8563_neg
  have he : Real.log (33799596503 / 20000000000) = -Real.log (20000000000 / 33799596503) := by
    rw [show ((33799596503 / 20000000000) : ℝ) = ((20000000000 / 33799596503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8564_neg : (525787163 / 1000000000) ≤ -Real.log (500000000000 / 845895020189) ∧
    -Real.log (500000000000 / 845895020189) ≤ (131446791 / 250000000) := by
  have h := checkLog_sound (w := (345895020189 / 1345895020189)) (n := 12)
    (lo := (525787163 / 1000000000)) (hi := (131446791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845895020189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845895020189 / 500000000000) = 1/(500000000000 / 845895020189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8564 : Bounds (525787163 / 1000000000) (131446791 / 250000000) (Real.log (845895020189 / 500000000000)) := by
  have h := reflection_log_8564_neg
  have he : Real.log (845895020189 / 500000000000) = -Real.log (500000000000 / 845895020189) := by
    rw [show ((845895020189 / 500000000000) : ℝ) = ((500000000000 / 845895020189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8565_neg : (114562811 / 500000000) ≤ -Real.log (400 / 503) ∧
    -Real.log (400 / 503) ≤ (229125623 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 903)) (n := 12)
    (lo := (114562811 / 500000000)) (hi := (229125623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 400) = 1/(400 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8565 : Bounds (114562811 / 500000000) (229125623 / 1000000000) (Real.log (503 / 400)) := by
  have h := reflection_log_8565_neg
  have he : Real.log (503 / 400) = -Real.log (400 / 503) := by
    rw [show ((503 / 400) : ℝ) = ((400 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8566_neg : (37216551 / 125000000) ≤ -Real.log (297 / 400) ∧
    -Real.log (297 / 400) ≤ (297732409 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 697)) (n := 12)
    (lo := (37216551 / 125000000)) (hi := (297732409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 297) = 1/(297 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8566 : Bounds (-297732409 / 1000000000) (-37216551 / 125000000) (Real.log (297 / 400)) := by
  have h := reflection_log_8566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8567_neg : (128733 / 500000000) ≤ -Real.log (400000 / 400103) ∧
    -Real.log (400000 / 400103) ≤ (257467 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 800103)) (n := 12)
    (lo := (128733 / 500000000)) (hi := (257467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400103 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400103 / 400000) = 1/(400000 / 400103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8567 : Bounds (128733 / 500000000) (257467 / 1000000000) (Real.log (400103 / 400000)) := by
  have h := reflection_log_8567_neg
  have he : Real.log (400103 / 400000) = -Real.log (400000 / 400103) := by
    rw [show ((400103 / 400000) : ℝ) = ((400000 / 400103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8568_neg : (257533 / 1000000000) ≤ -Real.log (399897 / 400000) ∧
    -Real.log (399897 / 400000) ≤ (128767 / 500000000) := by
  have h := checkLog_sound (w := (103 / 799897)) (n := 12)
    (lo := (257533 / 1000000000)) (hi := (128767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399897) = 1/(399897 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8568 : Bounds (-128767 / 500000000) (-257533 / 1000000000) (Real.log (399897 / 400000)) := by
  have h := reflection_log_8568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8569_neg : (122159223 / 1000000000) ≤ -Real.log (500000 / 564967) ∧
    -Real.log (500000 / 564967) ≤ (15269903 / 125000000) := by
  have h := checkLog_sound (w := (64967 / 1064967)) (n := 12)
    (lo := (122159223 / 1000000000)) (hi := (15269903 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564967 / 500000) = 1/(500000 / 564967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8569 : Bounds (122159223 / 1000000000) (15269903 / 125000000) (Real.log (564967 / 500000)) := by
  have h := reflection_log_8569_neg
  have he : Real.log (564967 / 500000) = -Real.log (500000 / 564967) := by
    rw [show ((564967 / 500000) : ℝ) = ((500000 / 564967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8570_neg : (4349569 / 31250000) ≤ -Real.log (435033 / 500000) ∧
    -Real.log (435033 / 500000) ≤ (139186209 / 1000000000) := by
  have h := checkLog_sound (w := (64967 / 935033)) (n := 12)
    (lo := (4349569 / 31250000)) (hi := (139186209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435033) = 1/(435033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8570 : Bounds (-139186209 / 1000000000) (-4349569 / 31250000) (Real.log (435033 / 500000)) := by
  have h := reflection_log_8570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8571_neg : (61307007 / 500000000) ≤ -Real.log (62500 / 70653) ∧
    -Real.log (62500 / 70653) ≤ (24522803 / 200000000) := by
  have h := checkLog_sound (w := (8153 / 133153)) (n := 12)
    (lo := (61307007 / 500000000)) (hi := (24522803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70653 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70653 / 62500) = 1/(62500 / 70653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8571 : Bounds (61307007 / 500000000) (24522803 / 200000000) (Real.log (70653 / 62500)) := by
  have h := reflection_log_8571_neg
  have he : Real.log (70653 / 62500) = -Real.log (62500 / 70653) := by
    rw [show ((70653 / 62500) : ℝ) = ((62500 / 70653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8572_neg : (69888571 / 500000000) ≤ -Real.log (54347 / 62500) ∧
    -Real.log (54347 / 62500) ≤ (139777143 / 1000000000) := by
  have h := checkLog_sound (w := (8153 / 116847)) (n := 12)
    (lo := (69888571 / 500000000)) (hi := (139777143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54347) = 1/(54347 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8572 : Bounds (-139777143 / 1000000000) (-69888571 / 500000000) (Real.log (54347 / 62500)) := by
  have h := reflection_log_8572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8573_neg : (2145391 / 125000000) ≤ -Real.log (3839778591 / 3906250000) ∧
    -Real.log (3839778591 / 3906250000) ≤ (17163129 / 1000000000) := by
  have h := checkLog_sound (w := (66471409 / 7746028591)) (n := 12)
    (lo := (2145391 / 125000000)) (hi := (17163129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3839778591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3839778591) = 1/(3839778591 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8573 : Bounds (-17163129 / 1000000000) (-2145391 / 125000000) (Real.log (3839778591 / 3906250000)) := by
  have h := reflection_log_8573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8574_neg : (2128373 / 125000000) ≤ -Real.log (245779288911 / 250000000000) ∧
    -Real.log (245779288911 / 250000000000) ≤ (3405397 / 200000000) := by
  have h := checkLog_sound (w := (4220711089 / 495779288911)) (n := 12)
    (lo := (2128373 / 125000000)) (hi := (3405397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245779288911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245779288911) = 1/(245779288911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8574 : Bounds (-3405397 / 200000000) (-2128373 / 125000000) (Real.log (245779288911 / 250000000000)) := by
  have h := reflection_log_8574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8575_neg : (32668179 / 125000000) ≤ -Real.log (50000000000 / 64933809619) ∧
    -Real.log (50000000000 / 64933809619) ≤ (261345433 / 1000000000) := by
  have h := checkLog_sound (w := (14933809619 / 114933809619)) (n := 12)
    (lo := (32668179 / 125000000)) (hi := (261345433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64933809619 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64933809619 / 50000000000) = 1/(50000000000 / 64933809619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8575 : Bounds (32668179 / 125000000) (261345433 / 1000000000) (Real.log (64933809619 / 50000000000)) := by
  have h := reflection_log_8575_neg
  have he : Real.log (64933809619 / 50000000000) = -Real.log (50000000000 / 64933809619) := by
    rw [show ((64933809619 / 50000000000) : ℝ) = ((50000000000 / 64933809619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
