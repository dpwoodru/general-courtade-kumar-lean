import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0007
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

theorem reflection_log_1_neg : (170692201 / 250000000) ≤ -Real.log (500000000000 / 989675292969) ∧
    -Real.log (500000000000 / 989675292969) ≤ (136553761 / 200000000) := by
  have h := checkLog_sound (w := (489675292969 / 1489675292969)) (n := 12)
    (lo := (170692201 / 250000000)) (hi := (136553761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989675292969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989675292969 / 500000000000) = 1/(500000000000 / 989675292969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170692201 / 250000000) (136553761 / 200000000) (Real.log (989675292969 / 500000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (989675292969 / 500000000000) = -Real.log (500000000000 / 989675292969) := by
    rw [show ((989675292969 / 500000000000) : ℝ) = ((500000000000 / 989675292969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3880068331 / 1000000000) ≤ -Real.log (10324707031 / 500000000000) ∧
    -Real.log (10324707031 / 500000000000) ≤ (3880068337 / 1000000000) := by
  have h := checkLog_sound (w := (5300292969 / 25949707031)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10324707031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10324707031) = 1/(10324707031 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3880068337 / 1000000000) (-3880068331 / 1000000000) (Real.log (10324707031 / 500000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170680483 / 250000000) ≤ -Real.log (25600 / 50669) ∧
    -Real.log (25600 / 50669) ≤ (682721933 / 1000000000) := by
  have h := checkLog_sound (w := (25069 / 76269)) (n := 12)
    (lo := (170680483 / 250000000)) (hi := (682721933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50669 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50669 / 25600) = 1/(25600 / 50669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170680483 / 250000000) (682721933 / 1000000000) (Real.log (50669 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50669 / 25600) = -Real.log (25600 / 50669) := by
    rw [show ((50669 / 25600) : ℝ) = ((25600 / 50669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1937792803 / 500000000) ≤ -Real.log (531 / 25600) ∧
    -Real.log (531 / 25600) ≤ (968896403 / 250000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 531) = 1/(531 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-968896403 / 250000000) (-1937792803 / 500000000) (Real.log (531 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (336140793 / 500000000) ≤ -Real.log (102400 / 200571) ∧
    -Real.log (102400 / 200571) ≤ (672281587 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 302971)) (n := 12)
    (lo := (336140793 / 500000000)) (hi := (672281587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200571 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200571 / 102400) = 1/(102400 / 200571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (336140793 / 500000000) (672281587 / 1000000000) (Real.log (200571 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200571 / 102400) = -Real.log (102400 / 200571) := by
    rw [show ((200571 / 102400) : ℝ) = ((102400 / 200571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3186921151 / 1000000000) ≤ -Real.log (4229 / 102400) ∧
    -Real.log (4229 / 102400) ≤ (796730289 / 250000000) := by
  have h := checkLog_sound (w := (2171 / 10629)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4229) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4229) = 1/(4229 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-796730289 / 250000000) (-3186921151 / 1000000000) (Real.log (4229 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168046713 / 250000000) ≤ -Real.log (12800 / 25069) ∧
    -Real.log (12800 / 25069) ≤ (672186853 / 1000000000) := by
  have h := checkLog_sound (w := (12269 / 37869)) (n := 12)
    (lo := (168046713 / 250000000)) (hi := (672186853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25069 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25069 / 12800) = 1/(12800 / 25069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168046713 / 250000000) (672186853 / 1000000000) (Real.log (25069 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (25069 / 12800) = -Real.log (12800 / 25069) := by
    rw [show ((25069 / 12800) : ℝ) = ((12800 / 25069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1591219213 / 500000000) ≤ -Real.log (531 / 12800) ∧
    -Real.log (531 / 12800) ≤ (3182438431 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 531) = 1/(531 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3182438431 / 1000000000) (-1591219213 / 500000000) (Real.log (531 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684298143 / 1000000000) ≤ -Real.log (50000 / 99119) ∧
    -Real.log (50000 / 99119) ≤ (21384317 / 31250000) := by
  have h := checkLog_sound (w := (49119 / 149119)) (n := 12)
    (lo := (684298143 / 1000000000)) (hi := (21384317 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99119 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99119 / 50000) = 1/(50000 / 99119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684298143 / 1000000000) (21384317 / 31250000) (Real.log (99119 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (99119 / 50000) = -Real.log (50000 / 99119) := by
    rw [show ((99119 / 50000) : ℝ) = ((50000 / 99119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (807744131 / 200000000) ≤ -Real.log (881 / 50000) ∧
    -Real.log (881 / 50000) ≤ (4038720661 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 4887)) (n := 12)
    (lo := (114596951 / 200000000)) (hi := (143246189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1762) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1762) = 1/(881 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4038720661 / 1000000000) (-807744131 / 200000000) (Real.log (881 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85542123 / 125000000) ≤ -Real.log (1000000 / 1982457) ∧
    -Real.log (1000000 / 1982457) ≤ (136867397 / 200000000) := by
  have h := checkLog_sound (w := (982457 / 2982457)) (n := 12)
    (lo := (85542123 / 125000000)) (hi := (136867397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982457 / 1000000) = 1/(1000000 / 1982457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85542123 / 125000000) (136867397 / 200000000) (Real.log (1982457 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982457 / 1000000) = -Real.log (1000000 / 1982457) := by
    rw [show ((1982457 / 1000000) : ℝ) = ((1000000 / 1982457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2021550133 / 500000000) ≤ -Real.log (17543 / 1000000) ∧
    -Real.log (17543 / 1000000) ≤ (252693767 / 62500000) := by
  have h := checkLog_sound (w := (13707 / 48793)) (n := 12)
    (lo := (288682183 / 500000000)) (hi := (577364367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17543) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17543) = 1/(17543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-252693767 / 62500000) (-2021550133 / 500000000) (Real.log (17543 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684264849 / 1000000000) ≤ -Real.log (500000 / 991157) ∧
    -Real.log (500000 / 991157) ≤ (13685297 / 20000000) := by
  have h := checkLog_sound (w := (491157 / 1491157)) (n := 12)
    (lo := (684264849 / 1000000000)) (hi := (13685297 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991157 / 500000) = 1/(500000 / 991157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684264849 / 1000000000) (13685297 / 20000000) (Real.log (991157 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991157 / 500000) = -Real.log (500000 / 991157) := by
    rw [show ((991157 / 500000) : ℝ) = ((500000 / 991157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (403498191 / 100000000) ≤ -Real.log (8843 / 500000) ∧
    -Real.log (8843 / 500000) ≤ (1008745479 / 250000000) := by
  have h := checkLog_sound (w := (3391 / 12234)) (n := 12)
    (lo := (56924601 / 100000000)) (hi := (569246011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8843) = 1/(8843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1008745479 / 250000000) (-403498191 / 100000000) (Real.log (8843 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684303691 / 1000000000) ≤ -Real.log (1000000 / 1982391) ∧
    -Real.log (1000000 / 1982391) ≤ (171075923 / 250000000) := by
  have h := checkLog_sound (w := (982391 / 2982391)) (n := 12)
    (lo := (684303691 / 1000000000)) (hi := (171075923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982391 / 1000000) = 1/(1000000 / 1982391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684303691 / 1000000000) (171075923 / 250000000) (Real.log (1982391 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982391 / 1000000) = -Real.log (1000000 / 1982391) := by
    rw [show ((1982391 / 1000000) : ℝ) = ((1000000 / 1982391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4039345141 / 1000000000) ≤ -Real.log (17609 / 1000000) ∧
    -Real.log (17609 / 1000000) ≤ (4039345147 / 1000000000) := by
  have h := checkLog_sound (w := (13641 / 48859)) (n := 12)
    (lo := (573609241 / 1000000000)) (hi := (286804621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17609) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17609) = 1/(17609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4039345147 / 1000000000) (-4039345141 / 1000000000) (Real.log (17609 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2361509399 / 500000000) ≤ -Real.log (62500000000 / 7031711123723) ∧
    -Real.log (62500000000 / 7031711123723) ≤ (944603761 / 200000000) := by
  have h := checkLog_sound (w := (3031711123723 / 11031711123723)) (n := 12)
    (lo := (282067859 / 500000000)) (hi := (564135719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7031711123723 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7031711123723 / 4000000000000) = 1/(62500000000 / 7031711123723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2361509399 / 500000000) (944603761 / 200000000) (Real.log (7031711123723 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7031711123723 / 62500000000) = -Real.log (62500000000 / 7031711123723) := by
    rw [show ((7031711123723 / 62500000000) : ℝ) = ((62500000000 / 7031711123723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18909749 / 4000000) ≤ -Real.log (15625000000 / 1765712285527) ∧
    -Real.log (15625000000 / 1765712285527) ≤ (4727437257 / 1000000000) := by
  have h := checkLog_sound (w := (765712285527 / 2765712285527)) (n := 12)
    (lo := (56855417 / 100000000)) (hi := (568554171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1765712285527 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1765712285527 / 1000000000000) = 1/(15625000000 / 1765712285527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18909749 / 4000000) (4727437257 / 1000000000) (Real.log (1765712285527 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1765712285527 / 15625000000) = -Real.log (15625000000 / 1765712285527) := by
    rw [show ((1765712285527 / 15625000000) : ℝ) = ((15625000000 / 1765712285527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2359623379 / 500000000) ≤ -Real.log (500000000000 / 56041897546081) ∧
    -Real.log (500000000000 / 56041897546081) ≤ (943849353 / 200000000) := by
  have h := checkLog_sound (w := (24041897546081 / 88041897546081)) (n := 12)
    (lo := (280181839 / 500000000)) (hi := (560363679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56041897546081 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56041897546081 / 32000000000000) = 1/(500000000000 / 56041897546081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2359623379 / 500000000) (943849353 / 200000000) (Real.log (56041897546081 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56041897546081 / 500000000000) = -Real.log (500000000000 / 56041897546081) := by
    rw [show ((56041897546081 / 500000000000) : ℝ) = ((500000000000 / 56041897546081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (73807013 / 15625000) ≤ -Real.log (250000000000 / 28144570958033) ∧
    -Real.log (250000000000 / 28144570958033) ≤ (4723648839 / 1000000000) := by
  have h := checkLog_sound (w := (12144570958033 / 44144570958033)) (n := 12)
    (lo := (70595719 / 125000000)) (hi := (564765753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28144570958033 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28144570958033 / 16000000000000) = 1/(250000000000 / 28144570958033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (73807013 / 15625000) (4723648839 / 1000000000) (Real.log (28144570958033 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28144570958033 / 250000000000) = -Real.log (250000000000 / 28144570958033) := by
    rw [show ((28144570958033 / 250000000000) : ℝ) = ((250000000000 / 28144570958033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0007
