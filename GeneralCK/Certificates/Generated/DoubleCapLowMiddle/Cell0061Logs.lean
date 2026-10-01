import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061
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

theorem reflection_log_1_neg : (169505907 / 250000000) ≤ -Real.log (51200 / 100863) ∧
    -Real.log (51200 / 100863) ≤ (678023629 / 1000000000) := by
  have h := checkLog_sound (w := (49663 / 152063)) (n := 12)
    (lo := (169505907 / 250000000)) (hi := (678023629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100863 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100863 / 51200) = 1/(51200 / 100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169505907 / 250000000) (678023629 / 1000000000) (Real.log (100863 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100863 / 51200) = -Real.log (51200 / 100863) := by
    rw [show ((100863 / 51200) : ℝ) = ((51200 / 100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (438238383 / 125000000) ≤ -Real.log (1537 / 51200) ∧
    -Real.log (1537 / 51200) ≤ (350590707 / 100000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1537) = 1/(1537 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-350590707 / 100000000) (-438238383 / 125000000) (Real.log (1537 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169482359 / 250000000) ≤ -Real.log (102400 / 201707) ∧
    -Real.log (102400 / 201707) ≤ (677929437 / 1000000000) := by
  have h := checkLog_sound (w := (99307 / 304107)) (n := 12)
    (lo := (169482359 / 250000000)) (hi := (677929437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201707 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201707 / 102400) = 1/(102400 / 201707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169482359 / 250000000) (677929437 / 1000000000) (Real.log (201707 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201707 / 102400) = -Real.log (102400 / 201707) := by
    rw [show ((201707 / 102400) : ℝ) = ((102400 / 201707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (54683519 / 15625000) ≤ -Real.log (3093 / 102400) ∧
    -Real.log (3093 / 102400) ≤ (1749872611 / 500000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3093) = 1/(3093 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1749872611 / 500000000) (-54683519 / 15625000) (Real.log (3093 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (662667837 / 1000000000) ≤ -Real.log (25600 / 49663) ∧
    -Real.log (25600 / 49663) ≤ (331333919 / 500000000) := by
  have h := checkLog_sound (w := (24063 / 75263)) (n := 12)
    (lo := (662667837 / 1000000000)) (hi := (331333919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49663 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49663 / 25600) = 1/(25600 / 49663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (662667837 / 1000000000) (331333919 / 500000000) (Real.log (49663 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49663 / 25600) = -Real.log (25600 / 49663) := by
    rw [show ((49663 / 25600) : ℝ) = ((25600 / 49663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (703189971 / 250000000) ≤ -Real.log (1537 / 25600) ∧
    -Real.log (1537 / 25600) ≤ (2812759889 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1537) = 1/(1537 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2812759889 / 1000000000) (-703189971 / 250000000) (Real.log (1537 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (662476529 / 1000000000) ≤ -Real.log (51200 / 99307) ∧
    -Real.log (51200 / 99307) ≤ (66247653 / 100000000) := by
  have h := checkLog_sound (w := (48107 / 150507)) (n := 12)
    (lo := (662476529 / 1000000000)) (hi := (66247653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99307 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99307 / 51200) = 1/(51200 / 99307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (662476529 / 1000000000) (66247653 / 100000000) (Real.log (99307 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99307 / 51200) = -Real.log (51200 / 99307) := by
    rw [show ((99307 / 51200) : ℝ) = ((51200 / 99307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (701649509 / 250000000) ≤ -Real.log (3093 / 51200) ∧
    -Real.log (3093 / 51200) ≤ (2806598041 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3093) = 1/(3093 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2806598041 / 1000000000) (-701649509 / 250000000) (Real.log (3093 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85055669 / 125000000) ≤ -Real.log (1000000 / 1974757) ∧
    -Real.log (1000000 / 1974757) ≤ (680445353 / 1000000000) := by
  have h := checkLog_sound (w := (974757 / 2974757)) (n := 12)
    (lo := (85055669 / 125000000)) (hi := (680445353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974757 / 1000000) = 1/(1000000 / 1974757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85055669 / 125000000) (680445353 / 1000000000) (Real.log (1974757 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974757 / 1000000) = -Real.log (1000000 / 1974757) := by
    rw [show ((1974757 / 1000000) : ℝ) = ((1000000 / 1974757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1839603193 / 500000000) ≤ -Real.log (25243 / 1000000) ∧
    -Real.log (25243 / 1000000) ≤ (459900799 / 125000000) := by
  have h := checkLog_sound (w := (6007 / 56493)) (n := 12)
    (lo := (106735243 / 500000000)) (hi := (213470487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25243) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25243) = 1/(25243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-459900799 / 125000000) (-1839603193 / 500000000) (Real.log (25243 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136104059 / 200000000) ≤ -Real.log (200000 / 394981) ∧
    -Real.log (200000 / 394981) ≤ (85065037 / 125000000) := by
  have h := checkLog_sound (w := (194981 / 594981)) (n := 12)
    (lo := (136104059 / 200000000)) (hi := (85065037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394981 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394981 / 200000) = 1/(200000 / 394981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136104059 / 200000000) (85065037 / 125000000) (Real.log (394981 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394981 / 200000) = -Real.log (200000 / 394981) := by
    rw [show ((394981 / 200000) : ℝ) = ((200000 / 394981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3685086653 / 1000000000) ≤ -Real.log (5019 / 200000) ∧
    -Real.log (5019 / 200000) ≤ (3685086659 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 11269)) (n := 12)
    (lo := (219350753 / 1000000000)) (hi := (109675377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5019) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5019) = 1/(5019 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3685086659 / 1000000000) (-3685086653 / 1000000000) (Real.log (5019 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680366859 / 1000000000) ≤ -Real.log (500000 / 987301) ∧
    -Real.log (500000 / 987301) ≤ (34018343 / 50000000) := by
  have h := checkLog_sound (w := (487301 / 1487301)) (n := 12)
    (lo := (680366859 / 1000000000)) (hi := (34018343 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987301 / 500000) = 1/(500000 / 987301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680366859 / 1000000000) (34018343 / 50000000) (Real.log (987301 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987301 / 500000) = -Real.log (500000 / 987301) := by
    rw [show ((987301 / 500000) : ℝ) = ((500000 / 987301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (734616969 / 200000000) ≤ -Real.log (12699 / 500000) ∧
    -Real.log (12699 / 500000) ≤ (3673084851 / 1000000000) := by
  have h := checkLog_sound (w := (1463 / 14162)) (n := 12)
    (lo := (41469789 / 200000000)) (hi := (103674473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12699) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12699) = 1/(12699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3673084851 / 1000000000) (-734616969 / 200000000) (Real.log (12699 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680443327 / 1000000000) ≤ -Real.log (1000000 / 1974753) ∧
    -Real.log (1000000 / 1974753) ≤ (10631927 / 15625000) := by
  have h := checkLog_sound (w := (974753 / 2974753)) (n := 12)
    (lo := (680443327 / 1000000000)) (hi := (10631927 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974753 / 1000000) = 1/(1000000 / 1974753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680443327 / 1000000000) (10631927 / 15625000) (Real.log (1974753 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974753 / 1000000) = -Real.log (1000000 / 1974753) := by
    rw [show ((1974753 / 1000000) : ℝ) = ((1000000 / 1974753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3679047939 / 1000000000) ≤ -Real.log (25247 / 1000000) ∧
    -Real.log (25247 / 1000000) ≤ (735809589 / 200000000) := by
  have h := checkLog_sound (w := (6003 / 56497)) (n := 12)
    (lo := (213312039 / 1000000000)) (hi := (5332801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25247) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25247) = 1/(25247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-735809589 / 200000000) (-3679047939 / 1000000000) (Real.log (25247 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2179825869 / 500000000) ≤ -Real.log (500000000000 / 39114942756407) ∧
    -Real.log (500000000000 / 39114942756407) ≤ (871930349 / 200000000) := by
  have h := checkLog_sound (w := (7114942756407 / 71114942756407)) (n := 12)
    (lo := (100384329 / 500000000)) (hi := (200768659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39114942756407 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39114942756407 / 32000000000000) = 1/(500000000000 / 39114942756407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2179825869 / 500000000) (871930349 / 200000000) (Real.log (39114942756407 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39114942756407 / 500000000000) = -Real.log (500000000000 / 39114942756407) := by
    rw [show ((39114942756407 / 500000000000) : ℝ) = ((500000000000 / 39114942756407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1091401737 / 250000000) ≤ -Real.log (500000000000 / 39348575413429) ∧
    -Real.log (500000000000 / 39348575413429) ≤ (873121391 / 200000000) := by
  have h := checkLog_sound (w := (7348575413429 / 71348575413429)) (n := 12)
    (lo := (51680967 / 250000000)) (hi := (206723869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39348575413429 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39348575413429 / 32000000000000) = 1/(500000000000 / 39348575413429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1091401737 / 250000000) (873121391 / 200000000) (Real.log (39348575413429 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (39348575413429 / 500000000000) = -Real.log (500000000000 / 39348575413429) := by
    rw [show ((39348575413429 / 500000000000) : ℝ) = ((500000000000 / 39348575413429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4353451703 / 1000000000) ≤ -Real.log (500000000000 / 38873178990471) ∧
    -Real.log (500000000000 / 38873178990471) ≤ (435345171 / 100000000) := by
  have h := checkLog_sound (w := (6873178990471 / 70873178990471)) (n := 12)
    (lo := (194568623 / 1000000000)) (hi := (12160539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38873178990471 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38873178990471 / 32000000000000) = 1/(500000000000 / 38873178990471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4353451703 / 1000000000) (435345171 / 100000000) (Real.log (38873178990471 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38873178990471 / 500000000000) = -Real.log (500000000000 / 38873178990471) := by
    rw [show ((38873178990471 / 500000000000) : ℝ) = ((500000000000 / 38873178990471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2179745633 / 500000000) ≤ -Real.log (125000000000 / 9777166594051) ∧
    -Real.log (125000000000 / 9777166594051) ≤ (4359491273 / 1000000000) := by
  have h := checkLog_sound (w := (1777166594051 / 17777166594051)) (n := 12)
    (lo := (100304093 / 500000000)) (hi := (200608187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9777166594051 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9777166594051 / 8000000000000) = 1/(125000000000 / 9777166594051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2179745633 / 500000000) (4359491273 / 1000000000) (Real.log (9777166594051 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9777166594051 / 125000000000) = -Real.log (125000000000 / 9777166594051) := by
    rw [show ((9777166594051 / 125000000000) : ℝ) = ((125000000000 / 9777166594051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061
