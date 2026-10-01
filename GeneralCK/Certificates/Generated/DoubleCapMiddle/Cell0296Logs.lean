import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0296
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

theorem reflection_log_1_neg : (8994433 / 40000000) ≤ -Real.log (5120 / 6411) ∧
    -Real.log (5120 / 6411) ≤ (112430413 / 500000000) := by
  have h := checkLog_sound (w := (1291 / 11531)) (n := 12)
    (lo := (8994433 / 40000000)) (hi := (112430413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6411 / 5120) = 1/(5120 / 6411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8994433 / 40000000) (112430413 / 500000000) (Real.log (6411 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6411 / 5120) = -Real.log (5120 / 6411) := by
    rw [show ((6411 / 5120) : ℝ) = ((5120 / 6411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (145275383 / 500000000) ≤ -Real.log (3829 / 5120) ∧
    -Real.log (3829 / 5120) ≤ (290550767 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 8949)) (n := 12)
    (lo := (145275383 / 500000000)) (hi := (290550767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3829) = 1/(3829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290550767 / 1000000000) (-145275383 / 500000000) (Real.log (3829 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8985073 / 40000000) ≤ -Real.log (10240 / 12819) ∧
    -Real.log (10240 / 12819) ≤ (112313413 / 500000000) := by
  have h := checkLog_sound (w := (2579 / 23059)) (n := 12)
    (lo := (8985073 / 40000000)) (hi := (112313413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10240) = 1/(10240 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8985073 / 40000000) (112313413 / 500000000) (Real.log (12819 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12819 / 10240) = -Real.log (10240 / 12819) := by
    rw [show ((12819 / 10240) : ℝ) = ((10240 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36269887 / 125000000) ≤ -Real.log (7661 / 10240) ∧
    -Real.log (7661 / 10240) ≤ (290159097 / 1000000000) := by
  have h := checkLog_sound (w := (2579 / 17901)) (n := 12)
    (lo := (36269887 / 125000000)) (hi := (290159097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7661) = 1/(7661 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290159097 / 1000000000) (-36269887 / 125000000) (Real.log (7661 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (102081399 / 250000000) ≤ -Real.log (2560 / 3851) ∧
    -Real.log (2560 / 3851) ≤ (408325597 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 6411)) (n := 12)
    (lo := (102081399 / 250000000)) (hi := (408325597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3851 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3851 / 2560) = 1/(2560 / 3851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (102081399 / 250000000) (408325597 / 1000000000) (Real.log (3851 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3851 / 2560) = -Real.log (2560 / 3851) := by
    rw [show ((3851 / 2560) : ℝ) = ((2560 / 3851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (701778069 / 1000000000) ≤ -Real.log (1269 / 2560) ∧
    -Real.log (1269 / 2560) ≤ (701778071 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 2549)) (n := 12)
    (lo := (8630889 / 1000000000)) (hi := (863089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1269) = 1/(1269 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-701778071 / 1000000000) (-701778069 / 1000000000) (Real.log (1269 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (407936011 / 1000000000) ≤ -Real.log (5120 / 7699) ∧
    -Real.log (5120 / 7699) ≤ (101984003 / 250000000) := by
  have h := checkLog_sound (w := (2579 / 12819)) (n := 12)
    (lo := (407936011 / 1000000000)) (hi := (101984003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7699 / 5120) = 1/(5120 / 7699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (407936011 / 1000000000) (101984003 / 250000000) (Real.log (7699 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7699 / 5120) = -Real.log (5120 / 7699) := by
    rw [show ((7699 / 5120) : ℝ) = ((5120 / 7699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (350298367 / 500000000) ≤ -Real.log (2541 / 5120) ∧
    -Real.log (2541 / 5120) ≤ (1368353 / 1953125) := by
  have h := checkLog_sound (w := (19 / 5101)) (n := 12)
    (lo := (3724777 / 500000000)) (hi := (1489911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2541) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2541) = 1/(2541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1368353 / 1953125) (-350298367 / 500000000) (Real.log (2541 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (307780979 / 1000000000) ≤ -Real.log (1000000 / 1360403) ∧
    -Real.log (1000000 / 1360403) ≤ (15389049 / 50000000) := by
  have h := checkLog_sound (w := (360403 / 2360403)) (n := 12)
    (lo := (307780979 / 1000000000)) (hi := (15389049 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360403 / 1000000) = 1/(1000000 / 1360403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (307780979 / 1000000000) (15389049 / 50000000) (Real.log (1360403 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1360403 / 1000000) = -Real.log (1000000 / 1360403) := by
    rw [show ((1360403 / 1000000) : ℝ) = ((1000000 / 1360403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111729247 / 250000000) ≤ -Real.log (639597 / 1000000) ∧
    -Real.log (639597 / 1000000) ≤ (446916989 / 1000000000) := by
  have h := checkLog_sound (w := (360403 / 1639597)) (n := 12)
    (lo := (111729247 / 250000000)) (hi := (446916989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639597) = 1/(639597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-446916989 / 1000000000) (-111729247 / 250000000) (Real.log (639597 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308097747 / 1000000000) ≤ -Real.log (500000 / 680417) ∧
    -Real.log (500000 / 680417) ≤ (77024437 / 250000000) := by
  have h := checkLog_sound (w := (180417 / 1180417)) (n := 12)
    (lo := (308097747 / 1000000000)) (hi := (77024437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680417 / 500000) = 1/(500000 / 680417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308097747 / 1000000000) (77024437 / 250000000) (Real.log (680417 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (680417 / 500000) = -Real.log (500000 / 680417) := by
    rw [show ((680417 / 500000) : ℝ) = ((500000 / 680417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (447591077 / 1000000000) ≤ -Real.log (319583 / 500000) ∧
    -Real.log (319583 / 500000) ≤ (223795539 / 500000000) := by
  have h := checkLog_sound (w := (180417 / 819583)) (n := 12)
    (lo := (447591077 / 1000000000)) (hi := (223795539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319583) = 1/(319583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223795539 / 500000000) (-447591077 / 1000000000) (Real.log (319583 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58637957 / 250000000) ≤ -Real.log (500000 / 632171) ∧
    -Real.log (500000 / 632171) ≤ (234551829 / 1000000000) := by
  have h := checkLog_sound (w := (132171 / 1132171)) (n := 12)
    (lo := (58637957 / 250000000)) (hi := (234551829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632171 / 500000) = 1/(500000 / 632171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58637957 / 250000000) (234551829 / 1000000000) (Real.log (632171 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (632171 / 500000) = -Real.log (500000 / 632171) := by
    rw [show ((632171 / 500000) : ℝ) = ((500000 / 632171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (153494971 / 500000000) ≤ -Real.log (367829 / 500000) ∧
    -Real.log (367829 / 500000) ≤ (306989943 / 1000000000) := by
  have h := checkLog_sound (w := (132171 / 867829)) (n := 12)
    (lo := (153494971 / 500000000)) (hi := (306989943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367829) = 1/(367829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306989943 / 1000000000) (-153494971 / 500000000) (Real.log (367829 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (234820707 / 1000000000) ≤ -Real.log (500000 / 632341) ∧
    -Real.log (500000 / 632341) ≤ (58705177 / 250000000) := by
  have h := checkLog_sound (w := (132341 / 1132341)) (n := 12)
    (lo := (234820707 / 1000000000)) (hi := (58705177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632341 / 500000) = 1/(500000 / 632341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (234820707 / 1000000000) (58705177 / 250000000) (Real.log (632341 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (632341 / 500000) = -Real.log (500000 / 632341) := by
    rw [show ((632341 / 500000) : ℝ) = ((500000 / 632341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15372611 / 50000000) ≤ -Real.log (367659 / 500000) ∧
    -Real.log (367659 / 500000) ≤ (307452221 / 1000000000) := by
  have h := checkLog_sound (w := (132341 / 867659)) (n := 12)
    (lo := (15372611 / 50000000)) (hi := (307452221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367659) = 1/(367659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-307452221 / 1000000000) (-15372611 / 50000000) (Real.log (367659 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (754697967 / 1000000000) ≤ -Real.log (10000000000 / 21269690133) ∧
    -Real.log (10000000000 / 21269690133) ≤ (754697969 / 1000000000) := by
  have h := checkLog_sound (w := (1269690133 / 41269690133)) (n := 12)
    (lo := (61550787 / 1000000000)) (hi := (15387697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21269690133 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21269690133 / 20000000000) = 1/(10000000000 / 21269690133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (754697967 / 1000000000) (754697969 / 1000000000) (Real.log (21269690133 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21269690133 / 10000000000) = -Real.log (10000000000 / 21269690133) := by
    rw [show ((21269690133 / 10000000000) : ℝ) = ((10000000000 / 21269690133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (755688823 / 1000000000) ≤ -Real.log (500000000000 / 1064538789611) ∧
    -Real.log (500000000000 / 1064538789611) ≤ (30227553 / 40000000) := by
  have h := checkLog_sound (w := (64538789611 / 2064538789611)) (n := 12)
    (lo := (62541643 / 1000000000)) (hi := (15635411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064538789611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064538789611 / 1000000000000) = 1/(500000000000 / 1064538789611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (755688823 / 1000000000) (30227553 / 40000000) (Real.log (1064538789611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1064538789611 / 500000000000) = -Real.log (500000000000 / 1064538789611) := by
    rw [show ((1064538789611 / 500000000000) : ℝ) = ((500000000000 / 1064538789611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54154177 / 100000000) ≤ -Real.log (500000000000 / 859327296107) ∧
    -Real.log (500000000000 / 859327296107) ≤ (541541771 / 1000000000) := by
  have h := checkLog_sound (w := (359327296107 / 1359327296107)) (n := 12)
    (lo := (54154177 / 100000000)) (hi := (541541771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859327296107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859327296107 / 500000000000) = 1/(500000000000 / 859327296107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54154177 / 100000000) (541541771 / 1000000000) (Real.log (859327296107 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (859327296107 / 500000000000) = -Real.log (500000000000 / 859327296107) := by
    rw [show ((859327296107 / 500000000000) : ℝ) = ((500000000000 / 859327296107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (542272927 / 1000000000) ≤ -Real.log (100000000000 / 171991165727) ∧
    -Real.log (100000000000 / 171991165727) ≤ (16946029 / 31250000) := by
  have h := checkLog_sound (w := (71991165727 / 271991165727)) (n := 12)
    (lo := (542272927 / 1000000000)) (hi := (16946029 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171991165727 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171991165727 / 100000000000) = 1/(100000000000 / 171991165727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (542272927 / 1000000000) (16946029 / 31250000) (Real.log (171991165727 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (171991165727 / 100000000000) = -Real.log (100000000000 / 171991165727) := by
    rw [show ((171991165727 / 100000000000) : ℝ) = ((100000000000 / 171991165727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0296
