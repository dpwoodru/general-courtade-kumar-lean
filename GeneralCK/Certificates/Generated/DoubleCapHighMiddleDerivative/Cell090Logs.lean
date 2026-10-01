import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell090
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (132457547 / 500000000) ≤ -Real.log (5120 / 6673) ∧
    -Real.log (5120 / 6673) ≤ (52983019 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 11793)) (n := 12)
    (lo := (132457547 / 500000000)) (hi := (52983019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6673 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6673 / 5120) = 1/(5120 / 6673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132457547 / 500000000) (52983019 / 200000000) (Real.log (6673 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6673 / 5120) = -Real.log (5120 / 6673) := by
    rw [show ((6673 / 5120) : ℝ) = ((5120 / 6673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (90357383 / 250000000) ≤ -Real.log (3567 / 5120) ∧
    -Real.log (3567 / 5120) ≤ (361429533 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 8687)) (n := 12)
    (lo := (90357383 / 250000000)) (hi := (361429533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3567) = 1/(3567 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-361429533 / 1000000000) (-90357383 / 250000000) (Real.log (3567 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13223271 / 50000000) ≤ -Real.log (512 / 667) ∧
    -Real.log (512 / 667) ≤ (264465421 / 1000000000) := by
  have h := checkLog_sound (w := (155 / 1179)) (n := 12)
    (lo := (13223271 / 50000000)) (hi := (264465421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 512) = 1/(512 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13223271 / 50000000) (264465421 / 1000000000) (Real.log (667 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (667 / 512) = -Real.log (512 / 667) := by
    rw [show ((667 / 512) : ℝ) = ((512 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (360588843 / 1000000000) ≤ -Real.log (357 / 512) ∧
    -Real.log (357 / 512) ≤ (90147211 / 250000000) := by
  have h := checkLog_sound (w := (155 / 869)) (n := 12)
    (lo := (360588843 / 1000000000)) (hi := (90147211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 357) = 1/(357 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-90147211 / 250000000) (-360588843 / 1000000000) (Real.log (357 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38934823 / 200000000) ≤ -Real.log (200000 / 242983) ∧
    -Real.log (200000 / 242983) ≤ (48668529 / 250000000) := by
  have h := checkLog_sound (w := (42983 / 442983)) (n := 12)
    (lo := (38934823 / 200000000)) (hi := (48668529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242983 / 200000) = 1/(200000 / 242983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38934823 / 200000000) (48668529 / 250000000) (Real.log (242983 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (242983 / 200000) = -Real.log (200000 / 242983) := by
    rw [show ((242983 / 200000) : ℝ) = ((200000 / 242983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (120981643 / 500000000) ≤ -Real.log (157017 / 200000) ∧
    -Real.log (157017 / 200000) ≤ (241963287 / 1000000000) := by
  have h := checkLog_sound (w := (42983 / 357017)) (n := 12)
    (lo := (120981643 / 500000000)) (hi := (241963287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157017) = 1/(157017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241963287 / 1000000000) (-120981643 / 500000000) (Real.log (157017 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (195020581 / 1000000000) ≤ -Real.log (125000 / 151917) ∧
    -Real.log (125000 / 151917) ≤ (97510291 / 500000000) := by
  have h := checkLog_sound (w := (26917 / 276917)) (n := 12)
    (lo := (195020581 / 1000000000)) (hi := (97510291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151917 / 125000) = 1/(125000 / 151917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (195020581 / 1000000000) (97510291 / 500000000) (Real.log (151917 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (151917 / 125000) = -Real.log (125000 / 151917) := by
    rw [show ((151917 / 125000) : ℝ) = ((125000 / 151917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (121249839 / 500000000) ≤ -Real.log (98083 / 125000) ∧
    -Real.log (98083 / 125000) ≤ (242499679 / 1000000000) := by
  have h := checkLog_sound (w := (26917 / 223083)) (n := 12)
    (lo := (121249839 / 500000000)) (hi := (242499679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98083) = 1/(98083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-242499679 / 1000000000) (-121249839 / 500000000) (Real.log (98083 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3579511 / 25000000) ≤ -Real.log (500000 / 576969) ∧
    -Real.log (500000 / 576969) ≤ (143180441 / 1000000000) := by
  have h := checkLog_sound (w := (76969 / 1076969)) (n := 12)
    (lo := (3579511 / 25000000)) (hi := (143180441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576969 / 500000) = 1/(500000 / 576969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3579511 / 25000000) (143180441 / 1000000000) (Real.log (576969 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576969 / 500000) = -Real.log (500000 / 576969) := by
    rw [show ((576969 / 500000) : ℝ) = ((500000 / 576969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41790659 / 250000000) ≤ -Real.log (423031 / 500000) ∧
    -Real.log (423031 / 500000) ≤ (167162637 / 1000000000) := by
  have h := checkLog_sound (w := (76969 / 923031)) (n := 12)
    (lo := (41790659 / 250000000)) (hi := (167162637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423031) = 1/(423031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-167162637 / 1000000000) (-41790659 / 250000000) (Real.log (423031 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143448183 / 1000000000) ≤ -Real.log (1000000 / 1154247) ∧
    -Real.log (1000000 / 1154247) ≤ (17931023 / 125000000) := by
  have h := checkLog_sound (w := (154247 / 2154247)) (n := 12)
    (lo := (143448183 / 1000000000)) (hi := (17931023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1154247 / 1000000) = 1/(1000000 / 1154247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143448183 / 1000000000) (17931023 / 125000000) (Real.log (1154247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1154247 / 1000000) = -Real.log (1000000 / 1154247) := by
    rw [show ((1154247 / 1000000) : ℝ) = ((1000000 / 1154247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41881981 / 250000000) ≤ -Real.log (845753 / 1000000) ∧
    -Real.log (845753 / 1000000) ≤ (6701117 / 40000000) := by
  have h := checkLog_sound (w := (154247 / 1845753)) (n := 12)
    (lo := (41881981 / 250000000)) (hi := (6701117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 845753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 845753) = 1/(845753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6701117 / 40000000) (-41881981 / 250000000) (Real.log (845753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78131783 / 125000000) ≤ -Real.log (500000000000 / 934173669467) ∧
    -Real.log (500000000000 / 934173669467) ≤ (125010853 / 200000000) := by
  have h := checkLog_sound (w := (434173669467 / 1434173669467)) (n := 12)
    (lo := (78131783 / 125000000)) (hi := (125010853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934173669467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934173669467 / 500000000000) = 1/(500000000000 / 934173669467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78131783 / 125000000) (125010853 / 200000000) (Real.log (934173669467 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (934173669467 / 500000000000) = -Real.log (500000000000 / 934173669467) := by
    rw [show ((934173669467 / 500000000000) : ℝ) = ((500000000000 / 934173669467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (626344627 / 1000000000) ≤ -Real.log (500000000000 / 935379871041) ∧
    -Real.log (500000000000 / 935379871041) ≤ (156586157 / 250000000) := by
  have h := checkLog_sound (w := (435379871041 / 1435379871041)) (n := 12)
    (lo := (626344627 / 1000000000)) (hi := (156586157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935379871041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935379871041 / 500000000000) = 1/(500000000000 / 935379871041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (626344627 / 1000000000) (156586157 / 250000000) (Real.log (935379871041 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (935379871041 / 500000000000) = -Real.log (500000000000 / 935379871041) := by
    rw [show ((935379871041 / 500000000000) : ℝ) = ((500000000000 / 935379871041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (218318701 / 500000000) ≤ -Real.log (250000000000 / 386873714311) ∧
    -Real.log (250000000000 / 386873714311) ≤ (436637403 / 1000000000) := by
  have h := checkLog_sound (w := (136873714311 / 636873714311)) (n := 12)
    (lo := (218318701 / 500000000)) (hi := (436637403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386873714311 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386873714311 / 250000000000) = 1/(250000000000 / 386873714311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218318701 / 500000000) (436637403 / 1000000000) (Real.log (386873714311 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (386873714311 / 250000000000) = -Real.log (250000000000 / 386873714311) := by
    rw [show ((386873714311 / 250000000000) : ℝ) = ((250000000000 / 386873714311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (21876013 / 50000000) ≤ -Real.log (125000000000 / 193607709797) ∧
    -Real.log (125000000000 / 193607709797) ≤ (437520261 / 1000000000) := by
  have h := checkLog_sound (w := (68607709797 / 318607709797)) (n := 12)
    (lo := (21876013 / 50000000)) (hi := (437520261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193607709797 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193607709797 / 125000000000) = 1/(125000000000 / 193607709797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (21876013 / 50000000) (437520261 / 1000000000) (Real.log (193607709797 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (193607709797 / 125000000000) = -Real.log (125000000000 / 193607709797) := by
    rw [show ((193607709797 / 125000000000) : ℝ) = ((125000000000 / 193607709797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (77585769 / 250000000) ≤ -Real.log (100000000000 / 136389295347) ∧
    -Real.log (100000000000 / 136389295347) ≤ (310343077 / 1000000000) := by
  have h := checkLog_sound (w := (36389295347 / 236389295347)) (n := 12)
    (lo := (77585769 / 250000000)) (hi := (310343077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136389295347 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136389295347 / 100000000000) = 1/(100000000000 / 136389295347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77585769 / 250000000) (310343077 / 1000000000) (Real.log (136389295347 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (136389295347 / 100000000000) = -Real.log (100000000000 / 136389295347) := by
    rw [show ((136389295347 / 100000000000) : ℝ) = ((100000000000 / 136389295347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310976107 / 1000000000) ≤ -Real.log (500000000000 / 682378306669) ∧
    -Real.log (500000000000 / 682378306669) ≤ (77744027 / 250000000) := by
  have h := checkLog_sound (w := (182378306669 / 1182378306669)) (n := 12)
    (lo := (310976107 / 1000000000)) (hi := (77744027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682378306669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682378306669 / 500000000000) = 1/(500000000000 / 682378306669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310976107 / 1000000000) (77744027 / 250000000) (Real.log (682378306669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (682378306669 / 500000000000) = -Real.log (500000000000 / 682378306669) := by
    rw [show ((682378306669 / 500000000000) : ℝ) = ((500000000000 / 682378306669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1203987 / 50000000) ≤ -Real.log (976207862991 / 1000000000000) ∧
    -Real.log (976207862991 / 1000000000000) ≤ (24079741 / 1000000000) := by
  have h := checkLog_sound (w := (23792137009 / 1976207862991)) (n := 12)
    (lo := (1203987 / 50000000)) (hi := (24079741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976207862991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976207862991) = 1/(976207862991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24079741 / 1000000000) (-1203987 / 50000000) (Real.log (976207862991 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4796439 / 200000000) ≤ -Real.log (244075773039 / 250000000000) ∧
    -Real.log (244075773039 / 250000000000) ≤ (5995549 / 250000000) := by
  have h := checkLog_sound (w := (5924226961 / 494075773039)) (n := 12)
    (lo := (4796439 / 200000000)) (hi := (5995549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244075773039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244075773039) = 1/(244075773039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5995549 / 250000000) (-4796439 / 200000000) (Real.log (244075773039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell090
