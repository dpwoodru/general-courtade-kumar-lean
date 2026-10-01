import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0371
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

theorem reflection_log_1_neg : (20715707 / 100000000) ≤ -Real.log (10240 / 12597) ∧
    -Real.log (10240 / 12597) ≤ (207157071 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 22837)) (n := 12)
    (lo := (20715707 / 100000000)) (hi := (207157071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12597 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12597 / 10240) = 1/(10240 / 12597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20715707 / 100000000) (207157071 / 1000000000) (Real.log (12597 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12597 / 10240) = -Real.log (10240 / 12597) := by
    rw [show ((12597 / 10240) : ℝ) = ((10240 / 12597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (261593077 / 1000000000) ≤ -Real.log (7883 / 10240) ∧
    -Real.log (7883 / 10240) ≤ (130796539 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 18123)) (n := 12)
    (lo := (261593077 / 1000000000)) (hi := (130796539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7883) = 1/(7883 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-130796539 / 500000000) (-261593077 / 1000000000) (Real.log (7883 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20691889 / 100000000) ≤ -Real.log (5120 / 6297) ∧
    -Real.log (5120 / 6297) ≤ (206918891 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 11417)) (n := 12)
    (lo := (20691889 / 100000000)) (hi := (206918891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6297 / 5120) = 1/(5120 / 6297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20691889 / 100000000) (206918891 / 1000000000) (Real.log (6297 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6297 / 5120) = -Real.log (5120 / 6297) := by
    rw [show ((6297 / 5120) : ℝ) = ((5120 / 6297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32651573 / 125000000) ≤ -Real.log (3943 / 5120) ∧
    -Real.log (3943 / 5120) ≤ (52242517 / 200000000) := by
  have h := checkLog_sound (w := (1177 / 9063)) (n := 12)
    (lo := (32651573 / 125000000)) (hi := (52242517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3943) = 1/(3943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-52242517 / 200000000) (-32651573 / 125000000) (Real.log (3943 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189338601 / 500000000) ≤ -Real.log (5120 / 7477) ∧
    -Real.log (5120 / 7477) ≤ (378677203 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 12597)) (n := 12)
    (lo := (189338601 / 500000000)) (hi := (378677203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7477 / 5120) = 1/(5120 / 7477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189338601 / 500000000) (378677203 / 1000000000) (Real.log (7477 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7477 / 5120) = -Real.log (5120 / 7477) := by
    rw [show ((7477 / 5120) : ℝ) = ((5120 / 7477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (616837393 / 1000000000) ≤ -Real.log (2763 / 5120) ∧
    -Real.log (2763 / 5120) ≤ (308418697 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 7883)) (n := 12)
    (lo := (616837393 / 1000000000)) (hi := (308418697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2763) = 1/(2763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-308418697 / 500000000) (-616837393 / 1000000000) (Real.log (2763 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (94568973 / 250000000) ≤ -Real.log (2560 / 3737) ∧
    -Real.log (2560 / 3737) ≤ (378275893 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 6297)) (n := 12)
    (lo := (94568973 / 250000000)) (hi := (378275893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3737 / 2560) = 1/(2560 / 3737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (94568973 / 250000000) (378275893 / 1000000000) (Real.log (3737 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3737 / 2560) = -Real.log (2560 / 3737) := by
    rw [show ((3737 / 2560) : ℝ) = ((2560 / 3737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (123150441 / 200000000) ≤ -Real.log (1383 / 2560) ∧
    -Real.log (1383 / 2560) ≤ (307876103 / 500000000) := by
  have h := checkLog_sound (w := (1177 / 3943)) (n := 12)
    (lo := (123150441 / 200000000)) (hi := (307876103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1383) = 1/(1383 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307876103 / 500000000) (-123150441 / 200000000) (Real.log (1383 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141931143 / 500000000) ≤ -Real.log (4000 / 5313) ∧
    -Real.log (4000 / 5313) ≤ (283862287 / 1000000000) := by
  have h := checkLog_sound (w := (1313 / 9313)) (n := 12)
    (lo := (141931143 / 500000000)) (hi := (283862287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5313 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5313 / 4000) = 1/(4000 / 5313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141931143 / 500000000) (283862287 / 1000000000) (Real.log (5313 / 4000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (5313 / 4000) = -Real.log (4000 / 5313) := by
    rw [show ((5313 / 4000) : ℝ) = ((4000 / 5313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (397869031 / 1000000000) ≤ -Real.log (2687 / 4000) ∧
    -Real.log (2687 / 4000) ≤ (49733629 / 125000000) := by
  have h := checkLog_sound (w := (1313 / 6687)) (n := 12)
    (lo := (397869031 / 1000000000)) (hi := (49733629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2687) = 1/(2687 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49733629 / 125000000) (-397869031 / 1000000000) (Real.log (2687 / 4000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142092231 / 500000000) ≤ -Real.log (500000 / 664339) ∧
    -Real.log (500000 / 664339) ≤ (284184463 / 1000000000) := by
  have h := checkLog_sound (w := (164339 / 1164339)) (n := 12)
    (lo := (142092231 / 500000000)) (hi := (284184463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664339 / 500000) = 1/(500000 / 664339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142092231 / 500000000) (284184463 / 1000000000) (Real.log (664339 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (664339 / 500000) = -Real.log (500000 / 664339) := by
    rw [show ((664339 / 500000) : ℝ) = ((500000 / 664339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (49813297 / 125000000) ≤ -Real.log (335661 / 500000) ∧
    -Real.log (335661 / 500000) ≤ (398506377 / 1000000000) := by
  have h := checkLog_sound (w := (164339 / 835661)) (n := 12)
    (lo := (49813297 / 125000000)) (hi := (398506377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335661) = 1/(335661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-398506377 / 1000000000) (-49813297 / 125000000) (Real.log (335661 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (107249951 / 500000000) ≤ -Real.log (500000 / 619621) ∧
    -Real.log (500000 / 619621) ≤ (214499903 / 1000000000) := by
  have h := checkLog_sound (w := (119621 / 1119621)) (n := 12)
    (lo := (107249951 / 500000000)) (hi := (214499903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619621 / 500000) = 1/(500000 / 619621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (107249951 / 500000000) (214499903 / 1000000000) (Real.log (619621 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (619621 / 500000) = -Real.log (500000 / 619621) := by
    rw [show ((619621 / 500000) : ℝ) = ((500000 / 619621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136719987 / 500000000) ≤ -Real.log (380379 / 500000) ∧
    -Real.log (380379 / 500000) ≤ (10937599 / 40000000) := by
  have h := checkLog_sound (w := (119621 / 880379)) (n := 12)
    (lo := (136719987 / 500000000)) (hi := (10937599 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380379) = 1/(380379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10937599 / 40000000) (-136719987 / 500000000) (Real.log (380379 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53691943 / 250000000) ≤ -Real.log (500000 / 619787) ∧
    -Real.log (500000 / 619787) ≤ (214767773 / 1000000000) := by
  have h := checkLog_sound (w := (119787 / 1119787)) (n := 12)
    (lo := (53691943 / 250000000)) (hi := (214767773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619787 / 500000) = 1/(500000 / 619787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53691943 / 250000000) (214767773 / 1000000000) (Real.log (619787 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (619787 / 500000) = -Real.log (500000 / 619787) := by
    rw [show ((619787 / 500000) : ℝ) = ((500000 / 619787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (68469119 / 250000000) ≤ -Real.log (380213 / 500000) ∧
    -Real.log (380213 / 500000) ≤ (273876477 / 1000000000) := by
  have h := checkLog_sound (w := (119787 / 880213)) (n := 12)
    (lo := (68469119 / 250000000)) (hi := (273876477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380213) = 1/(380213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273876477 / 1000000000) (-68469119 / 250000000) (Real.log (380213 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (681731317 / 1000000000) ≤ -Real.log (250000000000 / 494324525493) ∧
    -Real.log (250000000000 / 494324525493) ≤ (340865659 / 500000000) := by
  have h := checkLog_sound (w := (244324525493 / 744324525493)) (n := 12)
    (lo := (681731317 / 1000000000)) (hi := (340865659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494324525493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494324525493 / 250000000000) = 1/(250000000000 / 494324525493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (681731317 / 1000000000) (340865659 / 500000000) (Real.log (494324525493 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (494324525493 / 250000000000) = -Real.log (250000000000 / 494324525493) := by
    rw [show ((494324525493 / 250000000000) : ℝ) = ((250000000000 / 494324525493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (682690839 / 1000000000) ≤ -Real.log (100000000000 / 197919627243) ∧
    -Real.log (100000000000 / 197919627243) ≤ (17067271 / 25000000) := by
  have h := checkLog_sound (w := (97919627243 / 297919627243)) (n := 12)
    (lo := (682690839 / 1000000000)) (hi := (17067271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197919627243 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197919627243 / 100000000000) = 1/(100000000000 / 197919627243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (682690839 / 1000000000) (17067271 / 25000000) (Real.log (197919627243 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (197919627243 / 100000000000) = -Real.log (100000000000 / 197919627243) := by
    rw [show ((197919627243 / 100000000000) : ℝ) = ((100000000000 / 197919627243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (121984969 / 250000000) ≤ -Real.log (500000000000 / 814478454383) ∧
    -Real.log (500000000000 / 814478454383) ≤ (487939877 / 1000000000) := by
  have h := checkLog_sound (w := (314478454383 / 1314478454383)) (n := 12)
    (lo := (121984969 / 250000000)) (hi := (487939877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814478454383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814478454383 / 500000000000) = 1/(500000000000 / 814478454383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (121984969 / 250000000) (487939877 / 1000000000) (Real.log (814478454383 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (814478454383 / 500000000000) = -Real.log (500000000000 / 814478454383) := by
    rw [show ((814478454383 / 500000000000) : ℝ) = ((500000000000 / 814478454383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (61080531 / 125000000) ≤ -Real.log (100000000000 / 163010470447) ∧
    -Real.log (100000000000 / 163010470447) ≤ (488644249 / 1000000000) := by
  have h := checkLog_sound (w := (63010470447 / 263010470447)) (n := 12)
    (lo := (61080531 / 125000000)) (hi := (488644249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163010470447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163010470447 / 100000000000) = 1/(100000000000 / 163010470447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (61080531 / 125000000) (488644249 / 1000000000) (Real.log (163010470447 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (163010470447 / 100000000000) = -Real.log (100000000000 / 163010470447) := by
    rw [show ((163010470447 / 100000000000) : ℝ) = ((100000000000 / 163010470447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0371
