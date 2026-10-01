import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0188
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

theorem reflection_log_1_neg : (271040459 / 1000000000) ≤ -Real.log (2560 / 3357) ∧
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


theorem reflection_log_1 : Bounds (271040459 / 1000000000) (13552023 / 50000000) (Real.log (3357 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3357 / 2560) = -Real.log (2560 / 3357) := by
    rw [show ((3357 / 2560) : ℝ) = ((2560 / 3357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74598071 / 200000000) ≤ -Real.log (1763 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-93247589 / 250000000) (-74598071 / 200000000) (Real.log (1763 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67648383 / 250000000) ≤ -Real.log (5120 / 6711) ∧
    -Real.log (5120 / 6711) ≤ (270593533 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 11831)) (n := 12)
    (lo := (67648383 / 250000000)) (hi := (270593533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6711 / 5120) = 1/(5120 / 6711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67648383 / 250000000) (270593533 / 1000000000) (Real.log (6711 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6711 / 5120) = -Real.log (5120 / 6711) := by
    rw [show ((6711 / 5120) : ℝ) = ((5120 / 6711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (186069947 / 500000000) ≤ -Real.log (3529 / 5120) ∧
    -Real.log (3529 / 5120) ≤ (74427979 / 200000000) := by
  have h := checkLog_sound (w := (1591 / 8649)) (n := 12)
    (lo := (186069947 / 500000000)) (hi := (74427979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3529) = 1/(3529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-74427979 / 200000000) (-186069947 / 500000000) (Real.log (3529 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242032233 / 500000000) ≤ -Real.log (1280 / 2077) ∧
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


theorem reflection_log_5 : Bounds (242032233 / 500000000) (484064467 / 1000000000) (Real.log (2077 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2077 / 1280) = -Real.log (1280 / 2077) := by
    rw [show ((2077 / 1280) : ℝ) = ((1280 / 2077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (487299351 / 500000000) ≤ -Real.log (483 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-60912419 / 62500000) (-487299351 / 500000000) (Real.log (483 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48334201 / 100000000) ≤ -Real.log (2560 / 4151) ∧
    -Real.log (2560 / 4151) ≤ (483342011 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 6711)) (n := 12)
    (lo := (48334201 / 100000000)) (hi := (483342011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4151 / 2560) = 1/(2560 / 4151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48334201 / 100000000) (483342011 / 1000000000) (Real.log (4151 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4151 / 2560) = -Real.log (2560 / 4151) := by
    rw [show ((4151 / 2560) : ℝ) = ((2560 / 4151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (38859917 / 40000000) ≤ -Real.log (969 / 2560) ∧
    -Real.log (969 / 2560) ≤ (971497927 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 2249)) (n := 12)
    (lo := (55670149 / 200000000)) (hi := (139175373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 969) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 969) = 1/(969 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-971497927 / 1000000000) (-38859917 / 40000000) (Real.log (969 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3701681 / 10000000) ≤ -Real.log (500000 / 723989) ∧
    -Real.log (500000 / 723989) ≤ (370168101 / 1000000000) := by
  have h := checkLog_sound (w := (223989 / 1223989)) (n := 12)
    (lo := (3701681 / 10000000)) (hi := (370168101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723989 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723989 / 500000) = 1/(500000 / 723989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3701681 / 10000000) (370168101 / 1000000000) (Real.log (723989 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (723989 / 500000) = -Real.log (500000 / 723989) := by
    rw [show ((723989 / 500000) : ℝ) = ((500000 / 723989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (297083689 / 500000000) ≤ -Real.log (276011 / 500000) ∧
    -Real.log (276011 / 500000) ≤ (594167379 / 1000000000) := by
  have h := checkLog_sound (w := (223989 / 776011)) (n := 12)
    (lo := (297083689 / 500000000)) (hi := (594167379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276011) = 1/(276011 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-594167379 / 1000000000) (-297083689 / 500000000) (Real.log (276011 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37077911 / 100000000) ≤ -Real.log (1000000 / 1448863) ∧
    -Real.log (1000000 / 1448863) ≤ (370779111 / 1000000000) := by
  have h := checkLog_sound (w := (448863 / 2448863)) (n := 12)
    (lo := (37077911 / 100000000)) (hi := (370779111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1448863 / 1000000) = 1/(1000000 / 1448863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37077911 / 100000000) (370779111 / 1000000000) (Real.log (1448863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1448863 / 1000000) = -Real.log (1000000 / 1448863) := by
    rw [show ((1448863 / 1000000) : ℝ) = ((1000000 / 1448863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (595771861 / 1000000000) ≤ -Real.log (551137 / 1000000) ∧
    -Real.log (551137 / 1000000) ≤ (297885931 / 500000000) := by
  have h := checkLog_sound (w := (448863 / 1551137)) (n := 12)
    (lo := (595771861 / 1000000000)) (hi := (297885931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 551137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 551137) = 1/(551137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-297885931 / 500000000) (-595771861 / 1000000000) (Real.log (551137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144598587 / 500000000) ≤ -Real.log (200000 / 267071) ∧
    -Real.log (200000 / 267071) ≤ (11567887 / 40000000) := by
  have h := checkLog_sound (w := (67071 / 467071)) (n := 12)
    (lo := (144598587 / 500000000)) (hi := (11567887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267071 / 200000) = 1/(200000 / 267071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144598587 / 500000000) (11567887 / 40000000) (Real.log (267071 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (267071 / 200000) = -Real.log (200000 / 267071) := by
    rw [show ((267071 / 200000) : ℝ) = ((200000 / 267071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (81700443 / 200000000) ≤ -Real.log (132929 / 200000) ∧
    -Real.log (132929 / 200000) ≤ (51062777 / 125000000) := by
  have h := checkLog_sound (w := (67071 / 332929)) (n := 12)
    (lo := (81700443 / 200000000)) (hi := (51062777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132929) = 1/(132929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-51062777 / 125000000) (-81700443 / 200000000) (Real.log (132929 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14487559 / 50000000) ≤ -Real.log (200000 / 267219) ∧
    -Real.log (200000 / 267219) ≤ (289751181 / 1000000000) := by
  have h := checkLog_sound (w := (67219 / 467219)) (n := 12)
    (lo := (14487559 / 50000000)) (hi := (289751181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267219 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267219 / 200000) = 1/(200000 / 267219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14487559 / 50000000) (289751181 / 1000000000) (Real.log (267219 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (267219 / 200000) = -Real.log (200000 / 267219) := by
    rw [show ((267219 / 200000) : ℝ) = ((200000 / 267219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102404053 / 250000000) ≤ -Real.log (132781 / 200000) ∧
    -Real.log (132781 / 200000) ≤ (409616213 / 1000000000) := by
  have h := checkLog_sound (w := (67219 / 332781)) (n := 12)
    (lo := (102404053 / 250000000)) (hi := (409616213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132781) = 1/(132781 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-409616213 / 1000000000) (-102404053 / 250000000) (Real.log (132781 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (482167739 / 500000000) ≤ -Real.log (500000000000 / 1311522004557) ∧
    -Real.log (500000000000 / 1311522004557) ≤ (24108387 / 25000000) := by
  have h := checkLog_sound (w := (311522004557 / 2311522004557)) (n := 12)
    (lo := (135594149 / 500000000)) (hi := (271188299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311522004557 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1311522004557 / 1000000000000) = 1/(500000000000 / 1311522004557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (482167739 / 500000000) (24108387 / 25000000) (Real.log (1311522004557 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1311522004557 / 500000000000) = -Real.log (500000000000 / 1311522004557) := by
    rw [show ((1311522004557 / 500000000000) : ℝ) = ((500000000000 / 1311522004557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (241637743 / 250000000) ≤ -Real.log (250000000000 / 657215447339) ∧
    -Real.log (250000000000 / 657215447339) ≤ (483275487 / 500000000) := by
  have h := checkLog_sound (w := (157215447339 / 1157215447339)) (n := 12)
    (lo := (17087737 / 62500000)) (hi := (273403793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657215447339 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(657215447339 / 500000000000) = 1/(250000000000 / 657215447339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (241637743 / 250000000) (483275487 / 500000000) (Real.log (657215447339 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (657215447339 / 250000000000) = -Real.log (250000000000 / 657215447339) := by
    rw [show ((657215447339 / 250000000000) : ℝ) = ((250000000000 / 657215447339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (174424847 / 250000000) ≤ -Real.log (250000000000 / 502281293021) ∧
    -Real.log (250000000000 / 502281293021) ≤ (69769939 / 100000000) := by
  have h := checkLog_sound (w := (2281293021 / 1002281293021)) (n := 12)
    (lo := (284513 / 62500000)) (hi := (4552209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502281293021 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(502281293021 / 500000000000) = 1/(250000000000 / 502281293021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (174424847 / 250000000) (69769939 / 100000000) (Real.log (502281293021 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (502281293021 / 250000000000) = -Real.log (250000000000 / 502281293021) := by
    rw [show ((502281293021 / 250000000000) : ℝ) = ((250000000000 / 502281293021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (699367391 / 1000000000) ≤ -Real.log (500000000000 / 1006239597533) ∧
    -Real.log (500000000000 / 1006239597533) ≤ (699367393 / 1000000000) := by
  have h := checkLog_sound (w := (6239597533 / 2006239597533)) (n := 12)
    (lo := (6220211 / 1000000000)) (hi := (1555053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006239597533 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006239597533 / 1000000000000) = 1/(500000000000 / 1006239597533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (699367391 / 1000000000) (699367393 / 1000000000) (Real.log (1006239597533 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1006239597533 / 500000000000) = -Real.log (500000000000 / 1006239597533) := by
    rw [show ((1006239597533 / 500000000000) : ℝ) = ((500000000000 / 1006239597533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0188
