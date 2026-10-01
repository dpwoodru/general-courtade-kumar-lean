import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0089
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

theorem reflection_log_1_neg : (673492393 / 1000000000) ≤ -Real.log (51200 / 100407) ∧
    -Real.log (51200 / 100407) ≤ (336746197 / 500000000) := by
  have h := checkLog_sound (w := (49207 / 151607)) (n := 12)
    (lo := (673492393 / 1000000000)) (hi := (336746197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100407 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100407 / 51200) = 1/(51200 / 100407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (673492393 / 1000000000) (336746197 / 500000000) (Real.log (100407 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100407 / 51200) = -Real.log (51200 / 100407) := by
    rw [show ((100407 / 51200) : ℝ) = ((51200 / 100407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (405762311 / 125000000) ≤ -Real.log (1993 / 51200) ∧
    -Real.log (1993 / 51200) ≤ (3246098493 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1993) = 1/(1993 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3246098493 / 1000000000) (-405762311 / 125000000) (Real.log (1993 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336651573 / 500000000) ≤ -Real.log (12800 / 25097) ∧
    -Real.log (12800 / 25097) ≤ (673303147 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 37897)) (n := 12)
    (lo := (336651573 / 500000000)) (hi := (673303147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25097 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25097 / 12800) = 1/(12800 / 25097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336651573 / 500000000) (673303147 / 1000000000) (Real.log (25097 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25097 / 12800) = -Real.log (12800 / 25097) := by
    rw [show ((25097 / 12800) : ℝ) = ((12800 / 25097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3236610277 / 1000000000) ≤ -Real.log (503 / 12800) ∧
    -Real.log (503 / 12800) ≤ (1618305141 / 500000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 503) = 1/(503 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1618305141 / 500000000) (-3236610277 / 1000000000) (Real.log (503 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (326721769 / 500000000) ≤ -Real.log (25600 / 49207) ∧
    -Real.log (25600 / 49207) ≤ (653443539 / 1000000000) := by
  have h := checkLog_sound (w := (23607 / 74807)) (n := 12)
    (lo := (326721769 / 500000000)) (hi := (653443539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49207 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49207 / 25600) = 1/(25600 / 49207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (326721769 / 500000000) (653443539 / 1000000000) (Real.log (49207 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49207 / 25600) = -Real.log (25600 / 49207) := by
    rw [show ((49207 / 25600) : ℝ) = ((25600 / 49207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638237827 / 250000000) ≤ -Real.log (1993 / 25600) ∧
    -Real.log (1993 / 25600) ≤ (159559457 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1993) = 1/(1993 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159559457 / 62500000) (-638237827 / 250000000) (Real.log (1993 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653057339 / 1000000000) ≤ -Real.log (6400 / 12297) ∧
    -Real.log (6400 / 12297) ≤ (32652867 / 50000000) := by
  have h := checkLog_sound (w := (5897 / 18697)) (n := 12)
    (lo := (653057339 / 1000000000)) (hi := (32652867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 6400) = 1/(6400 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653057339 / 1000000000) (32652867 / 50000000) (Real.log (12297 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12297 / 6400) = -Real.log (6400 / 12297) := by
    rw [show ((12297 / 6400) : ℝ) = ((6400 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2543463097 / 1000000000) ≤ -Real.log (503 / 6400) ∧
    -Real.log (503 / 6400) ≤ (2543463101 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 503) = 1/(503 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2543463101 / 1000000000) (-2543463097 / 1000000000) (Real.log (503 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (338407771 / 500000000) ≤ -Real.log (500000 / 983801) ∧
    -Real.log (500000 / 983801) ≤ (676815543 / 1000000000) := by
  have h := checkLog_sound (w := (483801 / 1483801)) (n := 12)
    (lo := (338407771 / 500000000)) (hi := (676815543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983801 / 500000) = 1/(500000 / 983801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (338407771 / 500000000) (676815543 / 1000000000) (Real.log (983801 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (983801 / 500000) = -Real.log (500000 / 983801) := by
    rw [show ((983801 / 500000) : ℝ) = ((500000 / 983801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (428707323 / 125000000) ≤ -Real.log (16199 / 500000) ∧
    -Real.log (16199 / 500000) ≤ (3429658589 / 1000000000) := by
  have h := checkLog_sound (w := (15051 / 47449)) (n := 12)
    (lo := (82133733 / 125000000)) (hi := (131413973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16199) = 1/(16199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3429658589 / 1000000000) (-428707323 / 125000000) (Real.log (16199 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676962919 / 1000000000) ≤ -Real.log (250000 / 491973) ∧
    -Real.log (250000 / 491973) ≤ (16924073 / 25000000) := by
  have h := checkLog_sound (w := (241973 / 741973)) (n := 12)
    (lo := (676962919 / 1000000000)) (hi := (16924073 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491973 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491973 / 250000) = 1/(250000 / 491973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676962919 / 1000000000) (16924073 / 25000000) (Real.log (491973 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (491973 / 250000) = -Real.log (250000 / 491973) := by
    rw [show ((491973 / 250000) : ℝ) = ((250000 / 491973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (429831257 / 125000000) ≤ -Real.log (8027 / 250000) ∧
    -Real.log (8027 / 250000) ≤ (3438650061 / 1000000000) := by
  have h := checkLog_sound (w := (3799 / 11826)) (n := 12)
    (lo := (83257667 / 125000000)) (hi := (666061337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8027) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8027) = 1/(8027 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3438650061 / 1000000000) (-429831257 / 125000000) (Real.log (8027 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676674243 / 1000000000) ≤ -Real.log (250000 / 491831) ∧
    -Real.log (250000 / 491831) ≤ (169168561 / 250000000) := by
  have h := checkLog_sound (w := (241831 / 741831)) (n := 12)
    (lo := (676674243 / 1000000000)) (hi := (169168561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491831 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491831 / 250000) = 1/(250000 / 491831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676674243 / 1000000000) (169168561 / 250000000) (Real.log (491831 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (491831 / 250000) = -Real.log (250000 / 491831) := by
    rw [show ((491831 / 250000) : ℝ) = ((250000 / 491831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3421114413 / 1000000000) ≤ -Real.log (8169 / 250000) ∧
    -Real.log (8169 / 250000) ≤ (1710557209 / 500000000) := by
  have h := checkLog_sound (w := (3728 / 11897)) (n := 12)
    (lo := (648525693 / 1000000000)) (hi := (324262847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8169) = 1/(8169 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1710557209 / 500000000) (-3421114413 / 1000000000) (Real.log (8169 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338412091 / 500000000) ≤ -Real.log (1000000 / 1967619) ∧
    -Real.log (1000000 / 1967619) ≤ (676824183 / 1000000000) := by
  have h := checkLog_sound (w := (967619 / 2967619)) (n := 12)
    (lo := (338412091 / 500000000)) (hi := (676824183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967619 / 1000000) = 1/(1000000 / 1967619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338412091 / 500000000) (676824183 / 1000000000) (Real.log (1967619 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1967619 / 1000000) = -Real.log (1000000 / 1967619) := by
    rw [show ((1967619 / 1000000) : ℝ) = ((1000000 / 1967619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (686036689 / 200000000) ≤ -Real.log (32381 / 1000000) ∧
    -Real.log (32381 / 1000000) ≤ (68603669 / 20000000) := by
  have h := checkLog_sound (w := (30119 / 94881)) (n := 12)
    (lo := (26303789 / 40000000)) (hi := (328797363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32381) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32381) = 1/(32381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68603669 / 20000000) (-686036689 / 200000000) (Real.log (32381 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2053237063 / 500000000) ≤ -Real.log (250000000000 / 15183051422927) ∧
    -Real.log (250000000000 / 15183051422927) ≤ (1026618533 / 250000000) := by
  have h := checkLog_sound (w := (7183051422927 / 23183051422927)) (n := 12)
    (lo := (320369113 / 500000000)) (hi := (640738227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15183051422927 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15183051422927 / 8000000000000) = 1/(250000000000 / 15183051422927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2053237063 / 500000000) (1026618533 / 250000000) (Real.log (15183051422927 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15183051422927 / 250000000000) = -Real.log (250000000000 / 15183051422927) := by
    rw [show ((15183051422927 / 250000000000) : ℝ) = ((250000000000 / 15183051422927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2057806487 / 500000000) ≤ -Real.log (250000000000 / 15322443004859) ∧
    -Real.log (250000000000 / 15322443004859) ≤ (205780649 / 50000000) := by
  have h := checkLog_sound (w := (7322443004859 / 23322443004859)) (n := 12)
    (lo := (324938537 / 500000000)) (hi := (25995083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15322443004859 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15322443004859 / 8000000000000) = 1/(250000000000 / 15322443004859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2057806487 / 500000000) (205780649 / 50000000) (Real.log (15322443004859 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15322443004859 / 250000000000) = -Real.log (250000000000 / 15322443004859) := by
    rw [show ((15322443004859 / 250000000000) : ℝ) = ((250000000000 / 15322443004859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256111791 / 62500000) ≤ -Real.log (500000000000 / 30103501040519) ∧
    -Real.log (500000000000 / 30103501040519) ≤ (2048894331 / 500000000) := by
  have h := checkLog_sound (w := (14103501040519 / 46103501040519)) (n := 12)
    (lo := (158013189 / 250000000)) (hi := (632052757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30103501040519 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30103501040519 / 16000000000000) = 1/(500000000000 / 30103501040519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (256111791 / 62500000) (2048894331 / 500000000) (Real.log (30103501040519 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (30103501040519 / 500000000000) = -Real.log (500000000000 / 30103501040519) := by
    rw [show ((30103501040519 / 500000000000) : ℝ) = ((500000000000 / 30103501040519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4107007627 / 1000000000) ≤ -Real.log (500000000000 / 30382307526019) ∧
    -Real.log (500000000000 / 30382307526019) ≤ (4107007633 / 1000000000) := by
  have h := checkLog_sound (w := (14382307526019 / 46382307526019)) (n := 12)
    (lo := (641271727 / 1000000000)) (hi := (40079483 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30382307526019 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30382307526019 / 16000000000000) = 1/(500000000000 / 30382307526019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4107007627 / 1000000000) (4107007633 / 1000000000) (Real.log (30382307526019 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30382307526019 / 500000000000) = -Real.log (500000000000 / 30382307526019) := by
    rw [show ((30382307526019 / 500000000000) : ℝ) = ((500000000000 / 30382307526019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0089
