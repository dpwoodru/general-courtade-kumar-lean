import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0189
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

theorem reflection_log_1_neg : (67648383 / 250000000) ≤ -Real.log (5120 / 6711) ∧
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


theorem reflection_log_1 : Bounds (67648383 / 250000000) (270593533 / 1000000000) (Real.log (6711 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6711 / 5120) = -Real.log (5120 / 6711) := by
    rw [show ((6711 / 5120) : ℝ) = ((5120 / 6711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (186069947 / 500000000) ≤ -Real.log (3529 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-74427979 / 200000000) (-186069947 / 500000000) (Real.log (3529 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67536601 / 250000000) ≤ -Real.log (1280 / 1677) ∧
    -Real.log (1280 / 1677) ≤ (54029281 / 200000000) := by
  have h := checkLog_sound (w := (397 / 2957)) (n := 12)
    (lo := (67536601 / 250000000)) (hi := (54029281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1280) = 1/(1280 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67536601 / 250000000) (54029281 / 200000000) (Real.log (1677 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1677 / 1280) = -Real.log (1280 / 1677) := by
    rw [show ((1677 / 1280) : ℝ) = ((1280 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92822539 / 250000000) ≤ -Real.log (883 / 1280) ∧
    -Real.log (883 / 1280) ≤ (371290157 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2163)) (n := 12)
    (lo := (92822539 / 250000000)) (hi := (371290157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 883) = 1/(883 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-371290157 / 1000000000) (-92822539 / 250000000) (Real.log (883 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48334201 / 100000000) ≤ -Real.log (2560 / 4151) ∧
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


theorem reflection_log_5 : Bounds (48334201 / 100000000) (483342011 / 1000000000) (Real.log (4151 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4151 / 2560) = -Real.log (2560 / 4151) := by
    rw [show ((4151 / 2560) : ℝ) = ((2560 / 4151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (38859917 / 40000000) ≤ -Real.log (969 / 2560) ∧
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


theorem reflection_log_6 : Bounds (-971497927 / 1000000000) (-38859917 / 40000000) (Real.log (969 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (482619031 / 1000000000) ≤ -Real.log (640 / 1037) ∧
    -Real.log (640 / 1037) ≤ (60327379 / 125000000) := by
  have h := checkLog_sound (w := (397 / 1677)) (n := 12)
    (lo := (482619031 / 1000000000)) (hi := (60327379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1037 / 640) = 1/(640 / 1037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (482619031 / 1000000000) (60327379 / 125000000) (Real.log (1037 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1037 / 640) = -Real.log (640 / 1037) := by
    rw [show ((1037 / 640) : ℝ) = ((640 / 1037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (242101683 / 250000000) ≤ -Real.log (243 / 640) ∧
    -Real.log (243 / 640) ≤ (484203367 / 500000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 243) = 1/(243 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-484203367 / 500000000) (-242101683 / 250000000) (Real.log (243 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (369557407 / 1000000000) ≤ -Real.log (500000 / 723547) ∧
    -Real.log (500000 / 723547) ≤ (11548669 / 31250000) := by
  have h := checkLog_sound (w := (223547 / 1223547)) (n := 12)
    (lo := (369557407 / 1000000000)) (hi := (11548669 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723547 / 500000) = 1/(500000 / 723547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (369557407 / 1000000000) (11548669 / 31250000) (Real.log (723547 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (723547 / 500000) = -Real.log (500000 / 723547) := by
    rw [show ((723547 / 500000) : ℝ) = ((500000 / 723547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (592567273 / 1000000000) ≤ -Real.log (276453 / 500000) ∧
    -Real.log (276453 / 500000) ≤ (296283637 / 500000000) := by
  have h := checkLog_sound (w := (223547 / 776453)) (n := 12)
    (lo := (592567273 / 1000000000)) (hi := (296283637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276453) = 1/(276453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-296283637 / 500000000) (-592567273 / 1000000000) (Real.log (276453 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (370168791 / 1000000000) ≤ -Real.log (1000000 / 1447979) ∧
    -Real.log (1000000 / 1447979) ≤ (46271099 / 125000000) := by
  have h := checkLog_sound (w := (447979 / 2447979)) (n := 12)
    (lo := (370168791 / 1000000000)) (hi := (46271099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447979 / 1000000) = 1/(1000000 / 1447979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (370168791 / 1000000000) (46271099 / 125000000) (Real.log (1447979 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1447979 / 1000000) = -Real.log (1000000 / 1447979) := by
    rw [show ((1447979 / 1000000) : ℝ) = ((1000000 / 1447979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (594169189 / 1000000000) ≤ -Real.log (552021 / 1000000) ∧
    -Real.log (552021 / 1000000) ≤ (59416919 / 100000000) := by
  have h := checkLog_sound (w := (447979 / 1552021)) (n := 12)
    (lo := (594169189 / 1000000000)) (hi := (59416919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 552021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 552021) = 1/(552021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59416919 / 100000000) (-594169189 / 1000000000) (Real.log (552021 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (28864361 / 100000000) ≤ -Real.log (125000 / 166827) ∧
    -Real.log (125000 / 166827) ≤ (288643611 / 1000000000) := by
  have h := checkLog_sound (w := (41827 / 291827)) (n := 12)
    (lo := (28864361 / 100000000)) (hi := (288643611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166827 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166827 / 125000) = 1/(125000 / 166827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (28864361 / 100000000) (288643611 / 1000000000) (Real.log (166827 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (166827 / 125000) = -Real.log (125000 / 166827) := by
    rw [show ((166827 / 125000) : ℝ) = ((125000 / 166827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (407390961 / 1000000000) ≤ -Real.log (83173 / 125000) ∧
    -Real.log (83173 / 125000) ≤ (203695481 / 500000000) := by
  have h := checkLog_sound (w := (41827 / 208173)) (n := 12)
    (lo := (407390961 / 1000000000)) (hi := (203695481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 83173) = 1/(83173 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-203695481 / 500000000) (-407390961 / 1000000000) (Real.log (83173 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (144598961 / 500000000) ≤ -Real.log (250000 / 333839) ∧
    -Real.log (250000 / 333839) ≤ (289197923 / 1000000000) := by
  have h := checkLog_sound (w := (83839 / 583839)) (n := 12)
    (lo := (144598961 / 500000000)) (hi := (289197923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333839 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333839 / 250000) = 1/(250000 / 333839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144598961 / 500000000) (289197923 / 1000000000) (Real.log (333839 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (333839 / 250000) = -Real.log (250000 / 333839) := by
    rw [show ((333839 / 250000) : ℝ) = ((250000 / 333839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10212593 / 25000000) ≤ -Real.log (166161 / 250000) ∧
    -Real.log (166161 / 250000) ≤ (408503721 / 1000000000) := by
  have h := checkLog_sound (w := (83839 / 416161)) (n := 12)
    (lo := (10212593 / 25000000)) (hi := (408503721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 166161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 166161) = 1/(166161 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-408503721 / 1000000000) (-10212593 / 25000000) (Real.log (166161 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (24053117 / 25000000) ≤ -Real.log (500000000000 / 1308625697677) ∧
    -Real.log (500000000000 / 1308625697677) ≤ (481062341 / 500000000) := by
  have h := checkLog_sound (w := (308625697677 / 2308625697677)) (n := 12)
    (lo := (107591 / 400000)) (hi := (268977501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308625697677 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1308625697677 / 1000000000000) = 1/(500000000000 / 1308625697677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24053117 / 25000000) (481062341 / 500000000) (Real.log (1308625697677 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1308625697677 / 500000000000) = -Real.log (500000000000 / 1308625697677) := by
    rw [show ((1308625697677 / 500000000000) : ℝ) = ((500000000000 / 1308625697677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (48216899 / 50000000) ≤ -Real.log (15625000000 / 40985165193) ∧
    -Real.log (15625000000 / 40985165193) ≤ (482168991 / 500000000) := by
  have h := checkLog_sound (w := (9735165193 / 72235165193)) (n := 12)
    (lo := (677977 / 2500000)) (hi := (271190801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40985165193 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40985165193 / 31250000000) = 1/(15625000000 / 40985165193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (48216899 / 50000000) (482168991 / 500000000) (Real.log (40985165193 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40985165193 / 15625000000) = -Real.log (15625000000 / 40985165193) := by
    rw [show ((40985165193 / 15625000000) : ℝ) = ((15625000000 / 40985165193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (69603457 / 100000000) ≤ -Real.log (500000000000 / 1002891563367) ∧
    -Real.log (500000000000 / 1002891563367) ≤ (174008643 / 250000000) := by
  have h := checkLog_sound (w := (2891563367 / 2002891563367)) (n := 12)
    (lo := (288739 / 100000000)) (hi := (2887391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002891563367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002891563367 / 1000000000000) = 1/(500000000000 / 1002891563367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (69603457 / 100000000) (174008643 / 250000000) (Real.log (1002891563367 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1002891563367 / 500000000000) = -Real.log (500000000000 / 1002891563367) := by
    rw [show ((1002891563367 / 500000000000) : ℝ) = ((500000000000 / 1002891563367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (348850821 / 500000000) ≤ -Real.log (100000000000 / 200912969951) ∧
    -Real.log (100000000000 / 200912969951) ≤ (174425411 / 250000000) := by
  have h := checkLog_sound (w := (912969951 / 400912969951)) (n := 12)
    (lo := (2277231 / 500000000)) (hi := (4554463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200912969951 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200912969951 / 200000000000) = 1/(100000000000 / 200912969951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (348850821 / 500000000) (174425411 / 250000000) (Real.log (200912969951 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (200912969951 / 100000000000) = -Real.log (100000000000 / 200912969951) := by
    rw [show ((200912969951 / 100000000000) : ℝ) = ((100000000000 / 200912969951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0189
