import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0301
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

theorem reflection_log_1_neg : (55922569 / 250000000) ≤ -Real.log (10240 / 12807) ∧
    -Real.log (10240 / 12807) ≤ (223690277 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 23047)) (n := 12)
    (lo := (55922569 / 250000000)) (hi := (223690277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12807 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12807 / 10240) = 1/(10240 / 12807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55922569 / 250000000) (223690277 / 1000000000) (Real.log (12807 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12807 / 10240) = -Real.log (10240 / 12807) := by
    rw [show ((12807 / 10240) : ℝ) = ((10240 / 12807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144296973 / 500000000) ≤ -Real.log (7673 / 10240) ∧
    -Real.log (7673 / 10240) ≤ (288593947 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 17913)) (n := 12)
    (lo := (144296973 / 500000000)) (hi := (288593947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7673) = 1/(7673 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-288593947 / 1000000000) (-144296973 / 500000000) (Real.log (7673 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111728001 / 500000000) ≤ -Real.log (2560 / 3201) ∧
    -Real.log (2560 / 3201) ≤ (223456003 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 5761)) (n := 12)
    (lo := (111728001 / 500000000)) (hi := (223456003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3201 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3201 / 2560) = 1/(2560 / 3201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111728001 / 500000000) (223456003 / 1000000000) (Real.log (3201 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3201 / 2560) = -Real.log (2560 / 3201) := by
    rw [show ((3201 / 2560) : ℝ) = ((2560 / 3201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (288203041 / 1000000000) ≤ -Real.log (1919 / 2560) ∧
    -Real.log (1919 / 2560) ≤ (144101521 / 500000000) := by
  have h := checkLog_sound (w := (641 / 4479)) (n := 12)
    (lo := (288203041 / 1000000000)) (hi := (144101521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1919) = 1/(1919 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-144101521 / 500000000) (-288203041 / 1000000000) (Real.log (1919 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (406376151 / 1000000000) ≤ -Real.log (5120 / 7687) ∧
    -Real.log (5120 / 7687) ≤ (50797019 / 125000000) := by
  have h := checkLog_sound (w := (2567 / 12807)) (n := 12)
    (lo := (406376151 / 1000000000)) (hi := (50797019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7687 / 5120) = 1/(5120 / 7687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (406376151 / 1000000000) (50797019 / 125000000) (Real.log (7687 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7687 / 5120) = -Real.log (5120 / 7687) := by
    rw [show ((7687 / 5120) : ℝ) = ((5120 / 7687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6958853 / 10000000) ≤ -Real.log (2553 / 5120) ∧
    -Real.log (2553 / 5120) ≤ (347942651 / 500000000) := by
  have h := checkLog_sound (w := (7 / 5113)) (n := 12)
    (lo := (68453 / 25000000)) (hi := (2738121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2553) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2553) = 1/(2553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-347942651 / 500000000) (-6958853 / 10000000) (Real.log (2553 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81197161 / 200000000) ≤ -Real.log (1280 / 1921) ∧
    -Real.log (1280 / 1921) ≤ (202992903 / 500000000) := by
  have h := checkLog_sound (w := (641 / 3201)) (n := 12)
    (lo := (81197161 / 200000000)) (hi := (202992903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1280) = 1/(1280 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81197161 / 200000000) (202992903 / 500000000) (Real.log (1921 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1921 / 1280) = -Real.log (1280 / 1921) := by
    rw [show ((1921 / 1280) : ℝ) = ((1280 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (694710901 / 1000000000) ≤ -Real.log (639 / 1280) ∧
    -Real.log (639 / 1280) ≤ (694710903 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1279)) (n := 12)
    (lo := (1563721 / 1000000000)) (hi := (781861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 639) = 1/(639 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-694710903 / 1000000000) (-694710901 / 1000000000) (Real.log (639 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153099289 / 500000000) ≤ -Real.log (250000 / 339563) ∧
    -Real.log (250000 / 339563) ≤ (306198579 / 1000000000) := by
  have h := checkLog_sound (w := (89563 / 589563)) (n := 12)
    (lo := (153099289 / 500000000)) (hi := (306198579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339563 / 250000) = 1/(250000 / 339563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153099289 / 500000000) (306198579 / 1000000000) (Real.log (339563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (339563 / 250000) = -Real.log (250000 / 339563) := by
    rw [show ((339563 / 250000) : ℝ) = ((250000 / 339563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17742383 / 40000000) ≤ -Real.log (160437 / 250000) ∧
    -Real.log (160437 / 250000) ≤ (55444947 / 125000000) := by
  have h := checkLog_sound (w := (89563 / 410437)) (n := 12)
    (lo := (17742383 / 40000000)) (hi := (55444947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160437) = 1/(160437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55444947 / 125000000) (-17742383 / 40000000) (Real.log (160437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (38314481 / 125000000) ≤ -Real.log (1000000 / 1358683) ∧
    -Real.log (1000000 / 1358683) ≤ (306515849 / 1000000000) := by
  have h := checkLog_sound (w := (358683 / 2358683)) (n := 12)
    (lo := (38314481 / 125000000)) (hi := (306515849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358683 / 1000000) = 1/(1000000 / 1358683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (38314481 / 125000000) (306515849 / 1000000000) (Real.log (1358683 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1358683 / 1000000) = -Real.log (1000000 / 1358683) := by
    rw [show ((1358683 / 1000000) : ℝ) = ((1000000 / 1358683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111057851 / 250000000) ≤ -Real.log (641317 / 1000000) ∧
    -Real.log (641317 / 1000000) ≤ (88846281 / 200000000) := by
  have h := checkLog_sound (w := (358683 / 1641317)) (n := 12)
    (lo := (111057851 / 250000000)) (hi := (88846281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641317) = 1/(641317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88846281 / 200000000) (-111057851 / 250000000) (Real.log (641317 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (233211103 / 1000000000) ≤ -Real.log (125000 / 157831) ∧
    -Real.log (125000 / 157831) ≤ (7287847 / 31250000) := by
  have h := checkLog_sound (w := (32831 / 282831)) (n := 12)
    (lo := (233211103 / 1000000000)) (hi := (7287847 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157831 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157831 / 125000) = 1/(125000 / 157831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (233211103 / 1000000000) (7287847 / 31250000) (Real.log (157831 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (157831 / 125000) = -Real.log (125000 / 157831) := by
    rw [show ((157831 / 125000) : ℝ) = ((125000 / 157831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9521559 / 31250000) ≤ -Real.log (92169 / 125000) ∧
    -Real.log (92169 / 125000) ≤ (304689889 / 1000000000) := by
  have h := checkLog_sound (w := (32831 / 217169)) (n := 12)
    (lo := (9521559 / 31250000)) (hi := (304689889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92169) = 1/(92169 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-304689889 / 1000000000) (-9521559 / 31250000) (Real.log (92169 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (116740171 / 500000000) ≤ -Real.log (250000 / 315747) ∧
    -Real.log (250000 / 315747) ≤ (233480343 / 1000000000) := by
  have h := checkLog_sound (w := (65747 / 565747)) (n := 12)
    (lo := (116740171 / 500000000)) (hi := (233480343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315747 / 250000) = 1/(250000 / 315747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116740171 / 500000000) (233480343 / 1000000000) (Real.log (315747 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (315747 / 250000) = -Real.log (250000 / 315747) := by
    rw [show ((315747 / 250000) : ℝ) = ((250000 / 315747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2383993 / 7812500) ≤ -Real.log (184253 / 250000) ∧
    -Real.log (184253 / 250000) ≤ (61030221 / 200000000) := by
  have h := checkLog_sound (w := (65747 / 434253)) (n := 12)
    (lo := (2383993 / 7812500)) (hi := (61030221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184253) = 1/(184253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-61030221 / 200000000) (-2383993 / 7812500) (Real.log (184253 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (374879077 / 500000000) ≤ -Real.log (500000000000 / 1058244045949) ∧
    -Real.log (500000000000 / 1058244045949) ≤ (187439539 / 250000000) := by
  have h := checkLog_sound (w := (58244045949 / 2058244045949)) (n := 12)
    (lo := (28305487 / 500000000)) (hi := (2264439 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1058244045949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1058244045949 / 1000000000000) = 1/(500000000000 / 1058244045949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (374879077 / 500000000) (187439539 / 250000000) (Real.log (1058244045949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1058244045949 / 500000000000) = -Real.log (500000000000 / 1058244045949) := by
    rw [show ((1058244045949 / 500000000000) : ℝ) = ((500000000000 / 1058244045949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (187686813 / 250000000) ≤ -Real.log (125000000000 / 264822817733) ∧
    -Real.log (125000000000 / 264822817733) ≤ (375373627 / 500000000) := by
  have h := checkLog_sound (w := (14822817733 / 514822817733)) (n := 12)
    (lo := (7200009 / 125000000)) (hi := (57600073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264822817733 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264822817733 / 250000000000) = 1/(125000000000 / 264822817733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (187686813 / 250000000) (375373627 / 500000000) (Real.log (264822817733 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (264822817733 / 125000000000) = -Real.log (125000000000 / 264822817733) := by
    rw [show ((264822817733 / 125000000000) : ℝ) = ((125000000000 / 264822817733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (537900991 / 1000000000) ≤ -Real.log (500000000000 / 856204363723) ∧
    -Real.log (500000000000 / 856204363723) ≤ (8404703 / 15625000) := by
  have h := checkLog_sound (w := (356204363723 / 1356204363723)) (n := 12)
    (lo := (537900991 / 1000000000)) (hi := (8404703 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856204363723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856204363723 / 500000000000) = 1/(500000000000 / 856204363723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (537900991 / 1000000000) (8404703 / 15625000) (Real.log (856204363723 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (856204363723 / 500000000000) = -Real.log (500000000000 / 856204363723) := by
    rw [show ((856204363723 / 500000000000) : ℝ) = ((500000000000 / 856204363723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (269315723 / 500000000) ≤ -Real.log (500000000000 / 856830010909) ∧
    -Real.log (500000000000 / 856830010909) ≤ (538631447 / 1000000000) := by
  have h := checkLog_sound (w := (356830010909 / 1356830010909)) (n := 12)
    (lo := (269315723 / 500000000)) (hi := (538631447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856830010909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856830010909 / 500000000000) = 1/(500000000000 / 856830010909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (269315723 / 500000000) (538631447 / 1000000000) (Real.log (856830010909 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (856830010909 / 500000000000) = -Real.log (500000000000 / 856830010909) := by
    rw [show ((856830010909 / 500000000000) : ℝ) = ((500000000000 / 856830010909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0301
