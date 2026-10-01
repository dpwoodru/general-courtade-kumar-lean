import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0020
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

theorem reflection_log_1_neg : (199204511 / 500000000) ≤ -Real.log (2560 / 3813) ∧
    -Real.log (2560 / 3813) ≤ (398409023 / 1000000000) := by
  have h := checkLog_sound (w := (1253 / 6373)) (n := 12)
    (lo := (199204511 / 500000000)) (hi := (398409023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813 / 2560) = 1/(2560 / 3813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199204511 / 500000000) (398409023 / 1000000000) (Real.log (3813 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3813 / 2560) = -Real.log (2560 / 3813) := by
    rw [show ((3813 / 2560) : ℝ) = ((2560 / 3813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (672272823 / 1000000000) ≤ -Real.log (1307 / 2560) ∧
    -Real.log (1307 / 2560) ≤ (84034103 / 125000000) := by
  have h := checkLog_sound (w := (1253 / 3867)) (n := 12)
    (lo := (672272823 / 1000000000)) (hi := (84034103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1307) = 1/(1307 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-84034103 / 125000000) (-672272823 / 1000000000) (Real.log (1307 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (39762193 / 100000000) ≤ -Real.log (256 / 381) ∧
    -Real.log (256 / 381) ≤ (397621931 / 1000000000) := by
  have h := checkLog_sound (w := (125 / 637)) (n := 12)
    (lo := (39762193 / 100000000)) (hi := (397621931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 256) = 1/(256 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (39762193 / 100000000) (397621931 / 1000000000) (Real.log (381 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (381 / 256) = -Real.log (256 / 381) := by
    rw [show ((381 / 256) : ℝ) = ((256 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (669980121 / 1000000000) ≤ -Real.log (131 / 256) ∧
    -Real.log (131 / 256) ≤ (334990061 / 500000000) := by
  have h := checkLog_sound (w := (125 / 387)) (n := 12)
    (lo := (669980121 / 1000000000)) (hi := (334990061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 131) = 1/(131 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334990061 / 500000000) (-669980121 / 1000000000) (Real.log (131 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (682544293 / 1000000000) ≤ -Real.log (1280 / 2533) ∧
    -Real.log (1280 / 2533) ≤ (341272147 / 500000000) := by
  have h := checkLog_sound (w := (1253 / 3813)) (n := 12)
    (lo := (682544293 / 1000000000)) (hi := (341272147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2533 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2533 / 1280) = 1/(1280 / 2533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (682544293 / 1000000000) (341272147 / 500000000) (Real.log (2533 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2533 / 1280) = -Real.log (1280 / 2533) := by
    rw [show ((2533 / 1280) : ℝ) = ((1280 / 2533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (482347311 / 125000000) ≤ -Real.log (27 / 1280) ∧
    -Real.log (27 / 1280) ≤ (1929389247 / 500000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 27) = 1/(27 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1929389247 / 500000000) (-482347311 / 125000000) (Real.log (27 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85169903 / 125000000) ≤ -Real.log (128 / 253) ∧
    -Real.log (128 / 253) ≤ (27254369 / 40000000) := by
  have h := checkLog_sound (w := (125 / 381)) (n := 12)
    (lo := (85169903 / 125000000)) (hi := (27254369 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253 / 128) = 1/(128 / 253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85169903 / 125000000) (27254369 / 40000000) (Real.log (253 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (253 / 128) = -Real.log (128 / 253) := by
    rw [show ((253 / 128) : ℝ) = ((128 / 253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (938354493 / 250000000) ≤ -Real.log (3 / 128) ∧
    -Real.log (3 / 128) ≤ (1876708989 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4 / 3) = 1/(3 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1876708989 / 500000000) (-938354493 / 250000000) (Real.log (3 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (558625011 / 1000000000) ≤ -Real.log (1000000 / 1748267) ∧
    -Real.log (1000000 / 1748267) ≤ (139656253 / 250000000) := by
  have h := checkLog_sound (w := (748267 / 2748267)) (n := 12)
    (lo := (558625011 / 1000000000)) (hi := (139656253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1748267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1748267 / 1000000) = 1/(1000000 / 1748267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (558625011 / 1000000000) (139656253 / 250000000) (Real.log (1748267 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1748267 / 1000000) = -Real.log (1000000 / 1748267) := by
    rw [show ((1748267 / 1000000) : ℝ) = ((1000000 / 1748267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344846569 / 250000000) ≤ -Real.log (251733 / 1000000) ∧
    -Real.log (251733 / 1000000) ≤ (689693139 / 500000000) := by
  have h := checkLog_sound (w := (248267 / 751733)) (n := 12)
    (lo := (85779887 / 125000000)) (hi := (686239097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251733) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 251733) = 1/(251733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-689693139 / 500000000) (-344846569 / 250000000) (Real.log (251733 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (280085531 / 500000000) ≤ -Real.log (250000 / 437743) ∧
    -Real.log (250000 / 437743) ≤ (560171063 / 1000000000) := by
  have h := checkLog_sound (w := (187743 / 687743)) (n := 12)
    (lo := (280085531 / 500000000)) (hi := (560171063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437743 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437743 / 250000) = 1/(250000 / 437743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (280085531 / 500000000) (560171063 / 1000000000) (Real.log (437743 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (437743 / 250000) = -Real.log (250000 / 437743) := by
    rw [show ((437743 / 250000) : ℝ) = ((250000 / 437743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1390189937 / 1000000000) ≤ -Real.log (62257 / 250000) ∧
    -Real.log (62257 / 250000) ≤ (69509497 / 50000000) := by
  have h := checkLog_sound (w := (243 / 124757)) (n := 12)
    (lo := (3895577 / 1000000000)) (hi := (1947789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62257) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 62257) = 1/(62257 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69509497 / 50000000) (-1390189937 / 1000000000) (Real.log (62257 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (121188883 / 250000000) ≤ -Real.log (500000 / 811889) ∧
    -Real.log (500000 / 811889) ≤ (484755533 / 1000000000) := by
  have h := checkLog_sound (w := (311889 / 1311889)) (n := 12)
    (lo := (121188883 / 250000000)) (hi := (484755533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811889 / 500000) = 1/(500000 / 811889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (121188883 / 250000000) (484755533 / 1000000000) (Real.log (811889 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (811889 / 500000) = -Real.log (500000 / 811889) := by
    rw [show ((811889 / 500000) : ℝ) = ((500000 / 811889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (977575883 / 1000000000) ≤ -Real.log (188111 / 500000) ∧
    -Real.log (188111 / 500000) ≤ (195515177 / 200000000) := by
  have h := checkLog_sound (w := (61889 / 438111)) (n := 12)
    (lo := (284428703 / 1000000000)) (hi := (8888397 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 188111) = 1/(188111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-195515177 / 200000000) (-977575883 / 1000000000) (Real.log (188111 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (97320643 / 200000000) ≤ -Real.log (1000000 / 1626781) ∧
    -Real.log (1000000 / 1626781) ≤ (30412701 / 62500000) := by
  have h := checkLog_sound (w := (626781 / 2626781)) (n := 12)
    (lo := (97320643 / 200000000)) (hi := (30412701 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626781 / 1000000) = 1/(1000000 / 1626781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97320643 / 200000000) (30412701 / 62500000) (Real.log (1626781 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1626781 / 1000000) = -Real.log (1000000 / 1626781) := by
    rw [show ((1626781 / 1000000) : ℝ) = ((1000000 / 1626781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (985589899 / 1000000000) ≤ -Real.log (373219 / 1000000) ∧
    -Real.log (373219 / 1000000) ≤ (985589901 / 1000000000) := by
  have h := checkLog_sound (w := (126781 / 873219)) (n := 12)
    (lo := (292442719 / 1000000000)) (hi := (1827767 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373219) = 1/(373219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-985589901 / 1000000000) (-985589899 / 1000000000) (Real.log (373219 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1938011287 / 1000000000) ≤ -Real.log (100000000000 / 694492577453) ∧
    -Real.log (100000000000 / 694492577453) ≤ (193801129 / 100000000) := by
  have h := checkLog_sound (w := (294492577453 / 1094492577453)) (n := 12)
    (lo := (551716927 / 1000000000)) (hi := (8620577 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694492577453 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(694492577453 / 400000000000) = 1/(100000000000 / 694492577453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1938011287 / 1000000000) (193801129 / 100000000) (Real.log (694492577453 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (694492577453 / 100000000000) = -Real.log (100000000000 / 694492577453) := by
    rw [show ((694492577453 / 100000000000) : ℝ) = ((100000000000 / 694492577453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1950361 / 1000000) ≤ -Real.log (500000000000 / 3515612702187) ∧
    -Real.log (500000000000 / 3515612702187) ≤ (1950361003 / 1000000000) := by
  have h := checkLog_sound (w := (1515612702187 / 5515612702187)) (n := 12)
    (lo := (7050833 / 12500000)) (hi := (564066641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3515612702187 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3515612702187 / 2000000000000) = 1/(500000000000 / 3515612702187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1950361 / 1000000) (1950361003 / 1000000000) (Real.log (3515612702187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3515612702187 / 500000000000) = -Real.log (500000000000 / 3515612702187) := by
    rw [show ((3515612702187 / 500000000000) : ℝ) = ((500000000000 / 3515612702187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (182791427 / 125000000) ≤ -Real.log (500000000000 / 2158005114001) ∧
    -Real.log (500000000000 / 2158005114001) ≤ (1462331419 / 1000000000) := by
  have h := checkLog_sound (w := (158005114001 / 4158005114001)) (n := 12)
    (lo := (1188079 / 15625000)) (hi := (76037057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2158005114001 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2158005114001 / 2000000000000) = 1/(500000000000 / 2158005114001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (182791427 / 125000000) (1462331419 / 1000000000) (Real.log (2158005114001 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2158005114001 / 500000000000) = -Real.log (500000000000 / 2158005114001) := by
    rw [show ((2158005114001 / 500000000000) : ℝ) = ((500000000000 / 2158005114001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (736096557 / 500000000) ≤ -Real.log (50000000000 / 217939199237) ∧
    -Real.log (50000000000 / 217939199237) ≤ (1472193117 / 1000000000) := by
  have h := checkLog_sound (w := (17939199237 / 417939199237)) (n := 12)
    (lo := (42949377 / 500000000)) (hi := (17179751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217939199237 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(217939199237 / 200000000000) = 1/(50000000000 / 217939199237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (736096557 / 500000000) (1472193117 / 1000000000) (Real.log (217939199237 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (217939199237 / 50000000000) = -Real.log (50000000000 / 217939199237) := by
    rw [show ((217939199237 / 50000000000) : ℝ) = ((50000000000 / 217939199237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0020
