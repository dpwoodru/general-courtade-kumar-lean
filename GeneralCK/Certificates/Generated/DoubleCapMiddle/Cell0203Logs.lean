import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0203
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

theorem reflection_log_1_neg : (66078871 / 250000000) ≤ -Real.log (5120 / 6669) ∧
    -Real.log (5120 / 6669) ≤ (52863097 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 11789)) (n := 12)
    (lo := (66078871 / 250000000)) (hi := (52863097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6669 / 5120) = 1/(5120 / 6669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66078871 / 250000000) (52863097 / 200000000) (Real.log (6669 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6669 / 5120) = -Real.log (5120 / 6669) := by
    rw [show ((6669 / 5120) : ℝ) = ((5120 / 6669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36030877 / 100000000) ≤ -Real.log (3571 / 5120) ∧
    -Real.log (3571 / 5120) ≤ (360308771 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 8691)) (n := 12)
    (lo := (36030877 / 100000000)) (hi := (360308771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3571) = 1/(3571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-360308771 / 1000000000) (-36030877 / 100000000) (Real.log (3571 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13193277 / 50000000) ≤ -Real.log (2560 / 3333) ∧
    -Real.log (2560 / 3333) ≤ (263865541 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 5893)) (n := 12)
    (lo := (13193277 / 50000000)) (hi := (263865541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3333 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3333 / 2560) = 1/(2560 / 3333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13193277 / 50000000) (263865541 / 1000000000) (Real.log (3333 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3333 / 2560) = -Real.log (2560 / 3333) := by
    rw [show ((3333 / 2560) : ℝ) = ((2560 / 3333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (179734511 / 500000000) ≤ -Real.log (1787 / 2560) ∧
    -Real.log (1787 / 2560) ≤ (359469023 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 4347)) (n := 12)
    (lo := (179734511 / 500000000)) (hi := (359469023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1787) = 1/(1787 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-359469023 / 1000000000) (-179734511 / 500000000) (Real.log (1787 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (473172431 / 1000000000) ≤ -Real.log (2560 / 4109) ∧
    -Real.log (2560 / 4109) ≤ (29573277 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 6669)) (n := 12)
    (lo := (473172431 / 1000000000)) (hi := (29573277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4109 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4109 / 2560) = 1/(2560 / 4109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (473172431 / 1000000000) (29573277 / 62500000) (Real.log (4109 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4109 / 2560) = -Real.log (2560 / 4109) := by
    rw [show ((4109 / 2560) : ℝ) = ((2560 / 4109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (929067317 / 1000000000) ≤ -Real.log (1011 / 2560) ∧
    -Real.log (1011 / 2560) ≤ (929067319 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2291)) (n := 12)
    (lo := (235920137 / 1000000000)) (hi := (117960069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1011) = 1/(1011 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-929067319 / 1000000000) (-929067317 / 1000000000) (Real.log (1011 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23622103 / 50000000) ≤ -Real.log (1280 / 2053) ∧
    -Real.log (1280 / 2053) ≤ (472442061 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 3333)) (n := 12)
    (lo := (23622103 / 50000000)) (hi := (472442061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2053 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2053 / 1280) = 1/(1280 / 2053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23622103 / 50000000) (472442061 / 1000000000) (Real.log (2053 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2053 / 1280) = -Real.log (1280 / 2053) := by
    rw [show ((2053 / 1280) : ℝ) = ((1280 / 2053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28940761 / 31250000) ≤ -Real.log (507 / 1280) ∧
    -Real.log (507 / 1280) ≤ (463052177 / 500000000) := by
  have h := checkLog_sound (w := (133 / 1147)) (n := 12)
    (lo := (58239293 / 250000000)) (hi := (232957173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 507) = 1/(507 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-463052177 / 500000000) (-28940761 / 31250000) (Real.log (507 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (180495309 / 500000000) ≤ -Real.log (4000 / 5739) ∧
    -Real.log (4000 / 5739) ≤ (360990619 / 1000000000) := by
  have h := checkLog_sound (w := (1739 / 9739)) (n := 12)
    (lo := (180495309 / 500000000)) (hi := (360990619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5739 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5739 / 4000) = 1/(4000 / 5739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (180495309 / 500000000) (360990619 / 1000000000) (Real.log (5739 / 4000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (5739 / 4000) = -Real.log (4000 / 5739) := by
    rw [show ((5739 / 4000) : ℝ) = ((4000 / 5739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (570487167 / 1000000000) ≤ -Real.log (2261 / 4000) ∧
    -Real.log (2261 / 4000) ≤ (4456931 / 7812500) := by
  have h := checkLog_sound (w := (1739 / 6261)) (n := 12)
    (lo := (570487167 / 1000000000)) (hi := (4456931 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2261) = 1/(2261 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4456931 / 7812500) (-570487167 / 1000000000) (Real.log (2261 / 4000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (361604473 / 1000000000) ≤ -Real.log (1000000 / 1435631) ∧
    -Real.log (1000000 / 1435631) ≤ (180802237 / 500000000) := by
  have h := checkLog_sound (w := (435631 / 2435631)) (n := 12)
    (lo := (361604473 / 1000000000)) (hi := (180802237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1435631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1435631 / 1000000) = 1/(1000000 / 1435631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (361604473 / 1000000000) (180802237 / 500000000) (Real.log (1435631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1435631 / 1000000) = -Real.log (1000000 / 1435631) := by
    rw [show ((1435631 / 1000000) : ℝ) = ((1000000 / 1435631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (286023493 / 500000000) ≤ -Real.log (564369 / 1000000) ∧
    -Real.log (564369 / 1000000) ≤ (572046987 / 1000000000) := by
  have h := checkLog_sound (w := (435631 / 1564369)) (n := 12)
    (lo := (286023493 / 500000000)) (hi := (572046987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 564369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 564369) = 1/(564369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-572046987 / 1000000000) (-286023493 / 500000000) (Real.log (564369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8778829 / 31250000) ≤ -Real.log (1000000 / 1324351) ∧
    -Real.log (1000000 / 1324351) ≤ (280922529 / 1000000000) := by
  have h := checkLog_sound (w := (324351 / 2324351)) (n := 12)
    (lo := (8778829 / 31250000)) (hi := (280922529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324351 / 1000000) = 1/(1000000 / 1324351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8778829 / 31250000) (280922529 / 1000000000) (Real.log (1324351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1324351 / 1000000) = -Real.log (1000000 / 1324351) := by
    rw [show ((1324351 / 1000000) : ℝ) = ((1000000 / 1324351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (12252549 / 31250000) ≤ -Real.log (675649 / 1000000) ∧
    -Real.log (675649 / 1000000) ≤ (392081569 / 1000000000) := by
  have h := checkLog_sound (w := (324351 / 1675649)) (n := 12)
    (lo := (12252549 / 31250000)) (hi := (392081569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675649) = 1/(675649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-392081569 / 1000000000) (-12252549 / 31250000) (Real.log (675649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (281473589 / 1000000000) ≤ -Real.log (1000000 / 1325081) ∧
    -Real.log (1000000 / 1325081) ≤ (28147359 / 100000000) := by
  have h := checkLog_sound (w := (325081 / 2325081)) (n := 12)
    (lo := (281473589 / 1000000000)) (hi := (28147359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325081 / 1000000) = 1/(1000000 / 1325081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281473589 / 1000000000) (28147359 / 100000000) (Real.log (1325081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1325081 / 1000000) = -Real.log (1000000 / 1325081) := by
    rw [show ((1325081 / 1000000) : ℝ) = ((1000000 / 1325081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (78632519 / 200000000) ≤ -Real.log (674919 / 1000000) ∧
    -Real.log (674919 / 1000000) ≤ (98290649 / 250000000) := by
  have h := checkLog_sound (w := (325081 / 1674919)) (n := 12)
    (lo := (78632519 / 200000000)) (hi := (98290649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674919) = 1/(674919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-98290649 / 250000000) (-78632519 / 200000000) (Real.log (674919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (186295557 / 200000000) ≤ -Real.log (500000000000 / 1269128704113) ∧
    -Real.log (500000000000 / 1269128704113) ≤ (931477787 / 1000000000) := by
  have h := checkLog_sound (w := (269128704113 / 2269128704113)) (n := 12)
    (lo := (47666121 / 200000000)) (hi := (119165303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269128704113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1269128704113 / 1000000000000) = 1/(500000000000 / 1269128704113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (186295557 / 200000000) (931477787 / 1000000000) (Real.log (1269128704113 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1269128704113 / 500000000000) = -Real.log (500000000000 / 1269128704113) := by
    rw [show ((1269128704113 / 500000000000) : ℝ) = ((500000000000 / 1269128704113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (933651459 / 1000000000) ≤ -Real.log (500000000000 / 1271890376687) ∧
    -Real.log (500000000000 / 1271890376687) ≤ (933651461 / 1000000000) := by
  have h := checkLog_sound (w := (271890376687 / 2271890376687)) (n := 12)
    (lo := (240504279 / 1000000000)) (hi := (6012607 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271890376687 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1271890376687 / 1000000000000) = 1/(500000000000 / 1271890376687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (933651459 / 1000000000) (933651461 / 1000000000) (Real.log (1271890376687 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1271890376687 / 500000000000) = -Real.log (500000000000 / 1271890376687) := by
    rw [show ((1271890376687 / 500000000000) : ℝ) = ((500000000000 / 1271890376687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10515689 / 15625000) ≤ -Real.log (250000000000 / 490029216353) ∧
    -Real.log (250000000000 / 490029216353) ≤ (673004097 / 1000000000) := by
  have h := checkLog_sound (w := (240029216353 / 740029216353)) (n := 12)
    (lo := (10515689 / 15625000)) (hi := (673004097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490029216353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490029216353 / 250000000000) = 1/(250000000000 / 490029216353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (10515689 / 15625000) (673004097 / 1000000000) (Real.log (490029216353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (490029216353 / 250000000000) = -Real.log (250000000000 / 490029216353) := by
    rw [show ((490029216353 / 250000000000) : ℝ) = ((250000000000 / 490029216353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (84329523 / 125000000) ≤ -Real.log (125000000000 / 245414820149) ∧
    -Real.log (125000000000 / 245414820149) ≤ (134927237 / 200000000) := by
  have h := checkLog_sound (w := (120414820149 / 370414820149)) (n := 12)
    (lo := (84329523 / 125000000)) (hi := (134927237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245414820149 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245414820149 / 125000000000) = 1/(125000000000 / 245414820149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (84329523 / 125000000) (134927237 / 200000000) (Real.log (245414820149 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245414820149 / 125000000000) = -Real.log (125000000000 / 245414820149) := by
    rw [show ((245414820149 / 125000000000) : ℝ) = ((125000000000 / 245414820149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0203
