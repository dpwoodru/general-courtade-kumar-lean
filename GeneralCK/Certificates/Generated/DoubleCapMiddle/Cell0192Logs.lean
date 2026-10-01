import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0192
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

theorem reflection_log_1_neg : (5385031 / 20000000) ≤ -Real.log (2560 / 3351) ∧
    -Real.log (2560 / 3351) ≤ (269251551 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5911)) (n := 12)
    (lo := (5385031 / 20000000)) (hi := (269251551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3351 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3351 / 2560) = 1/(2560 / 3351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5385031 / 20000000) (269251551 / 1000000000) (Real.log (3351 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3351 / 2560) = -Real.log (2560 / 3351) := by
    rw [show ((3351 / 2560) : ℝ) = ((2560 / 3351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (369592843 / 1000000000) ≤ -Real.log (1769 / 2560) ∧
    -Real.log (1769 / 2560) ≤ (92398211 / 250000000) := by
  have h := checkLog_sound (w := (791 / 4329)) (n := 12)
    (lo := (369592843 / 1000000000)) (hi := (92398211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1769) = 1/(1769 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-92398211 / 250000000) (-369592843 / 1000000000) (Real.log (1769 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134401911 / 500000000) ≤ -Real.log (5120 / 6699) ∧
    -Real.log (5120 / 6699) ≤ (268803823 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 11819)) (n := 12)
    (lo := (134401911 / 500000000)) (hi := (268803823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6699 / 5120) = 1/(5120 / 6699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134401911 / 500000000) (268803823 / 1000000000) (Real.log (6699 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6699 / 5120) = -Real.log (5120 / 6699) := by
    rw [show ((6699 / 5120) : ℝ) = ((5120 / 6699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73749053 / 200000000) ≤ -Real.log (3541 / 5120) ∧
    -Real.log (3541 / 5120) ≤ (184372633 / 500000000) := by
  have h := checkLog_sound (w := (1579 / 8661)) (n := 12)
    (lo := (73749053 / 200000000)) (hi := (184372633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3541) = 1/(3541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-184372633 / 500000000) (-73749053 / 200000000) (Real.log (3541 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30073219 / 62500000) ≤ -Real.log (1280 / 2071) ∧
    -Real.log (1280 / 2071) ≤ (96234301 / 200000000) := by
  have h := checkLog_sound (w := (791 / 3351)) (n := 12)
    (lo := (30073219 / 62500000)) (hi := (96234301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2071 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2071 / 1280) = 1/(1280 / 2071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30073219 / 62500000) (96234301 / 200000000) (Real.log (2071 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2071 / 1280) = -Real.log (1280 / 2071) := by
    rw [show ((2071 / 1280) : ℝ) = ((1280 / 2071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (481126433 / 500000000) ≤ -Real.log (489 / 1280) ∧
    -Real.log (489 / 1280) ≤ (240563217 / 250000000) := by
  have h := checkLog_sound (w := (151 / 1129)) (n := 12)
    (lo := (134552843 / 500000000)) (hi := (269105687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 489) = 1/(489 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-240563217 / 250000000) (-481126433 / 500000000) (Real.log (489 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240223477 / 500000000) ≤ -Real.log (2560 / 4139) ∧
    -Real.log (2560 / 4139) ≤ (96089391 / 200000000) := by
  have h := checkLog_sound (w := (1579 / 6699)) (n := 12)
    (lo := (240223477 / 500000000)) (hi := (96089391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4139 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4139 / 2560) = 1/(2560 / 4139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240223477 / 500000000) (96089391 / 200000000) (Real.log (4139 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4139 / 2560) = -Real.log (2560 / 4139) := by
    rw [show ((4139 / 2560) : ℝ) = ((2560 / 4139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (959190077 / 1000000000) ≤ -Real.log (981 / 2560) ∧
    -Real.log (981 / 2560) ≤ (959190079 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2261)) (n := 12)
    (lo := (266042897 / 1000000000)) (hi := (133021449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 981) = 1/(981 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-959190079 / 1000000000) (-959190077 / 1000000000) (Real.log (981 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45965559 / 125000000) ≤ -Real.log (250000 / 361111) ∧
    -Real.log (250000 / 361111) ≤ (367724473 / 1000000000) := by
  have h := checkLog_sound (w := (111111 / 611111)) (n := 12)
    (lo := (45965559 / 125000000)) (hi := (367724473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361111 / 250000) = 1/(250000 / 361111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45965559 / 125000000) (367724473 / 1000000000) (Real.log (361111 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (361111 / 250000) = -Real.log (250000 / 361111) := by
    rw [show ((361111 / 250000) : ℝ) = ((250000 / 361111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73473233 / 125000000) ≤ -Real.log (138889 / 250000) ∧
    -Real.log (138889 / 250000) ≤ (117557173 / 200000000) := by
  have h := checkLog_sound (w := (111111 / 388889)) (n := 12)
    (lo := (73473233 / 125000000)) (hi := (117557173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 138889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 138889) = 1/(138889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-117557173 / 200000000) (-73473233 / 125000000) (Real.log (138889 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73667257 / 200000000) ≤ -Real.log (62500 / 90333) ∧
    -Real.log (62500 / 90333) ≤ (184168143 / 500000000) := by
  have h := checkLog_sound (w := (27833 / 152833)) (n := 12)
    (lo := (73667257 / 200000000)) (hi := (184168143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90333 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90333 / 62500) = 1/(62500 / 90333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73667257 / 200000000) (184168143 / 500000000) (Real.log (90333 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (90333 / 62500) = -Real.log (62500 / 90333) := by
    rw [show ((90333 / 62500) : ℝ) = ((62500 / 90333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58937833 / 100000000) ≤ -Real.log (34667 / 62500) ∧
    -Real.log (34667 / 62500) ≤ (589378331 / 1000000000) := by
  have h := checkLog_sound (w := (27833 / 97167)) (n := 12)
    (lo := (58937833 / 100000000)) (hi := (589378331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34667) = 1/(34667 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-589378331 / 1000000000) (-58937833 / 100000000) (Real.log (34667 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (286985579 / 1000000000) ≤ -Real.log (200000 / 266481) ∧
    -Real.log (200000 / 266481) ≤ (14349279 / 50000000) := by
  have h := checkLog_sound (w := (66481 / 466481)) (n := 12)
    (lo := (286985579 / 1000000000)) (hi := (14349279 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266481 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266481 / 200000) = 1/(200000 / 266481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (286985579 / 1000000000) (14349279 / 50000000) (Real.log (266481 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (266481 / 200000) = -Real.log (200000 / 266481) := by
    rw [show ((266481 / 200000) : ℝ) = ((200000 / 266481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50509197 / 125000000) ≤ -Real.log (133519 / 200000) ∧
    -Real.log (133519 / 200000) ≤ (404073577 / 1000000000) := by
  have h := checkLog_sound (w := (66481 / 333519)) (n := 12)
    (lo := (50509197 / 125000000)) (hi := (404073577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133519) = 1/(133519 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-404073577 / 1000000000) (-50509197 / 125000000) (Real.log (133519 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (143769281 / 500000000) ≤ -Real.log (500000 / 666571) ∧
    -Real.log (500000 / 666571) ≤ (287538563 / 1000000000) := by
  have h := checkLog_sound (w := (166571 / 1166571)) (n := 12)
    (lo := (143769281 / 500000000)) (hi := (287538563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666571 / 500000) = 1/(500000 / 666571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (143769281 / 500000000) (287538563 / 1000000000) (Real.log (666571 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (666571 / 500000) = -Real.log (500000 / 666571) := by
    rw [show ((666571 / 500000) : ℝ) = ((500000 / 666571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (405178149 / 1000000000) ≤ -Real.log (333429 / 500000) ∧
    -Real.log (333429 / 500000) ≤ (8103563 / 20000000) := by
  have h := checkLog_sound (w := (166571 / 833429)) (n := 12)
    (lo := (405178149 / 1000000000)) (hi := (8103563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333429) = 1/(333429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-8103563 / 20000000) (-405178149 / 1000000000) (Real.log (333429 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (14929849 / 15625000) ≤ -Real.log (500000000000 / 1299998560001) ∧
    -Real.log (500000000000 / 1299998560001) ≤ (477755169 / 500000000) := by
  have h := checkLog_sound (w := (299998560001 / 2299998560001)) (n := 12)
    (lo := (65590789 / 250000000)) (hi := (262363157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299998560001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1299998560001 / 1000000000000) = 1/(500000000000 / 1299998560001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14929849 / 15625000) (477755169 / 500000000) (Real.log (1299998560001 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1299998560001 / 500000000000) = -Real.log (500000000000 / 1299998560001) := by
    rw [show ((1299998560001 / 500000000000) : ℝ) = ((500000000000 / 1299998560001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (191542923 / 200000000) ≤ -Real.log (500000000000 / 1302867280123) ∧
    -Real.log (500000000000 / 1302867280123) ≤ (957714617 / 1000000000) := by
  have h := checkLog_sound (w := (302867280123 / 2302867280123)) (n := 12)
    (lo := (52913487 / 200000000)) (hi := (66141859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302867280123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1302867280123 / 1000000000000) = 1/(500000000000 / 1302867280123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (191542923 / 200000000) (957714617 / 1000000000) (Real.log (1302867280123 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1302867280123 / 500000000000) = -Real.log (500000000000 / 1302867280123) := by
    rw [show ((1302867280123 / 500000000000) : ℝ) = ((500000000000 / 1302867280123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (172764789 / 250000000) ≤ -Real.log (500000000000 / 997914154539) ∧
    -Real.log (500000000000 / 997914154539) ≤ (691059157 / 1000000000) := by
  have h := checkLog_sound (w := (497914154539 / 1497914154539)) (n := 12)
    (lo := (172764789 / 250000000)) (hi := (691059157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997914154539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997914154539 / 500000000000) = 1/(500000000000 / 997914154539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (172764789 / 250000000) (691059157 / 1000000000) (Real.log (997914154539 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (997914154539 / 500000000000) = -Real.log (500000000000 / 997914154539) := by
    rw [show ((997914154539 / 500000000000) : ℝ) = ((500000000000 / 997914154539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (692716711 / 1000000000) ≤ -Real.log (500000000000 / 999569623519) ∧
    -Real.log (500000000000 / 999569623519) ≤ (86589589 / 125000000) := by
  have h := checkLog_sound (w := (499569623519 / 1499569623519)) (n := 12)
    (lo := (692716711 / 1000000000)) (hi := (86589589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999569623519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999569623519 / 500000000000) = 1/(500000000000 / 999569623519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (692716711 / 1000000000) (86589589 / 125000000) (Real.log (999569623519 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (999569623519 / 500000000000) = -Real.log (500000000000 / 999569623519) := by
    rw [show ((999569623519 / 500000000000) : ℝ) = ((500000000000 / 999569623519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0192
