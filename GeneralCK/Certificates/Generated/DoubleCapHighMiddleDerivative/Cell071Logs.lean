import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell071
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

theorem reflection_log_1_neg : (128168259 / 500000000) ≤ -Real.log (640 / 827) ∧
    -Real.log (640 / 827) ≤ (256336519 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1467)) (n := 12)
    (lo := (128168259 / 500000000)) (hi := (256336519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827 / 640) = 1/(640 / 827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128168259 / 500000000) (256336519 / 1000000000) (Real.log (827 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (827 / 640) = -Real.log (640 / 827) := by
    rw [show ((827 / 640) : ℝ) = ((640 / 827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6911521 / 20000000) ≤ -Real.log (453 / 640) ∧
    -Real.log (453 / 640) ≤ (345576051 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 453) = 1/(453 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345576051 / 1000000000) (-6911521 / 20000000) (Real.log (453 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (255882969 / 1000000000) ≤ -Real.log (5120 / 6613) ∧
    -Real.log (5120 / 6613) ≤ (25588297 / 100000000) := by
  have h := checkLog_sound (w := (1493 / 11733)) (n := 12)
    (lo := (255882969 / 1000000000)) (hi := (25588297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6613 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6613 / 5120) = 1/(5120 / 6613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (255882969 / 1000000000) (25588297 / 100000000) (Real.log (6613 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6613 / 5120) = -Real.log (5120 / 6613) := by
    rw [show ((6613 / 5120) : ℝ) = ((5120 / 6613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172374289 / 500000000) ≤ -Real.log (3627 / 5120) ∧
    -Real.log (3627 / 5120) ≤ (344748579 / 1000000000) := by
  have h := checkLog_sound (w := (1493 / 8747)) (n := 12)
    (lo := (172374289 / 500000000)) (hi := (344748579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3627) = 1/(3627 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-344748579 / 1000000000) (-172374289 / 500000000) (Real.log (3627 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47024129 / 250000000) ≤ -Real.log (20000 / 24139) ∧
    -Real.log (20000 / 24139) ≤ (188096517 / 1000000000) := by
  have h := checkLog_sound (w := (4139 / 44139)) (n := 12)
    (lo := (47024129 / 250000000)) (hi := (188096517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24139 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24139 / 20000) = 1/(20000 / 24139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47024129 / 250000000) (188096517 / 1000000000) (Real.log (24139 / 20000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24139 / 20000) = -Real.log (20000 / 24139) := by
    rw [show ((24139 / 20000) : ℝ) = ((20000 / 24139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (231869007 / 1000000000) ≤ -Real.log (15861 / 20000) ∧
    -Real.log (15861 / 20000) ≤ (14491813 / 62500000) := by
  have h := checkLog_sound (w := (4139 / 35861)) (n := 12)
    (lo := (231869007 / 1000000000)) (hi := (14491813 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15861) = 1/(15861 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14491813 / 62500000) (-231869007 / 1000000000) (Real.log (15861 / 20000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4711111 / 25000000) ≤ -Real.log (100000 / 120737) ∧
    -Real.log (100000 / 120737) ≤ (188444441 / 1000000000) := by
  have h := checkLog_sound (w := (20737 / 220737)) (n := 12)
    (lo := (4711111 / 25000000)) (hi := (188444441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120737 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120737 / 100000) = 1/(100000 / 120737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4711111 / 25000000) (188444441 / 1000000000) (Real.log (120737 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (120737 / 100000) = -Real.log (100000 / 120737) := by
    rw [show ((120737 / 100000) : ℝ) = ((100000 / 120737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58099687 / 250000000) ≤ -Real.log (79263 / 100000) ∧
    -Real.log (79263 / 100000) ≤ (232398749 / 1000000000) := by
  have h := checkLog_sound (w := (20737 / 179263)) (n := 12)
    (lo := (58099687 / 250000000)) (hi := (232398749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 79263) = 1/(79263 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-232398749 / 1000000000) (-58099687 / 250000000) (Real.log (79263 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17262897 / 125000000) ≤ -Real.log (500000 / 574047) ∧
    -Real.log (500000 / 574047) ≤ (138103177 / 1000000000) := by
  have h := checkLog_sound (w := (74047 / 1074047)) (n := 12)
    (lo := (17262897 / 125000000)) (hi := (138103177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574047 / 500000) = 1/(500000 / 574047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17262897 / 125000000) (138103177 / 1000000000) (Real.log (574047 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (574047 / 500000) = -Real.log (500000 / 574047) := by
    rw [show ((574047 / 500000) : ℝ) = ((500000 / 574047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (80139543 / 500000000) ≤ -Real.log (425953 / 500000) ∧
    -Real.log (425953 / 500000) ≤ (160279087 / 1000000000) := by
  have h := checkLog_sound (w := (74047 / 925953)) (n := 12)
    (lo := (80139543 / 500000000)) (hi := (160279087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425953) = 1/(425953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160279087 / 1000000000) (-80139543 / 500000000) (Real.log (425953 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13837141 / 100000000) ≤ -Real.log (500000 / 574201) ∧
    -Real.log (500000 / 574201) ≤ (138371411 / 1000000000) := by
  have h := checkLog_sound (w := (74201 / 1074201)) (n := 12)
    (lo := (13837141 / 100000000)) (hi := (138371411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574201 / 500000) = 1/(500000 / 574201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13837141 / 100000000) (138371411 / 1000000000) (Real.log (574201 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (574201 / 500000) = -Real.log (500000 / 574201) := by
    rw [show ((574201 / 500000) : ℝ) = ((500000 / 574201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80320347 / 500000000) ≤ -Real.log (425799 / 500000) ∧
    -Real.log (425799 / 500000) ≤ (32128139 / 200000000) := by
  have h := checkLog_sound (w := (74201 / 925799)) (n := 12)
    (lo := (80320347 / 500000000)) (hi := (32128139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425799) = 1/(425799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32128139 / 200000000) (-80320347 / 500000000) (Real.log (425799 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150157887 / 250000000) ≤ -Real.log (250000000000 / 455817480011) ∧
    -Real.log (250000000000 / 455817480011) ≤ (600631549 / 1000000000) := by
  have h := checkLog_sound (w := (205817480011 / 705817480011)) (n := 12)
    (lo := (150157887 / 250000000)) (hi := (600631549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455817480011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455817480011 / 250000000000) = 1/(250000000000 / 455817480011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150157887 / 250000000) (600631549 / 1000000000) (Real.log (455817480011 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (455817480011 / 250000000000) = -Real.log (250000000000 / 455817480011) := by
    rw [show ((455817480011 / 250000000000) : ℝ) = ((250000000000 / 455817480011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601912569 / 1000000000) ≤ -Real.log (500000000000 / 912803532009) ∧
    -Real.log (500000000000 / 912803532009) ≤ (60191257 / 100000000) := by
  have h := checkLog_sound (w := (412803532009 / 1412803532009)) (n := 12)
    (lo := (601912569 / 1000000000)) (hi := (60191257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912803532009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912803532009 / 500000000000) = 1/(500000000000 / 912803532009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (601912569 / 1000000000) (60191257 / 100000000) (Real.log (912803532009 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (912803532009 / 500000000000) = -Real.log (500000000000 / 912803532009) := by
    rw [show ((912803532009 / 500000000000) : ℝ) = ((500000000000 / 912803532009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (419965523 / 1000000000) ≤ -Real.log (125000000000 / 190238635647) ∧
    -Real.log (125000000000 / 190238635647) ≤ (104991381 / 250000000) := by
  have h := checkLog_sound (w := (65238635647 / 315238635647)) (n := 12)
    (lo := (419965523 / 1000000000)) (hi := (104991381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190238635647 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190238635647 / 125000000000) = 1/(125000000000 / 190238635647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (419965523 / 1000000000) (104991381 / 250000000) (Real.log (190238635647 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (190238635647 / 125000000000) = -Real.log (125000000000 / 190238635647) := by
    rw [show ((190238635647 / 125000000000) : ℝ) = ((125000000000 / 190238635647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (420843189 / 1000000000) ≤ -Real.log (125000000000 / 190405674779) ∧
    -Real.log (125000000000 / 190405674779) ≤ (42084319 / 100000000) := by
  have h := checkLog_sound (w := (65405674779 / 315405674779)) (n := 12)
    (lo := (420843189 / 1000000000)) (hi := (42084319 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190405674779 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190405674779 / 125000000000) = 1/(125000000000 / 190405674779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (420843189 / 1000000000) (42084319 / 100000000) (Real.log (190405674779 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (190405674779 / 125000000000) = -Real.log (125000000000 / 190405674779) := by
    rw [show ((190405674779 / 125000000000) : ℝ) = ((125000000000 / 190405674779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (149191131 / 500000000) ≤ -Real.log (500000000000 / 673838428183) ∧
    -Real.log (500000000000 / 673838428183) ≤ (298382263 / 1000000000) := by
  have h := checkLog_sound (w := (173838428183 / 1173838428183)) (n := 12)
    (lo := (149191131 / 500000000)) (hi := (298382263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673838428183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673838428183 / 500000000000) = 1/(500000000000 / 673838428183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (149191131 / 500000000) (298382263 / 1000000000) (Real.log (673838428183 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (673838428183 / 500000000000) = -Real.log (500000000000 / 673838428183) := by
    rw [show ((673838428183 / 500000000000) : ℝ) = ((500000000000 / 673838428183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59802421 / 200000000) ≤ -Real.log (100000000000 / 134852594769) ∧
    -Real.log (100000000000 / 134852594769) ≤ (149506053 / 500000000) := by
  have h := checkLog_sound (w := (34852594769 / 234852594769)) (n := 12)
    (lo := (59802421 / 200000000)) (hi := (149506053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134852594769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134852594769 / 100000000000) = 1/(100000000000 / 134852594769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59802421 / 200000000) (149506053 / 500000000) (Real.log (134852594769 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (134852594769 / 100000000000) = -Real.log (100000000000 / 134852594769) := by
    rw [show ((134852594769 / 100000000000) : ℝ) = ((100000000000 / 134852594769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22269283 / 1000000000) ≤ -Real.log (244494211599 / 250000000000) ∧
    -Real.log (244494211599 / 250000000000) ≤ (5567321 / 250000000) := by
  have h := checkLog_sound (w := (5505788401 / 494494211599)) (n := 12)
    (lo := (22269283 / 1000000000)) (hi := (5567321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244494211599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244494211599) = 1/(244494211599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5567321 / 250000000) (-22269283 / 1000000000) (Real.log (244494211599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2217591 / 100000000) ≤ -Real.log (244517041791 / 250000000000) ∧
    -Real.log (244517041791 / 250000000000) ≤ (22175911 / 1000000000) := by
  have h := checkLog_sound (w := (5482958209 / 494517041791)) (n := 12)
    (lo := (2217591 / 100000000)) (hi := (22175911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244517041791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244517041791) = 1/(244517041791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22175911 / 1000000000) (-2217591 / 100000000) (Real.log (244517041791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell071
