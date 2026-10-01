import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell055
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

theorem reflection_log_1_neg : (249054933 / 1000000000) ≤ -Real.log (640 / 821) ∧
    -Real.log (640 / 821) ≤ (124527467 / 500000000) := by
  have h := checkLog_sound (w := (181 / 1461)) (n := 12)
    (lo := (249054933 / 1000000000)) (hi := (124527467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821 / 640) = 1/(640 / 821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (249054933 / 1000000000) (124527467 / 500000000) (Real.log (821 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (821 / 640) = -Real.log (640 / 821) := by
    rw [show ((821 / 640) : ℝ) = ((640 / 821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (166208983 / 500000000) ≤ -Real.log (459 / 640) ∧
    -Real.log (459 / 640) ≤ (332417967 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 459) = 1/(459 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332417967 / 1000000000) (-166208983 / 500000000) (Real.log (459 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62149517 / 250000000) ≤ -Real.log (1024 / 1313) ∧
    -Real.log (1024 / 1313) ≤ (248598069 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2337)) (n := 12)
    (lo := (62149517 / 250000000)) (hi := (248598069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1024) = 1/(1024 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62149517 / 250000000) (248598069 / 1000000000) (Real.log (1313 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1313 / 1024) = -Real.log (1024 / 1313) := by
    rw [show ((1313 / 1024) : ℝ) = ((1024 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165800653 / 500000000) ≤ -Real.log (735 / 1024) ∧
    -Real.log (735 / 1024) ≤ (331601307 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1759)) (n := 12)
    (lo := (165800653 / 500000000)) (hi := (331601307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 735) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 735) = 1/(735 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-331601307 / 1000000000) (-165800653 / 500000000) (Real.log (735 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36505807 / 200000000) ≤ -Real.log (1000000 / 1200249) ∧
    -Real.log (1000000 / 1200249) ≤ (45632259 / 250000000) := by
  have h := checkLog_sound (w := (200249 / 2200249)) (n := 12)
    (lo := (36505807 / 200000000)) (hi := (45632259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200249 / 1000000) = 1/(1000000 / 1200249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36505807 / 200000000) (45632259 / 250000000) (Real.log (1200249 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1200249 / 1000000) = -Real.log (1000000 / 1200249) := by
    rw [show ((1200249 / 1000000) : ℝ) = ((1000000 / 1200249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (223454849 / 1000000000) ≤ -Real.log (799751 / 1000000) ∧
    -Real.log (799751 / 1000000) ≤ (4469097 / 20000000) := by
  have h := checkLog_sound (w := (200249 / 1799751)) (n := 12)
    (lo := (223454849 / 1000000000)) (hi := (4469097 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799751) = 1/(799751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4469097 / 20000000) (-223454849 / 1000000000) (Real.log (799751 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (182878901 / 1000000000) ≤ -Real.log (1000000 / 1200669) ∧
    -Real.log (1000000 / 1200669) ≤ (91439451 / 500000000) := by
  have h := checkLog_sound (w := (200669 / 2200669)) (n := 12)
    (lo := (182878901 / 1000000000)) (hi := (91439451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200669 / 1000000) = 1/(1000000 / 1200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (182878901 / 1000000000) (91439451 / 500000000) (Real.log (1200669 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1200669 / 1000000) = -Real.log (1000000 / 1200669) := by
    rw [show ((1200669 / 1000000) : ℝ) = ((1000000 / 1200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (223980151 / 1000000000) ≤ -Real.log (799331 / 1000000) ∧
    -Real.log (799331 / 1000000) ≤ (27997519 / 125000000) := by
  have h := checkLog_sound (w := (200669 / 1799331)) (n := 12)
    (lo := (223980151 / 1000000000)) (hi := (27997519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799331) = 1/(799331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-27997519 / 125000000) (-223980151 / 1000000000) (Real.log (799331 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5352869 / 40000000) ≤ -Real.log (1000000 / 1143189) ∧
    -Real.log (1000000 / 1143189) ≤ (66910863 / 500000000) := by
  have h := checkLog_sound (w := (143189 / 2143189)) (n := 12)
    (lo := (5352869 / 40000000)) (hi := (66910863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143189 / 1000000) = 1/(1000000 / 1143189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5352869 / 40000000) (66910863 / 500000000) (Real.log (1143189 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1143189 / 1000000) = -Real.log (1000000 / 1143189) := by
    rw [show ((1143189 / 1000000) : ℝ) = ((1000000 / 1143189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (154537921 / 1000000000) ≤ -Real.log (856811 / 1000000) ∧
    -Real.log (856811 / 1000000) ≤ (77268961 / 500000000) := by
  have h := checkLog_sound (w := (143189 / 1856811)) (n := 12)
    (lo := (154537921 / 1000000000)) (hi := (77268961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856811) = 1/(856811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77268961 / 500000000) (-154537921 / 1000000000) (Real.log (856811 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33522559 / 250000000) ≤ -Real.log (125000 / 142937) ∧
    -Real.log (125000 / 142937) ≤ (134090237 / 1000000000) := by
  have h := checkLog_sound (w := (17937 / 267937)) (n := 12)
    (lo := (33522559 / 250000000)) (hi := (134090237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142937 / 125000) = 1/(125000 / 142937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33522559 / 250000000) (134090237 / 1000000000) (Real.log (142937 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142937 / 125000) = -Real.log (125000 / 142937) := by
    rw [show ((142937 / 125000) : ℝ) = ((125000 / 142937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (154896291 / 1000000000) ≤ -Real.log (107063 / 125000) ∧
    -Real.log (107063 / 125000) ≤ (38724073 / 250000000) := by
  have h := checkLog_sound (w := (17937 / 232063)) (n := 12)
    (lo := (154896291 / 1000000000)) (hi := (38724073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107063) = 1/(107063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38724073 / 250000000) (-154896291 / 1000000000) (Real.log (107063 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (928319 / 1600000) ≤ -Real.log (500000000000 / 893197278911) ∧
    -Real.log (500000000000 / 893197278911) ≤ (36262461 / 62500000) := by
  have h := checkLog_sound (w := (393197278911 / 1393197278911)) (n := 12)
    (lo := (928319 / 1600000)) (hi := (36262461 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893197278911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893197278911 / 500000000000) = 1/(500000000000 / 893197278911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (928319 / 1600000) (36262461 / 62500000) (Real.log (893197278911 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (893197278911 / 500000000000) = -Real.log (500000000000 / 893197278911) := by
    rw [show ((893197278911 / 500000000000) : ℝ) = ((500000000000 / 893197278911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (581472899 / 1000000000) ≤ -Real.log (500000000000 / 894335511983) ∧
    -Real.log (500000000000 / 894335511983) ≤ (5814729 / 10000000) := by
  have h := checkLog_sound (w := (394335511983 / 1394335511983)) (n := 12)
    (lo := (581472899 / 1000000000)) (hi := (5814729 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894335511983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894335511983 / 500000000000) = 1/(500000000000 / 894335511983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (581472899 / 1000000000) (5814729 / 10000000) (Real.log (894335511983 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (894335511983 / 500000000000) = -Real.log (500000000000 / 894335511983) := by
    rw [show ((894335511983 / 500000000000) : ℝ) = ((500000000000 / 894335511983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (81196777 / 200000000) ≤ -Real.log (500000000000 / 750389183633) ∧
    -Real.log (500000000000 / 750389183633) ≤ (202991943 / 500000000) := by
  have h := checkLog_sound (w := (250389183633 / 1250389183633)) (n := 12)
    (lo := (81196777 / 200000000)) (hi := (202991943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750389183633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750389183633 / 500000000000) = 1/(500000000000 / 750389183633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (81196777 / 200000000) (202991943 / 500000000) (Real.log (750389183633 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (750389183633 / 500000000000) = -Real.log (500000000000 / 750389183633) := by
    rw [show ((750389183633 / 500000000000) : ℝ) = ((500000000000 / 750389183633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101714763 / 250000000) ≤ -Real.log (4000000000 / 6008369499) ∧
    -Real.log (4000000000 / 6008369499) ≤ (406859053 / 1000000000) := by
  have h := checkLog_sound (w := (2008369499 / 10008369499)) (n := 12)
    (lo := (101714763 / 250000000)) (hi := (406859053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6008369499 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6008369499 / 4000000000) = 1/(4000000000 / 6008369499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101714763 / 250000000) (406859053 / 1000000000) (Real.log (6008369499 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6008369499 / 4000000000) = -Real.log (4000000000 / 6008369499) := by
    rw [show ((6008369499 / 4000000000) : ℝ) = ((4000000000 / 6008369499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (144179823 / 500000000) ≤ -Real.log (500000000000 / 667118536059) ∧
    -Real.log (500000000000 / 667118536059) ≤ (288359647 / 1000000000) := by
  have h := checkLog_sound (w := (167118536059 / 1167118536059)) (n := 12)
    (lo := (144179823 / 500000000)) (hi := (288359647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667118536059 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667118536059 / 500000000000) = 1/(500000000000 / 667118536059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (144179823 / 500000000) (288359647 / 1000000000) (Real.log (667118536059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667118536059 / 500000000000) = -Real.log (500000000000 / 667118536059) := by
    rw [show ((667118536059 / 500000000000) : ℝ) = ((500000000000 / 667118536059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (288986527 / 1000000000) ≤ -Real.log (100000000000 / 133507374163) ∧
    -Real.log (100000000000 / 133507374163) ≤ (9030829 / 31250000) := by
  have h := checkLog_sound (w := (33507374163 / 233507374163)) (n := 12)
    (lo := (288986527 / 1000000000)) (hi := (9030829 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133507374163 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133507374163 / 100000000000) = 1/(100000000000 / 133507374163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (288986527 / 1000000000) (9030829 / 31250000) (Real.log (133507374163 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (133507374163 / 100000000000) = -Real.log (100000000000 / 133507374163) := by
    rw [show ((133507374163 / 100000000000) : ℝ) = ((100000000000 / 133507374163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10403027 / 500000000) ≤ -Real.log (15303264031 / 15625000000) ∧
    -Real.log (15303264031 / 15625000000) ≤ (4161211 / 200000000) := by
  have h := checkLog_sound (w := (321735969 / 30928264031)) (n := 12)
    (lo := (10403027 / 500000000)) (hi := (4161211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15303264031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15303264031) = 1/(15303264031 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4161211 / 200000000) (-10403027 / 500000000) (Real.log (15303264031 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4143239 / 200000000) ≤ -Real.log (979496910279 / 1000000000000) ∧
    -Real.log (979496910279 / 1000000000000) ≤ (5179049 / 250000000) := by
  have h := checkLog_sound (w := (20503089721 / 1979496910279)) (n := 12)
    (lo := (4143239 / 200000000)) (hi := (5179049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979496910279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979496910279) = 1/(979496910279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5179049 / 250000000) (-4143239 / 200000000) (Real.log (979496910279 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell055
