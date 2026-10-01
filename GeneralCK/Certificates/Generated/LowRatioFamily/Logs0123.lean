import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7872_neg : (125015753 / 1000000000) ≤ -Real.log (882483 / 1000000) ∧
    -Real.log (882483 / 1000000) ≤ (62507877 / 500000000) := by
  have h := checkLog_sound (w := (117517 / 1882483)) (n := 12)
    (lo := (125015753 / 1000000000)) (hi := (62507877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882483) = 1/(882483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7872 : Bounds (-62507877 / 500000000) (-125015753 / 1000000000) (Real.log (882483 / 1000000)) := by
  have h := reflection_log_7872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7873_neg : (13906493 / 1000000000) ≤ -Real.log (986189754711 / 1000000000000) ∧
    -Real.log (986189754711 / 1000000000000) ≤ (6953247 / 500000000) := by
  have h := checkLog_sound (w := (13810245289 / 1986189754711)) (n := 12)
    (lo := (13906493 / 1000000000)) (hi := (6953247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986189754711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986189754711) = 1/(986189754711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7873 : Bounds (-6953247 / 500000000) (-13906493 / 1000000000) (Real.log (986189754711 / 1000000000000)) := by
  have h := reflection_log_7873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7874_neg : (13790439 / 1000000000) ≤ -Real.log (986304213159 / 1000000000000) ∧
    -Real.log (986304213159 / 1000000000000) ≤ (344761 / 25000000) := by
  have h := checkLog_sound (w := (13695786841 / 1986304213159)) (n := 12)
    (lo := (13790439 / 1000000000)) (hi := (344761 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986304213159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986304213159) = 1/(986304213159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7874 : Bounds (-344761 / 25000000) (-13790439 / 1000000000) (Real.log (986304213159 / 1000000000000)) := by
  have h := reflection_log_7874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7875_neg : (235135403 / 1000000000) ≤ -Real.log (100000000000 / 126508005359) ∧
    -Real.log (100000000000 / 126508005359) ≤ (58783851 / 250000000) := by
  have h := checkLog_sound (w := (26508005359 / 226508005359)) (n := 12)
    (lo := (235135403 / 1000000000)) (hi := (58783851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126508005359 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126508005359 / 100000000000) = 1/(100000000000 / 126508005359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7875 : Bounds (235135403 / 1000000000) (58783851 / 250000000) (Real.log (126508005359 / 100000000000)) := by
  have h := reflection_log_7875_neg
  have he : Real.log (126508005359 / 100000000000) = -Real.log (100000000000 / 126508005359) := by
    rw [show ((126508005359 / 100000000000) : ℝ) = ((100000000000 / 126508005359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7876_neg : (236125013 / 1000000000) ≤ -Real.log (500000000000 / 633166304621) ∧
    -Real.log (500000000000 / 633166304621) ≤ (118062507 / 500000000) := by
  have h := checkLog_sound (w := (133166304621 / 1133166304621)) (n := 12)
    (lo := (236125013 / 1000000000)) (hi := (118062507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633166304621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633166304621 / 500000000000) = 1/(500000000000 / 633166304621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7876 : Bounds (236125013 / 1000000000) (118062507 / 500000000) (Real.log (633166304621 / 500000000000)) := by
  have h := reflection_log_7876_neg
  have he : Real.log (633166304621 / 500000000000) = -Real.log (500000000000 / 633166304621) := by
    rw [show ((633166304621 / 500000000000) : ℝ) = ((500000000000 / 633166304621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7877_neg : (47260441 / 100000000) ≤ -Real.log (500000000000 / 802083333333) ∧
    -Real.log (500000000000 / 802083333333) ≤ (472604411 / 1000000000) := by
  have h := checkLog_sound (w := (302083333333 / 1302083333333)) (n := 12)
    (lo := (47260441 / 100000000)) (hi := (472604411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802083333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802083333333 / 500000000000) = 1/(500000000000 / 802083333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7877 : Bounds (47260441 / 100000000) (472604411 / 1000000000) (Real.log (802083333333 / 500000000000)) := by
  have h := reflection_log_7877_neg
  have he : Real.log (802083333333 / 500000000000) = -Real.log (500000000000 / 802083333333) := by
    rw [show ((802083333333 / 500000000000) : ℝ) = ((500000000000 / 802083333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7878_neg : (236830713 / 500000000) ≤ -Real.log (125000000000 / 200732899023) ∧
    -Real.log (125000000000 / 200732899023) ≤ (473661427 / 1000000000) := by
  have h := checkLog_sound (w := (75732899023 / 325732899023)) (n := 12)
    (lo := (236830713 / 500000000)) (hi := (473661427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200732899023 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200732899023 / 125000000000) = 1/(125000000000 / 200732899023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7878 : Bounds (236830713 / 500000000) (473661427 / 1000000000) (Real.log (200732899023 / 125000000000)) := by
  have h := reflection_log_7878_neg
  have he : Real.log (200732899023 / 125000000000) = -Real.log (125000000000 / 200732899023) := by
    rw [show ((200732899023 / 125000000000) : ℝ) = ((125000000000 / 200732899023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7879_neg : (13090639 / 62500000) ≤ -Real.log (1000 / 1233) ∧
    -Real.log (1000 / 1233) ≤ (8378009 / 40000000) := by
  have h := checkLog_sound (w := (233 / 2233)) (n := 12)
    (lo := (13090639 / 62500000)) (hi := (8378009 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1000) = 1/(1000 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7879 : Bounds (13090639 / 62500000) (8378009 / 40000000) (Real.log (1233 / 1000)) := by
  have h := reflection_log_7879_neg
  have he : Real.log (1233 / 1000) = -Real.log (1000 / 1233) := by
    rw [show ((1233 / 1000) : ℝ) = ((1000 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7880_neg : (265268477 / 1000000000) ≤ -Real.log (767 / 1000) ∧
    -Real.log (767 / 1000) ≤ (132634239 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1767)) (n := 12)
    (lo := (265268477 / 1000000000)) (hi := (132634239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 767) = 1/(767 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7880 : Bounds (-132634239 / 500000000) (-265268477 / 1000000000) (Real.log (767 / 1000)) := by
  have h := reflection_log_7880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7881_neg : (58243 / 250000000) ≤ -Real.log (1000000 / 1000233) ∧
    -Real.log (1000000 / 1000233) ≤ (232973 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2000233)) (n := 12)
    (lo := (58243 / 250000000)) (hi := (232973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000233 / 1000000) = 1/(1000000 / 1000233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7881 : Bounds (58243 / 250000000) (232973 / 1000000000) (Real.log (1000233 / 1000000)) := by
  have h := reflection_log_7881_neg
  have he : Real.log (1000233 / 1000000) = -Real.log (1000000 / 1000233) := by
    rw [show ((1000233 / 1000000) : ℝ) = ((1000000 / 1000233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7882_neg : (233027 / 1000000000) ≤ -Real.log (999767 / 1000000) ∧
    -Real.log (999767 / 1000000) ≤ (58257 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1999767)) (n := 12)
    (lo := (233027 / 1000000000)) (hi := (58257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999767) = 1/(999767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7882 : Bounds (-58257 / 250000000) (-233027 / 1000000000) (Real.log (999767 / 1000000)) := by
  have h := reflection_log_7882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7883_neg : (11090253 / 100000000) ≤ -Real.log (500000 / 558643) ∧
    -Real.log (500000 / 558643) ≤ (110902531 / 1000000000) := by
  have h := checkLog_sound (w := (58643 / 1058643)) (n := 12)
    (lo := (11090253 / 100000000)) (hi := (110902531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558643 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558643 / 500000) = 1/(500000 / 558643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7883 : Bounds (11090253 / 100000000) (110902531 / 1000000000) (Real.log (558643 / 500000)) := by
  have h := reflection_log_7883_neg
  have he : Real.log (558643 / 500000) = -Real.log (500000 / 558643) := by
    rw [show ((558643 / 500000) : ℝ) = ((500000 / 558643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7884_neg : (62377013 / 500000000) ≤ -Real.log (441357 / 500000) ∧
    -Real.log (441357 / 500000) ≤ (124754027 / 1000000000) := by
  have h := checkLog_sound (w := (58643 / 941357)) (n := 12)
    (lo := (62377013 / 500000000)) (hi := (124754027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441357) = 1/(441357 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7884 : Bounds (-124754027 / 1000000000) (-62377013 / 500000000) (Real.log (441357 / 500000)) := by
  have h := reflection_log_7884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7885_neg : (55670051 / 500000000) ≤ -Real.log (40000 / 44711) ∧
    -Real.log (40000 / 44711) ≤ (111340103 / 1000000000) := by
  have h := checkLog_sound (w := (4711 / 84711)) (n := 12)
    (lo := (55670051 / 500000000)) (hi := (111340103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44711 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44711 / 40000) = 1/(40000 / 44711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7885 : Bounds (55670051 / 500000000) (111340103 / 1000000000) (Real.log (44711 / 40000)) := by
  have h := reflection_log_7885_neg
  have he : Real.log (44711 / 40000) = -Real.log (40000 / 44711) := by
    rw [show ((44711 / 40000) : ℝ) = ((40000 / 44711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7886_neg : (125308153 / 1000000000) ≤ -Real.log (35289 / 40000) ∧
    -Real.log (35289 / 40000) ≤ (62654077 / 500000000) := by
  have h := checkLog_sound (w := (4711 / 75289)) (n := 12)
    (lo := (125308153 / 1000000000)) (hi := (62654077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 35289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 35289) = 1/(35289 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7886 : Bounds (-62654077 / 500000000) (-125308153 / 1000000000) (Real.log (35289 / 40000)) := by
  have h := reflection_log_7886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7887_neg : (13968051 / 1000000000) ≤ -Real.log (1577806479 / 1600000000) ∧
    -Real.log (1577806479 / 1600000000) ≤ (3492013 / 250000000) := by
  have h := checkLog_sound (w := (22193521 / 3177806479)) (n := 12)
    (lo := (13968051 / 1000000000)) (hi := (3492013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1577806479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1577806479) = 1/(1577806479 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7887 : Bounds (-3492013 / 250000000) (-13968051 / 1000000000) (Real.log (1577806479 / 1600000000)) := by
  have h := reflection_log_7887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7888_neg : (1731437 / 125000000) ≤ -Real.log (246560998551 / 250000000000) ∧
    -Real.log (246560998551 / 250000000000) ≤ (13851497 / 1000000000) := by
  have h := checkLog_sound (w := (3439001449 / 496560998551)) (n := 12)
    (lo := (1731437 / 125000000)) (hi := (13851497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246560998551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246560998551) = 1/(246560998551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7888 : Bounds (-13851497 / 1000000000) (-1731437 / 125000000) (Real.log (246560998551 / 250000000000)) := by
  have h := reflection_log_7888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7889_neg : (58914139 / 250000000) ≤ -Real.log (250000000000 / 316434881513) ∧
    -Real.log (250000000000 / 316434881513) ≤ (235656557 / 1000000000) := by
  have h := checkLog_sound (w := (66434881513 / 566434881513)) (n := 12)
    (lo := (58914139 / 250000000)) (hi := (235656557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316434881513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316434881513 / 250000000000) = 1/(250000000000 / 316434881513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7889 : Bounds (58914139 / 250000000) (235656557 / 1000000000) (Real.log (316434881513 / 250000000000)) := by
  have h := reflection_log_7889_neg
  have he : Real.log (316434881513 / 250000000000) = -Real.log (250000000000 / 316434881513) := by
    rw [show ((316434881513 / 250000000000) : ℝ) = ((250000000000 / 316434881513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7890_neg : (47329651 / 200000000) ≤ -Real.log (500000000000 / 633497690499) ∧
    -Real.log (500000000000 / 633497690499) ≤ (3697629 / 15625000) := by
  have h := checkLog_sound (w := (133497690499 / 1133497690499)) (n := 12)
    (lo := (47329651 / 200000000)) (hi := (3697629 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633497690499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633497690499 / 500000000000) = 1/(500000000000 / 633497690499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7890 : Bounds (47329651 / 200000000) (3697629 / 15625000) (Real.log (633497690499 / 500000000000)) := by
  have h := reflection_log_7890_neg
  have he : Real.log (633497690499 / 500000000000) = -Real.log (500000000000 / 633497690499) := by
    rw [show ((633497690499 / 500000000000) : ℝ) = ((500000000000 / 633497690499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7891_neg : (236830713 / 500000000) ≤ -Real.log (500000000000 / 802931596091) ∧
    -Real.log (500000000000 / 802931596091) ≤ (473661427 / 1000000000) := by
  have h := checkLog_sound (w := (302931596091 / 1302931596091)) (n := 12)
    (lo := (236830713 / 500000000)) (hi := (473661427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802931596091 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802931596091 / 500000000000) = 1/(500000000000 / 802931596091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7891 : Bounds (236830713 / 500000000) (473661427 / 1000000000) (Real.log (802931596091 / 500000000000)) := by
  have h := reflection_log_7891_neg
  have he : Real.log (802931596091 / 500000000000) = -Real.log (500000000000 / 802931596091) := by
    rw [show ((802931596091 / 500000000000) : ℝ) = ((500000000000 / 802931596091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7892_neg : (474718701 / 1000000000) ≤ -Real.log (250000000000 / 401890482399) ∧
    -Real.log (250000000000 / 401890482399) ≤ (237359351 / 500000000) := by
  have h := checkLog_sound (w := (151890482399 / 651890482399)) (n := 12)
    (lo := (474718701 / 1000000000)) (hi := (237359351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401890482399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401890482399 / 250000000000) = 1/(250000000000 / 401890482399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7892 : Bounds (474718701 / 1000000000) (237359351 / 500000000) (Real.log (401890482399 / 250000000000)) := by
  have h := reflection_log_7892_neg
  have he : Real.log (401890482399 / 250000000000) = -Real.log (250000000000 / 401890482399) := by
    rw [show ((401890482399 / 250000000000) : ℝ) = ((250000000000 / 401890482399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7893_neg : (26231957 / 125000000) ≤ -Real.log (2000 / 2467) ∧
    -Real.log (2000 / 2467) ≤ (209855657 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 4467)) (n := 12)
    (lo := (26231957 / 125000000)) (hi := (209855657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 2000) = 1/(2000 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7893 : Bounds (26231957 / 125000000) (209855657 / 1000000000) (Real.log (2467 / 2000)) := by
  have h := reflection_log_7893_neg
  have he : Real.log (2467 / 2000) = -Real.log (2000 / 2467) := by
    rw [show ((2467 / 2000) : ℝ) = ((2000 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7894_neg : (13296029 / 50000000) ≤ -Real.log (1533 / 2000) ∧
    -Real.log (1533 / 2000) ≤ (265920581 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 3533)) (n := 12)
    (lo := (13296029 / 50000000)) (hi := (265920581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1533) = 1/(1533 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7894 : Bounds (-265920581 / 1000000000) (-13296029 / 50000000) (Real.log (1533 / 2000)) := by
  have h := reflection_log_7894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7895_neg : (456 / 1953125) ≤ -Real.log (2000000 / 2000467) ∧
    -Real.log (2000000 / 2000467) ≤ (233473 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 4000467)) (n := 12)
    (lo := (456 / 1953125)) (hi := (233473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000467 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000467 / 2000000) = 1/(2000000 / 2000467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7895 : Bounds (456 / 1953125) (233473 / 1000000000) (Real.log (2000467 / 2000000)) := by
  have h := reflection_log_7895_neg
  have he : Real.log (2000467 / 2000000) = -Real.log (2000000 / 2000467) := by
    rw [show ((2000467 / 2000000) : ℝ) = ((2000000 / 2000467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7896_neg : (233527 / 1000000000) ≤ -Real.log (1999533 / 2000000) ∧
    -Real.log (1999533 / 2000000) ≤ (29191 / 125000000) := by
  have h := checkLog_sound (w := (467 / 3999533)) (n := 12)
    (lo := (233527 / 1000000000)) (hi := (29191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999533) = 1/(1999533 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7896 : Bounds (-29191 / 125000000) (-233527 / 1000000000) (Real.log (1999533 / 2000000)) := by
  have h := reflection_log_7896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7897_neg : (4445301 / 40000000) ≤ -Real.log (1000000 / 1117543) ∧
    -Real.log (1000000 / 1117543) ≤ (55566263 / 500000000) := by
  have h := checkLog_sound (w := (117543 / 2117543)) (n := 12)
    (lo := (4445301 / 40000000)) (hi := (55566263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117543 / 1000000) = 1/(1000000 / 1117543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7897 : Bounds (4445301 / 40000000) (55566263 / 500000000) (Real.log (1117543 / 1000000)) := by
  have h := reflection_log_7897_neg
  have he : Real.log (1117543 / 1000000) = -Real.log (1000000 / 1117543) := by
    rw [show ((1117543 / 1000000) : ℝ) = ((1000000 / 1117543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7898_neg : (3907663 / 31250000) ≤ -Real.log (882457 / 1000000) ∧
    -Real.log (882457 / 1000000) ≤ (125045217 / 1000000000) := by
  have h := checkLog_sound (w := (117543 / 1882457)) (n := 12)
    (lo := (3907663 / 31250000)) (hi := (125045217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882457) = 1/(882457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7898 : Bounds (-125045217 / 1000000000) (-3907663 / 31250000) (Real.log (882457 / 1000000)) := by
  have h := reflection_log_7898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7899_neg : (111570891 / 1000000000) ≤ -Real.log (1000000 / 1118033) ∧
    -Real.log (1000000 / 1118033) ≤ (27892723 / 250000000) := by
  have h := checkLog_sound (w := (118033 / 2118033)) (n := 12)
    (lo := (111570891 / 1000000000)) (hi := (27892723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118033 / 1000000) = 1/(1000000 / 1118033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7899 : Bounds (111570891 / 1000000000) (27892723 / 250000000) (Real.log (1118033 / 1000000)) := by
  have h := reflection_log_7899_neg
  have he : Real.log (1118033 / 1000000) = -Real.log (1000000 / 1118033) := by
    rw [show ((1118033 / 1000000) : ℝ) = ((1000000 / 1118033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7900_neg : (62800319 / 500000000) ≤ -Real.log (881967 / 1000000) ∧
    -Real.log (881967 / 1000000) ≤ (125600639 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 1881967)) (n := 12)
    (lo := (62800319 / 500000000)) (hi := (125600639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881967) = 1/(881967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7900 : Bounds (-125600639 / 1000000000) (-62800319 / 500000000) (Real.log (881967 / 1000000)) := by
  have h := reflection_log_7900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7901_neg : (14029747 / 1000000000) ≤ -Real.log (986068210911 / 1000000000000) ∧
    -Real.log (986068210911 / 1000000000000) ≤ (3507437 / 250000000) := by
  have h := checkLog_sound (w := (13931789089 / 1986068210911)) (n := 12)
    (lo := (14029747 / 1000000000)) (hi := (3507437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986068210911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986068210911) = 1/(986068210911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7901 : Bounds (-3507437 / 250000000) (-14029747 / 1000000000) (Real.log (986068210911 / 1000000000000)) := by
  have h := reflection_log_7901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7902_neg : (13912691 / 1000000000) ≤ -Real.log (986183643151 / 1000000000000) ∧
    -Real.log (986183643151 / 1000000000000) ≤ (3478173 / 250000000) := by
  have h := checkLog_sound (w := (13816356849 / 1986183643151)) (n := 12)
    (lo := (13912691 / 1000000000)) (hi := (3478173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986183643151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986183643151) = 1/(986183643151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7902 : Bounds (-3478173 / 250000000) (-13912691 / 1000000000) (Real.log (986183643151 / 1000000000000)) := by
  have h := reflection_log_7902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7903_neg : (118088871 / 500000000) ≤ -Real.log (125000000000 / 158299922829) ∧
    -Real.log (125000000000 / 158299922829) ≤ (236177743 / 1000000000) := by
  have h := checkLog_sound (w := (33299922829 / 283299922829)) (n := 12)
    (lo := (118088871 / 500000000)) (hi := (236177743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158299922829 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158299922829 / 125000000000) = 1/(125000000000 / 158299922829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7903 : Bounds (118088871 / 500000000) (236177743 / 1000000000) (Real.log (158299922829 / 125000000000)) := by
  have h := reflection_log_7903_neg
  have he : Real.log (158299922829 / 125000000000) = -Real.log (125000000000 / 158299922829) := by
    rw [show ((158299922829 / 125000000000) : ℝ) = ((125000000000 / 158299922829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7904_neg : (237171529 / 1000000000) ≤ -Real.log (500000000000 / 633829270257) ∧
    -Real.log (500000000000 / 633829270257) ≤ (23717153 / 100000000) := by
  have h := checkLog_sound (w := (133829270257 / 1133829270257)) (n := 12)
    (lo := (237171529 / 1000000000)) (hi := (23717153 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633829270257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633829270257 / 500000000000) = 1/(500000000000 / 633829270257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7904 : Bounds (237171529 / 1000000000) (23717153 / 100000000) (Real.log (633829270257 / 500000000000)) := by
  have h := reflection_log_7904_neg
  have he : Real.log (633829270257 / 500000000000) = -Real.log (500000000000 / 633829270257) := by
    rw [show ((633829270257 / 500000000000) : ℝ) = ((500000000000 / 633829270257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7905_neg : (474718701 / 1000000000) ≤ -Real.log (500000000000 / 803780964797) ∧
    -Real.log (500000000000 / 803780964797) ≤ (237359351 / 500000000) := by
  have h := checkLog_sound (w := (303780964797 / 1303780964797)) (n := 12)
    (lo := (474718701 / 1000000000)) (hi := (237359351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803780964797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803780964797 / 500000000000) = 1/(500000000000 / 803780964797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7905 : Bounds (474718701 / 1000000000) (237359351 / 500000000) (Real.log (803780964797 / 500000000000)) := by
  have h := reflection_log_7905_neg
  have he : Real.log (803780964797 / 500000000000) = -Real.log (500000000000 / 803780964797) := by
    rw [show ((803780964797 / 500000000000) : ℝ) = ((500000000000 / 803780964797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7906_neg : (475776237 / 1000000000) ≤ -Real.log (250000000000 / 402315720809) ∧
    -Real.log (250000000000 / 402315720809) ≤ (237888119 / 500000000) := by
  have h := checkLog_sound (w := (152315720809 / 652315720809)) (n := 12)
    (lo := (475776237 / 1000000000)) (hi := (237888119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402315720809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402315720809 / 250000000000) = 1/(250000000000 / 402315720809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7906 : Bounds (475776237 / 1000000000) (237888119 / 500000000) (Real.log (402315720809 / 250000000000)) := by
  have h := reflection_log_7906_neg
  have he : Real.log (402315720809 / 250000000000) = -Real.log (250000000000 / 402315720809) := by
    rw [show ((402315720809 / 250000000000) : ℝ) = ((250000000000 / 402315720809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7907_neg : (8410437 / 40000000) ≤ -Real.log (500 / 617) ∧
    -Real.log (500 / 617) ≤ (105130463 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1117)) (n := 12)
    (lo := (8410437 / 40000000)) (hi := (105130463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617 / 500) = 1/(500 / 617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7907 : Bounds (8410437 / 40000000) (105130463 / 500000000) (Real.log (617 / 500)) := by
  have h := reflection_log_7907_neg
  have he : Real.log (617 / 500) = -Real.log (500 / 617) := by
    rw [show ((617 / 500) : ℝ) = ((500 / 617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7908_neg : (266573109 / 1000000000) ≤ -Real.log (383 / 500) ∧
    -Real.log (383 / 500) ≤ (26657311 / 100000000) := by
  have h := checkLog_sound (w := (117 / 883)) (n := 12)
    (lo := (266573109 / 1000000000)) (hi := (26657311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 383) = 1/(383 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7908 : Bounds (-26657311 / 100000000) (-266573109 / 1000000000) (Real.log (383 / 500)) := by
  have h := reflection_log_7908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7909_neg : (58493 / 250000000) ≤ -Real.log (500000 / 500117) ∧
    -Real.log (500000 / 500117) ≤ (233973 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1000117)) (n := 12)
    (lo := (58493 / 250000000)) (hi := (233973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500117 / 500000) = 1/(500000 / 500117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7909 : Bounds (58493 / 250000000) (233973 / 1000000000) (Real.log (500117 / 500000)) := by
  have h := reflection_log_7909_neg
  have he : Real.log (500117 / 500000) = -Real.log (500000 / 500117) := by
    rw [show ((500117 / 500000) : ℝ) = ((500000 / 500117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7910_neg : (234027 / 1000000000) ≤ -Real.log (499883 / 500000) ∧
    -Real.log (499883 / 500000) ≤ (58507 / 250000000) := by
  have h := checkLog_sound (w := (117 / 999883)) (n := 12)
    (lo := (234027 / 1000000000)) (hi := (58507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499883) = 1/(499883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7910 : Bounds (-58507 / 250000000) (-234027 / 1000000000) (Real.log (499883 / 500000)) := by
  have h := reflection_log_7910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7911_neg : (55681681 / 500000000) ≤ -Real.log (1000000 / 1117801) ∧
    -Real.log (1000000 / 1117801) ≤ (111363363 / 1000000000) := by
  have h := checkLog_sound (w := (117801 / 2117801)) (n := 12)
    (lo := (55681681 / 500000000)) (hi := (111363363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117801 / 1000000) = 1/(1000000 / 1117801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7911 : Bounds (55681681 / 500000000) (111363363 / 1000000000) (Real.log (1117801 / 1000000)) := by
  have h := reflection_log_7911_neg
  have he : Real.log (1117801 / 1000000) = -Real.log (1000000 / 1117801) := by
    rw [show ((1117801 / 1000000) : ℝ) = ((1000000 / 1117801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7912_neg : (15667203 / 125000000) ≤ -Real.log (882199 / 1000000) ∧
    -Real.log (882199 / 1000000) ≤ (1002701 / 8000000) := by
  have h := checkLog_sound (w := (117801 / 1882199)) (n := 12)
    (lo := (15667203 / 125000000)) (hi := (1002701 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882199) = 1/(882199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7912 : Bounds (-1002701 / 8000000) (-15667203 / 125000000) (Real.log (882199 / 1000000)) := by
  have h := reflection_log_7912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7913_neg : (111801627 / 1000000000) ≤ -Real.log (1000000 / 1118291) ∧
    -Real.log (1000000 / 1118291) ≤ (27950407 / 250000000) := by
  have h := checkLog_sound (w := (118291 / 2118291)) (n := 12)
    (lo := (111801627 / 1000000000)) (hi := (27950407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118291 / 1000000) = 1/(1000000 / 1118291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7913 : Bounds (111801627 / 1000000000) (27950407 / 250000000) (Real.log (1118291 / 1000000)) := by
  have h := reflection_log_7913_neg
  have he : Real.log (1118291 / 1000000) = -Real.log (1000000 / 1118291) := by
    rw [show ((1118291 / 1000000) : ℝ) = ((1000000 / 1118291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7914_neg : (125893209 / 1000000000) ≤ -Real.log (881709 / 1000000) ∧
    -Real.log (881709 / 1000000) ≤ (12589321 / 100000000) := by
  have h := checkLog_sound (w := (118291 / 1881709)) (n := 12)
    (lo := (125893209 / 1000000000)) (hi := (12589321 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881709) = 1/(881709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7914 : Bounds (-12589321 / 100000000) (-125893209 / 1000000000) (Real.log (881709 / 1000000)) := by
  have h := reflection_log_7914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7915_neg : (7045791 / 500000000) ≤ -Real.log (986007239319 / 1000000000000) ∧
    -Real.log (986007239319 / 1000000000000) ≤ (14091583 / 1000000000) := by
  have h := checkLog_sound (w := (13992760681 / 1986007239319)) (n := 12)
    (lo := (7045791 / 500000000)) (hi := (14091583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986007239319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986007239319) = 1/(986007239319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7915 : Bounds (-14091583 / 1000000000) (-7045791 / 500000000) (Real.log (986007239319 / 1000000000000)) := by
  have h := reflection_log_7915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7916_neg : (6987131 / 500000000) ≤ -Real.log (986122924399 / 1000000000000) ∧
    -Real.log (986122924399 / 1000000000000) ≤ (13974263 / 1000000000) := by
  have h := checkLog_sound (w := (13877075601 / 1986122924399)) (n := 12)
    (lo := (6987131 / 500000000)) (hi := (13974263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986122924399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986122924399) = 1/(986122924399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7916 : Bounds (-13974263 / 1000000000) (-6987131 / 500000000) (Real.log (986122924399 / 1000000000000)) := by
  have h := reflection_log_7916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7917_neg : (236700987 / 1000000000) ≤ -Real.log (20000000000 / 25341243869) ∧
    -Real.log (20000000000 / 25341243869) ≤ (59175247 / 250000000) := by
  have h := checkLog_sound (w := (5341243869 / 45341243869)) (n := 12)
    (lo := (236700987 / 1000000000)) (hi := (59175247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25341243869 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25341243869 / 20000000000) = 1/(20000000000 / 25341243869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7917 : Bounds (236700987 / 1000000000) (59175247 / 250000000) (Real.log (25341243869 / 20000000000)) := by
  have h := reflection_log_7917_neg
  have he : Real.log (25341243869 / 20000000000) = -Real.log (20000000000 / 25341243869) := by
    rw [show ((25341243869 / 20000000000) : ℝ) = ((20000000000 / 25341243869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7918_neg : (59423709 / 250000000) ≤ -Real.log (15625000000 / 19817532627) ∧
    -Real.log (15625000000 / 19817532627) ≤ (237694837 / 1000000000) := by
  have h := checkLog_sound (w := (4192532627 / 35442532627)) (n := 12)
    (lo := (59423709 / 250000000)) (hi := (237694837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19817532627 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19817532627 / 15625000000) = 1/(15625000000 / 19817532627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7918 : Bounds (59423709 / 250000000) (237694837 / 1000000000) (Real.log (19817532627 / 15625000000)) := by
  have h := reflection_log_7918_neg
  have he : Real.log (19817532627 / 15625000000) = -Real.log (15625000000 / 19817532627) := by
    rw [show ((19817532627 / 15625000000) : ℝ) = ((15625000000 / 19817532627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7919_neg : (475776237 / 1000000000) ≤ -Real.log (500000000000 / 804631441617) ∧
    -Real.log (500000000000 / 804631441617) ≤ (237888119 / 500000000) := by
  have h := checkLog_sound (w := (304631441617 / 1304631441617)) (n := 12)
    (lo := (475776237 / 1000000000)) (hi := (237888119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804631441617 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804631441617 / 500000000000) = 1/(500000000000 / 804631441617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7919 : Bounds (475776237 / 1000000000) (237888119 / 500000000) (Real.log (804631441617 / 500000000000)) := by
  have h := reflection_log_7919_neg
  have he : Real.log (804631441617 / 500000000000) = -Real.log (500000000000 / 804631441617) := by
    rw [show ((804631441617 / 500000000000) : ℝ) = ((500000000000 / 804631441617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7920_neg : (238417017 / 500000000) ≤ -Real.log (500000000000 / 805483028721) ∧
    -Real.log (500000000000 / 805483028721) ≤ (95366807 / 200000000) := by
  have h := checkLog_sound (w := (305483028721 / 1305483028721)) (n := 12)
    (lo := (238417017 / 500000000)) (hi := (95366807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805483028721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805483028721 / 500000000000) = 1/(500000000000 / 805483028721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7920 : Bounds (238417017 / 500000000) (95366807 / 200000000) (Real.log (805483028721 / 500000000000)) := by
  have h := reflection_log_7920_neg
  have he : Real.log (805483028721 / 500000000000) = -Real.log (500000000000 / 805483028721) := by
    rw [show ((805483028721 / 500000000000) : ℝ) = ((500000000000 / 805483028721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7921_neg : (210666029 / 1000000000) ≤ -Real.log (2000 / 2469) ∧
    -Real.log (2000 / 2469) ≤ (21066603 / 100000000) := by
  have h := checkLog_sound (w := (469 / 4469)) (n := 12)
    (lo := (210666029 / 1000000000)) (hi := (21066603 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2000) = 1/(2000 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7921 : Bounds (210666029 / 1000000000) (21066603 / 100000000) (Real.log (2469 / 2000)) := by
  have h := reflection_log_7921_neg
  have he : Real.log (2469 / 2000) = -Real.log (2000 / 2469) := by
    rw [show ((2469 / 2000) : ℝ) = ((2000 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7922_neg : (267226063 / 1000000000) ≤ -Real.log (1531 / 2000) ∧
    -Real.log (1531 / 2000) ≤ (16701629 / 62500000) := by
  have h := checkLog_sound (w := (469 / 3531)) (n := 12)
    (lo := (267226063 / 1000000000)) (hi := (16701629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1531) = 1/(1531 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7922 : Bounds (-16701629 / 62500000) (-267226063 / 1000000000) (Real.log (1531 / 2000)) := by
  have h := reflection_log_7922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7923_neg : (29309 / 125000000) ≤ -Real.log (2000000 / 2000469) ∧
    -Real.log (2000000 / 2000469) ≤ (234473 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4000469)) (n := 12)
    (lo := (29309 / 125000000)) (hi := (234473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000469 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000469 / 2000000) = 1/(2000000 / 2000469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7923 : Bounds (29309 / 125000000) (234473 / 1000000000) (Real.log (2000469 / 2000000)) := by
  have h := reflection_log_7923_neg
  have he : Real.log (2000469 / 2000000) = -Real.log (2000000 / 2000469) := by
    rw [show ((2000469 / 2000000) : ℝ) = ((2000000 / 2000469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7924_neg : (234527 / 1000000000) ≤ -Real.log (1999531 / 2000000) ∧
    -Real.log (1999531 / 2000000) ≤ (7329 / 31250000) := by
  have h := checkLog_sound (w := (469 / 3999531)) (n := 12)
    (lo := (234527 / 1000000000)) (hi := (7329 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999531) = 1/(1999531 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7924 : Bounds (-7329 / 31250000) (-234527 / 1000000000) (Real.log (1999531 / 2000000)) := by
  have h := reflection_log_7924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7925_neg : (111593251 / 1000000000) ≤ -Real.log (500000 / 559029) ∧
    -Real.log (500000 / 559029) ≤ (27898313 / 250000000) := by
  have h := checkLog_sound (w := (59029 / 1059029)) (n := 12)
    (lo := (111593251 / 1000000000)) (hi := (27898313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559029 / 500000) = 1/(500000 / 559029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7925 : Bounds (111593251 / 1000000000) (27898313 / 250000000) (Real.log (559029 / 500000)) := by
  have h := reflection_log_7925_neg
  have he : Real.log (559029 / 500000) = -Real.log (500000 / 559029) := by
    rw [show ((559029 / 500000) : ℝ) = ((500000 / 559029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7926_neg : (15703623 / 125000000) ≤ -Real.log (440971 / 500000) ∧
    -Real.log (440971 / 500000) ≤ (25125797 / 200000000) := by
  have h := checkLog_sound (w := (59029 / 940971)) (n := 12)
    (lo := (15703623 / 125000000)) (hi := (25125797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440971) = 1/(440971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7926 : Bounds (-25125797 / 200000000) (-15703623 / 125000000) (Real.log (440971 / 500000)) := by
  have h := reflection_log_7926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7927_neg : (22406283 / 200000000) ≤ -Real.log (250000 / 279637) ∧
    -Real.log (250000 / 279637) ≤ (14003927 / 125000000) := by
  have h := checkLog_sound (w := (29637 / 529637)) (n := 12)
    (lo := (22406283 / 200000000)) (hi := (14003927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279637 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279637 / 250000) = 1/(250000 / 279637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7927 : Bounds (22406283 / 200000000) (14003927 / 125000000) (Real.log (279637 / 250000)) := by
  have h := reflection_log_7927_neg
  have he : Real.log (279637 / 250000) = -Real.log (250000 / 279637) := by
    rw [show ((279637 / 250000) : ℝ) = ((250000 / 279637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7928_neg : (126184731 / 1000000000) ≤ -Real.log (220363 / 250000) ∧
    -Real.log (220363 / 250000) ≤ (31546183 / 250000000) := by
  have h := checkLog_sound (w := (29637 / 470363)) (n := 12)
    (lo := (126184731 / 1000000000)) (hi := (31546183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 220363) = 1/(220363 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7928 : Bounds (-31546183 / 250000000) (-126184731 / 1000000000) (Real.log (220363 / 250000)) := by
  have h := reflection_log_7928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7929_neg : (2830663 / 200000000) ≤ -Real.log (61621648231 / 62500000000) ∧
    -Real.log (61621648231 / 62500000000) ≤ (3538329 / 250000000) := by
  have h := checkLog_sound (w := (878351769 / 124121648231)) (n := 12)
    (lo := (2830663 / 200000000)) (hi := (3538329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61621648231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61621648231) = 1/(61621648231 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7929 : Bounds (-3538329 / 250000000) (-2830663 / 200000000) (Real.log (61621648231 / 62500000000)) := by
  have h := reflection_log_7929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7930_neg : (14035733 / 1000000000) ≤ -Real.log (246515577159 / 250000000000) ∧
    -Real.log (246515577159 / 250000000000) ≤ (7017867 / 500000000) := by
  have h := checkLog_sound (w := (3484422841 / 496515577159)) (n := 12)
    (lo := (14035733 / 1000000000)) (hi := (7017867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246515577159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246515577159) = 1/(246515577159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7930 : Bounds (-7017867 / 500000000) (-14035733 / 1000000000) (Real.log (246515577159 / 250000000000)) := by
  have h := reflection_log_7930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7931_neg : (59305559 / 250000000) ≤ -Real.log (500000000000 / 633861410387) ∧
    -Real.log (500000000000 / 633861410387) ≤ (237222237 / 1000000000) := by
  have h := checkLog_sound (w := (133861410387 / 1133861410387)) (n := 12)
    (lo := (59305559 / 250000000)) (hi := (237222237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633861410387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633861410387 / 500000000000) = 1/(500000000000 / 633861410387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7931 : Bounds (59305559 / 250000000) (237222237 / 1000000000) (Real.log (633861410387 / 500000000000)) := by
  have h := reflection_log_7931_neg
  have he : Real.log (633861410387 / 500000000000) = -Real.log (500000000000 / 633861410387) := by
    rw [show ((633861410387 / 500000000000) : ℝ) = ((500000000000 / 633861410387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7932_neg : (119108073 / 500000000) ≤ -Real.log (250000000000 / 317245862509) ∧
    -Real.log (250000000000 / 317245862509) ≤ (238216147 / 1000000000) := by
  have h := checkLog_sound (w := (67245862509 / 567245862509)) (n := 12)
    (lo := (119108073 / 500000000)) (hi := (238216147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317245862509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317245862509 / 250000000000) = 1/(250000000000 / 317245862509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7932 : Bounds (119108073 / 500000000) (238216147 / 1000000000) (Real.log (317245862509 / 250000000000)) := by
  have h := reflection_log_7932_neg
  have he : Real.log (317245862509 / 250000000000) = -Real.log (250000000000 / 317245862509) := by
    rw [show ((317245862509 / 250000000000) : ℝ) = ((250000000000 / 317245862509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7933_neg : (238417017 / 500000000) ≤ -Real.log (6250000000 / 10068537859) ∧
    -Real.log (6250000000 / 10068537859) ≤ (95366807 / 200000000) := by
  have h := checkLog_sound (w := (3818537859 / 16318537859)) (n := 12)
    (lo := (238417017 / 500000000)) (hi := (95366807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10068537859 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10068537859 / 6250000000) = 1/(6250000000 / 10068537859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7933 : Bounds (238417017 / 500000000) (95366807 / 200000000) (Real.log (10068537859 / 6250000000)) := by
  have h := reflection_log_7933_neg
  have he : Real.log (10068537859 / 6250000000) = -Real.log (6250000000 / 10068537859) := by
    rw [show ((10068537859 / 6250000000) : ℝ) = ((6250000000 / 10068537859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7934_neg : (477892093 / 1000000000) ≤ -Real.log (500000000000 / 806335728283) ∧
    -Real.log (500000000000 / 806335728283) ≤ (238946047 / 500000000) := by
  have h := checkLog_sound (w := (306335728283 / 1306335728283)) (n := 12)
    (lo := (477892093 / 1000000000)) (hi := (238946047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806335728283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806335728283 / 500000000000) = 1/(500000000000 / 806335728283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7934 : Bounds (477892093 / 1000000000) (238946047 / 500000000) (Real.log (806335728283 / 500000000000)) := by
  have h := reflection_log_7934_neg
  have he : Real.log (806335728283 / 500000000000) = -Real.log (500000000000 / 806335728283) := by
    rw [show ((806335728283 / 500000000000) : ℝ) = ((500000000000 / 806335728283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7935_neg : (21107097 / 100000000) ≤ -Real.log (200 / 247) ∧
    -Real.log (200 / 247) ≤ (211070971 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 447)) (n := 12)
    (lo := (21107097 / 100000000)) (hi := (211070971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 200) = 1/(200 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7935 : Bounds (21107097 / 100000000) (211070971 / 1000000000) (Real.log (247 / 200)) := by
  have h := reflection_log_7935_neg
  have he : Real.log (247 / 200) = -Real.log (200 / 247) := by
    rw [show ((247 / 200) : ℝ) = ((200 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
