import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell134
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

theorem reflection_log_1_neg : (284503197 / 1000000000) ≤ -Real.log (1024 / 1361) ∧
    -Real.log (1024 / 1361) ≤ (142251599 / 500000000) := by
  have h := checkLog_sound (w := (337 / 2385)) (n := 12)
    (lo := (284503197 / 1000000000)) (hi := (142251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1024) = 1/(1024 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (284503197 / 1000000000) (142251599 / 500000000) (Real.log (1361 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1361 / 1024) = -Real.log (1024 / 1361) := by
    rw [show ((1361 / 1024) : ℝ) = ((1024 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (399137513 / 1000000000) ≤ -Real.log (687 / 1024) ∧
    -Real.log (687 / 1024) ≤ (199568757 / 500000000) := by
  have h := checkLog_sound (w := (337 / 1711)) (n := 12)
    (lo := (399137513 / 1000000000)) (hi := (199568757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 687) = 1/(687 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-199568757 / 500000000) (-399137513 / 1000000000) (Real.log (687 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (284062247 / 1000000000) ≤ -Real.log (2560 / 3401) ∧
    -Real.log (2560 / 3401) ≤ (35507781 / 125000000) := by
  have h := checkLog_sound (w := (841 / 5961)) (n := 12)
    (lo := (284062247 / 1000000000)) (hi := (35507781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3401 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3401 / 2560) = 1/(2560 / 3401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (284062247 / 1000000000) (35507781 / 125000000) (Real.log (3401 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3401 / 2560) = -Real.log (2560 / 3401) := by
    rw [show ((3401 / 2560) : ℝ) = ((2560 / 3401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99566133 / 250000000) ≤ -Real.log (1719 / 2560) ∧
    -Real.log (1719 / 2560) ≤ (398264533 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 4279)) (n := 12)
    (lo := (99566133 / 250000000)) (hi := (398264533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1719) = 1/(1719 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-398264533 / 1000000000) (-99566133 / 250000000) (Real.log (1719 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41953133 / 200000000) ≤ -Real.log (1000000 / 1233389) ∧
    -Real.log (1000000 / 1233389) ≤ (104882833 / 500000000) := by
  have h := checkLog_sound (w := (233389 / 2233389)) (n := 12)
    (lo := (41953133 / 200000000)) (hi := (104882833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233389 / 1000000) = 1/(1000000 / 1233389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41953133 / 200000000) (104882833 / 500000000) (Real.log (1233389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1233389 / 1000000) = -Real.log (1000000 / 1233389) := by
    rw [show ((1233389 / 1000000) : ℝ) = ((1000000 / 1233389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (265775777 / 1000000000) ≤ -Real.log (766611 / 1000000) ∧
    -Real.log (766611 / 1000000) ≤ (132887889 / 500000000) := by
  have h := checkLog_sound (w := (233389 / 1766611)) (n := 12)
    (lo := (265775777 / 1000000000)) (hi := (132887889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766611) = 1/(766611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132887889 / 500000000) (-265775777 / 1000000000) (Real.log (766611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (210107753 / 1000000000) ≤ -Real.log (1000000 / 1233811) ∧
    -Real.log (1000000 / 1233811) ≤ (105053877 / 500000000) := by
  have h := checkLog_sound (w := (233811 / 2233811)) (n := 12)
    (lo := (210107753 / 1000000000)) (hi := (105053877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233811 / 1000000) = 1/(1000000 / 1233811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (210107753 / 1000000000) (105053877 / 500000000) (Real.log (1233811 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1233811 / 1000000) = -Real.log (1000000 / 1233811) := by
    rw [show ((1233811 / 1000000) : ℝ) = ((1000000 / 1233811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (266326403 / 1000000000) ≤ -Real.log (766189 / 1000000) ∧
    -Real.log (766189 / 1000000) ≤ (66581601 / 250000000) := by
  have h := checkLog_sound (w := (233811 / 1766189)) (n := 12)
    (lo := (266326403 / 1000000000)) (hi := (66581601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766189) = 1/(766189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-66581601 / 250000000) (-266326403 / 1000000000) (Real.log (766189 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (154916101 / 1000000000) ≤ -Real.log (25000 / 29189) ∧
    -Real.log (25000 / 29189) ≤ (77458051 / 500000000) := by
  have h := checkLog_sound (w := (4189 / 54189)) (n := 12)
    (lo := (154916101 / 1000000000)) (hi := (77458051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29189 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29189 / 25000) = 1/(25000 / 29189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (154916101 / 1000000000) (77458051 / 500000000) (Real.log (29189 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29189 / 25000) = -Real.log (25000 / 29189) := by
    rw [show ((29189 / 25000) : ℝ) = ((25000 / 29189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183394131 / 1000000000) ≤ -Real.log (20811 / 25000) ∧
    -Real.log (20811 / 25000) ≤ (45848533 / 250000000) := by
  have h := checkLog_sound (w := (4189 / 45811)) (n := 12)
    (lo := (183394131 / 1000000000)) (hi := (45848533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20811) = 1/(20811 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45848533 / 250000000) (-183394131 / 1000000000) (Real.log (20811 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (155183289 / 1000000000) ≤ -Real.log (15625 / 18248) ∧
    -Real.log (15625 / 18248) ≤ (15518329 / 100000000) := by
  have h := checkLog_sound (w := (2623 / 33873)) (n := 12)
    (lo := (155183289 / 1000000000)) (hi := (15518329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18248 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18248 / 15625) = 1/(15625 / 18248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (155183289 / 1000000000) (15518329 / 100000000) (Real.log (18248 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18248 / 15625) = -Real.log (15625 / 18248) := by
    rw [show ((18248 / 15625) : ℝ) = ((15625 / 18248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183769003 / 1000000000) ≤ -Real.log (13002 / 15625) ∧
    -Real.log (13002 / 15625) ≤ (45942251 / 250000000) := by
  have h := checkLog_sound (w := (2623 / 28627)) (n := 12)
    (lo := (183769003 / 1000000000)) (hi := (45942251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13002) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13002) = 1/(13002 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-45942251 / 250000000) (-183769003 / 1000000000) (Real.log (13002 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682326779 / 1000000000) ≤ -Real.log (125000000000 / 247309482257) ∧
    -Real.log (125000000000 / 247309482257) ≤ (34116339 / 50000000) := by
  have h := checkLog_sound (w := (122309482257 / 372309482257)) (n := 12)
    (lo := (682326779 / 1000000000)) (hi := (34116339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247309482257 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247309482257 / 125000000000) = 1/(125000000000 / 247309482257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682326779 / 1000000000) (34116339 / 50000000) (Real.log (247309482257 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247309482257 / 125000000000) = -Real.log (125000000000 / 247309482257) := by
    rw [show ((247309482257 / 125000000000) : ℝ) = ((125000000000 / 247309482257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (68364071 / 100000000) ≤ -Real.log (500000000000 / 990538573509) ∧
    -Real.log (500000000000 / 990538573509) ≤ (683640711 / 1000000000) := by
  have h := checkLog_sound (w := (490538573509 / 1490538573509)) (n := 12)
    (lo := (68364071 / 100000000)) (hi := (683640711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990538573509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990538573509 / 500000000000) = 1/(500000000000 / 990538573509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (68364071 / 100000000) (683640711 / 1000000000) (Real.log (990538573509 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (990538573509 / 500000000000) = -Real.log (500000000000 / 990538573509) := by
    rw [show ((990538573509 / 500000000000) : ℝ) = ((500000000000 / 990538573509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (237770721 / 500000000) ≤ -Real.log (250000000000 / 402221269979) ∧
    -Real.log (250000000000 / 402221269979) ≤ (475541443 / 1000000000) := by
  have h := checkLog_sound (w := (152221269979 / 652221269979)) (n := 12)
    (lo := (237770721 / 500000000)) (hi := (475541443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402221269979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402221269979 / 250000000000) = 1/(250000000000 / 402221269979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237770721 / 500000000) (475541443 / 1000000000) (Real.log (402221269979 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (402221269979 / 250000000000) = -Real.log (250000000000 / 402221269979) := by
    rw [show ((402221269979 / 250000000000) : ℝ) = ((250000000000 / 402221269979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (119108539 / 250000000) ≤ -Real.log (100000000000 / 161032199627) ∧
    -Real.log (100000000000 / 161032199627) ≤ (476434157 / 1000000000) := by
  have h := checkLog_sound (w := (61032199627 / 261032199627)) (n := 12)
    (lo := (119108539 / 250000000)) (hi := (476434157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161032199627 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161032199627 / 100000000000) = 1/(100000000000 / 161032199627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (119108539 / 250000000) (476434157 / 1000000000) (Real.log (161032199627 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (161032199627 / 100000000000) = -Real.log (100000000000 / 161032199627) := by
    rw [show ((161032199627 / 100000000000) : ℝ) = ((100000000000 / 161032199627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (42288779 / 125000000) ≤ -Real.log (1000000000 / 1402575561) ∧
    -Real.log (1000000000 / 1402575561) ≤ (338310233 / 1000000000) := by
  have h := checkLog_sound (w := (402575561 / 2402575561)) (n := 12)
    (lo := (42288779 / 125000000)) (hi := (338310233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1402575561 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1402575561 / 1000000000) = 1/(1000000000 / 1402575561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (42288779 / 125000000) (338310233 / 1000000000) (Real.log (1402575561 / 1000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1402575561 / 1000000000) = -Real.log (1000000000 / 1402575561) := by
    rw [show ((1402575561 / 1000000000) : ℝ) = ((1000000000 / 1402575561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338952293 / 1000000000) ≤ -Real.log (125000000000 / 175434548531) ∧
    -Real.log (125000000000 / 175434548531) ≤ (169476147 / 500000000) := by
  have h := checkLog_sound (w := (50434548531 / 300434548531)) (n := 12)
    (lo := (338952293 / 1000000000)) (hi := (169476147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175434548531 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175434548531 / 125000000000) = 1/(125000000000 / 175434548531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338952293 / 1000000000) (169476147 / 500000000) (Real.log (175434548531 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (175434548531 / 125000000000) = -Real.log (125000000000 / 175434548531) := by
    rw [show ((175434548531 / 125000000000) : ℝ) = ((125000000000 / 175434548531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14292857 / 500000000) ≤ -Real.log (237260496 / 244140625) ∧
    -Real.log (237260496 / 244140625) ≤ (5717143 / 200000000) := by
  have h := checkLog_sound (w := (6880129 / 481401121)) (n := 12)
    (lo := (14292857 / 500000000)) (hi := (5717143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 237260496) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 237260496) = 1/(237260496 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5717143 / 200000000) (-14292857 / 500000000) (Real.log (237260496 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2847803 / 100000000) ≤ -Real.log (607452279 / 625000000) ∧
    -Real.log (607452279 / 625000000) ≤ (28478031 / 1000000000) := by
  have h := checkLog_sound (w := (17547721 / 1232452279)) (n := 12)
    (lo := (2847803 / 100000000)) (hi := (28478031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 607452279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 607452279) = 1/(607452279 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28478031 / 1000000000) (-2847803 / 100000000) (Real.log (607452279 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell134
