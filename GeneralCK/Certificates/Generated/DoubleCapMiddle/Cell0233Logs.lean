import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0233
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

theorem reflection_log_1_neg : (250728319 / 1000000000) ≤ -Real.log (5120 / 6579) ∧
    -Real.log (5120 / 6579) ≤ (391763 / 1562500) := by
  have h := checkLog_sound (w := (1459 / 11699)) (n := 12)
    (lo := (250728319 / 1000000000)) (hi := (391763 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6579 / 5120) = 1/(5120 / 6579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (250728319 / 1000000000) (391763 / 1562500) (Real.log (6579 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6579 / 5120) = -Real.log (5120 / 6579) := by
    rw [show ((6579 / 5120) : ℝ) = ((5120 / 6579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41927263 / 125000000) ≤ -Real.log (3661 / 5120) ∧
    -Real.log (3661 / 5120) ≤ (67083621 / 200000000) := by
  have h := checkLog_sound (w := (1459 / 8781)) (n := 12)
    (lo := (41927263 / 125000000)) (hi := (67083621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3661) = 1/(3661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-67083621 / 200000000) (-41927263 / 125000000) (Real.log (3661 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (125136109 / 500000000) ≤ -Real.log (320 / 411) ∧
    -Real.log (320 / 411) ≤ (250272219 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 731)) (n := 12)
    (lo := (125136109 / 500000000)) (hi := (250272219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411 / 320) = 1/(320 / 411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (125136109 / 500000000) (250272219 / 1000000000) (Real.log (411 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (411 / 320) = -Real.log (320 / 411) := by
    rw [show ((411 / 320) : ℝ) = ((320 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20912437 / 62500000) ≤ -Real.log (229 / 320) ∧
    -Real.log (229 / 320) ≤ (334598993 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 549)) (n := 12)
    (lo := (20912437 / 62500000)) (hi := (334598993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 229) = 1/(229 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334598993 / 1000000000) (-20912437 / 62500000) (Real.log (229 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7047279 / 15625000) ≤ -Real.log (2560 / 4019) ∧
    -Real.log (2560 / 4019) ≤ (451025857 / 1000000000) := by
  have h := checkLog_sound (w := (1459 / 6579)) (n := 12)
    (lo := (7047279 / 15625000)) (hi := (451025857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4019 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4019 / 2560) = 1/(2560 / 4019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7047279 / 15625000) (451025857 / 1000000000) (Real.log (4019 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4019 / 2560) = -Real.log (2560 / 4019) := by
    rw [show ((4019 / 2560) : ℝ) = ((2560 / 4019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2109471 / 2500000) ≤ -Real.log (1101 / 2560) ∧
    -Real.log (1101 / 2560) ≤ (421894201 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2381)) (n := 12)
    (lo := (7532061 / 50000000)) (hi := (150641221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1101) = 1/(1101 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-421894201 / 500000000) (-2109471 / 2500000) (Real.log (1101 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (450279123 / 1000000000) ≤ -Real.log (160 / 251) ∧
    -Real.log (160 / 251) ≤ (112569781 / 250000000) := by
  have h := checkLog_sound (w := (91 / 411)) (n := 12)
    (lo := (450279123 / 1000000000)) (hi := (112569781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251 / 160) = 1/(160 / 251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (450279123 / 1000000000) (112569781 / 250000000) (Real.log (251 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (251 / 160) = -Real.log (160 / 251) := by
    rw [show ((251 / 160) : ℝ) = ((160 / 251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (84106731 / 100000000) ≤ -Real.log (69 / 160) ∧
    -Real.log (69 / 160) ≤ (52566707 / 62500000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 69) = 1/(69 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52566707 / 62500000) (-84106731 / 100000000) (Real.log (69 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (171253779 / 500000000) ≤ -Real.log (40000 / 56339) ∧
    -Real.log (40000 / 56339) ≤ (342507559 / 1000000000) := by
  have h := checkLog_sound (w := (16339 / 96339)) (n := 12)
    (lo := (171253779 / 500000000)) (hi := (342507559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56339 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56339 / 40000) = 1/(40000 / 56339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (171253779 / 500000000) (342507559 / 1000000000) (Real.log (56339 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56339 / 40000) = -Real.log (40000 / 56339) := by
    rw [show ((56339 / 40000) : ℝ) = ((40000 / 56339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (525051331 / 1000000000) ≤ -Real.log (23661 / 40000) ∧
    -Real.log (23661 / 40000) ≤ (131262833 / 250000000) := by
  have h := checkLog_sound (w := (16339 / 63661)) (n := 12)
    (lo := (525051331 / 1000000000)) (hi := (131262833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 23661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 23661) = 1/(23661 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131262833 / 250000000) (-525051331 / 1000000000) (Real.log (23661 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171563593 / 500000000) ≤ -Real.log (250000 / 352337) ∧
    -Real.log (250000 / 352337) ≤ (343127187 / 1000000000) := by
  have h := checkLog_sound (w := (102337 / 602337)) (n := 12)
    (lo := (171563593 / 500000000)) (hi := (343127187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352337 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352337 / 250000) = 1/(250000 / 352337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171563593 / 500000000) (343127187 / 1000000000) (Real.log (352337 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (352337 / 250000) = -Real.log (250000 / 352337) := by
    rw [show ((352337 / 250000) : ℝ) = ((250000 / 352337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (526528267 / 1000000000) ≤ -Real.log (147663 / 250000) ∧
    -Real.log (147663 / 250000) ≤ (131632067 / 250000000) := by
  have h := checkLog_sound (w := (102337 / 397663)) (n := 12)
    (lo := (526528267 / 1000000000)) (hi := (131632067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147663) = 1/(147663 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-131632067 / 250000000) (-526528267 / 1000000000) (Real.log (147663 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132257897 / 500000000) ≤ -Real.log (2500 / 3257) ∧
    -Real.log (2500 / 3257) ≤ (52903159 / 200000000) := by
  have h := checkLog_sound (w := (757 / 5757)) (n := 12)
    (lo := (132257897 / 500000000)) (hi := (52903159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2500) = 1/(2500 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132257897 / 500000000) (52903159 / 200000000) (Real.log (3257 / 2500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3257 / 2500) = -Real.log (2500 / 3257) := by
    rw [show ((3257 / 2500) : ℝ) = ((2500 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72136593 / 200000000) ≤ -Real.log (1743 / 2500) ∧
    -Real.log (1743 / 2500) ≤ (180341483 / 500000000) := by
  have h := checkLog_sound (w := (757 / 4243)) (n := 12)
    (lo := (72136593 / 200000000)) (hi := (180341483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1743) = 1/(1743 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-180341483 / 500000000) (-72136593 / 200000000) (Real.log (1743 / 2500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132530313 / 500000000) ≤ -Real.log (100000 / 130351) ∧
    -Real.log (100000 / 130351) ≤ (265060627 / 1000000000) := by
  have h := checkLog_sound (w := (30351 / 230351)) (n := 12)
    (lo := (132530313 / 500000000)) (hi := (265060627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130351 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130351 / 100000) = 1/(100000 / 130351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132530313 / 500000000) (265060627 / 1000000000) (Real.log (130351 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (130351 / 100000) = -Real.log (100000 / 130351) := by
    rw [show ((130351 / 100000) : ℝ) = ((100000 / 130351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361701843 / 1000000000) ≤ -Real.log (69649 / 100000) ∧
    -Real.log (69649 / 100000) ≤ (90425461 / 250000000) := by
  have h := checkLog_sound (w := (30351 / 169649)) (n := 12)
    (lo := (361701843 / 1000000000)) (hi := (90425461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69649) = 1/(69649 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90425461 / 250000000) (-361701843 / 1000000000) (Real.log (69649 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (867558889 / 1000000000) ≤ -Real.log (1250000000 / 2976364059) ∧
    -Real.log (1250000000 / 2976364059) ≤ (867558891 / 1000000000) := by
  have h := checkLog_sound (w := (476364059 / 5476364059)) (n := 12)
    (lo := (174411709 / 1000000000)) (hi := (17441171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2976364059 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2976364059 / 2500000000) = 1/(1250000000 / 2976364059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (867558889 / 1000000000) (867558891 / 1000000000) (Real.log (2976364059 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2976364059 / 1250000000) = -Real.log (1250000000 / 2976364059) := by
    rw [show ((2976364059 / 1250000000) : ℝ) = ((1250000000 / 2976364059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (869655453 / 1000000000) ≤ -Real.log (500000000000 / 1193044296811) ∧
    -Real.log (500000000000 / 1193044296811) ≤ (173931091 / 200000000) := by
  have h := checkLog_sound (w := (193044296811 / 2193044296811)) (n := 12)
    (lo := (176508273 / 1000000000)) (hi := (88254137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193044296811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1193044296811 / 1000000000000) = 1/(500000000000 / 1193044296811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (869655453 / 1000000000) (173931091 / 200000000) (Real.log (1193044296811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1193044296811 / 500000000000) = -Real.log (500000000000 / 1193044296811) := by
    rw [show ((1193044296811 / 500000000000) : ℝ) = ((500000000000 / 1193044296811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (625198759 / 1000000000) ≤ -Real.log (62500000000 / 116788582903) ∧
    -Real.log (62500000000 / 116788582903) ≤ (15629969 / 25000000) := by
  have h := checkLog_sound (w := (54288582903 / 179288582903)) (n := 12)
    (lo := (625198759 / 1000000000)) (hi := (15629969 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116788582903 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116788582903 / 62500000000) = 1/(62500000000 / 116788582903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (625198759 / 1000000000) (15629969 / 25000000) (Real.log (116788582903 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (116788582903 / 62500000000) = -Real.log (62500000000 / 116788582903) := by
    rw [show ((116788582903 / 62500000000) : ℝ) = ((62500000000 / 116788582903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (626762469 / 1000000000) ≤ -Real.log (500000000000 / 935770793551) ∧
    -Real.log (500000000000 / 935770793551) ≤ (62676247 / 100000000) := by
  have h := checkLog_sound (w := (435770793551 / 1435770793551)) (n := 12)
    (lo := (626762469 / 1000000000)) (hi := (62676247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935770793551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935770793551 / 500000000000) = 1/(500000000000 / 935770793551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (626762469 / 1000000000) (62676247 / 100000000) (Real.log (935770793551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (935770793551 / 500000000000) = -Real.log (500000000000 / 935770793551) := by
    rw [show ((935770793551 / 500000000000) : ℝ) = ((500000000000 / 935770793551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0233
