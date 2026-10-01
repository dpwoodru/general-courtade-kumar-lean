import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0234
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

theorem reflection_log_1_neg : (125136109 / 500000000) ≤ -Real.log (320 / 411) ∧
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


theorem reflection_log_1 : Bounds (125136109 / 500000000) (250272219 / 1000000000) (Real.log (411 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (411 / 320) = -Real.log (320 / 411) := by
    rw [show ((411 / 320) : ℝ) = ((320 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20912437 / 62500000) ≤ -Real.log (229 / 320) ∧
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


theorem reflection_log_2 : Bounds (-334598993 / 1000000000) (-20912437 / 62500000) (Real.log (229 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24981591 / 100000000) ≤ -Real.log (5120 / 6573) ∧
    -Real.log (5120 / 6573) ≤ (249815911 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 11693)) (n := 12)
    (lo := (24981591 / 100000000)) (hi := (249815911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5120) = 1/(5120 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24981591 / 100000000) (249815911 / 1000000000) (Real.log (6573 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6573 / 5120) = -Real.log (5120 / 6573) := by
    rw [show ((6573 / 5120) : ℝ) = ((5120 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333780549 / 1000000000) ≤ -Real.log (3667 / 5120) ∧
    -Real.log (3667 / 5120) ≤ (6675611 / 20000000) := by
  have h := checkLog_sound (w := (1453 / 8787)) (n := 12)
    (lo := (333780549 / 1000000000)) (hi := (6675611 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3667) = 1/(3667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6675611 / 20000000) (-333780549 / 1000000000) (Real.log (3667 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (450279123 / 1000000000) ≤ -Real.log (160 / 251) ∧
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


theorem reflection_log_5 : Bounds (450279123 / 1000000000) (112569781 / 250000000) (Real.log (251 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (251 / 160) = -Real.log (160 / 251) := by
    rw [show ((251 / 160) : ℝ) = ((160 / 251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (84106731 / 100000000) ≤ -Real.log (69 / 160) ∧
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


theorem reflection_log_6 : Bounds (-52566707 / 62500000) (-84106731 / 100000000) (Real.log (69 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56191479 / 125000000) ≤ -Real.log (2560 / 4013) ∧
    -Real.log (2560 / 4013) ≤ (449531833 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 6573)) (n := 12)
    (lo := (56191479 / 125000000)) (hi := (449531833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4013 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4013 / 2560) = 1/(2560 / 4013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56191479 / 125000000) (449531833 / 1000000000) (Real.log (4013 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4013 / 2560) = -Real.log (2560 / 4013) := by
    rw [show ((4013 / 2560) : ℝ) = ((2560 / 4013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209588401 / 250000000) ≤ -Real.log (1107 / 2560) ∧
    -Real.log (1107 / 2560) ≤ (419176803 / 500000000) := by
  have h := checkLog_sound (w := (173 / 2387)) (n := 12)
    (lo := (18150803 / 125000000)) (hi := (5808257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1107) = 1/(1107 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-419176803 / 500000000) (-209588401 / 250000000) (Real.log (1107 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341888257 / 1000000000) ≤ -Real.log (1000000 / 1407603) ∧
    -Real.log (1000000 / 1407603) ≤ (170944129 / 500000000) := by
  have h := checkLog_sound (w := (407603 / 2407603)) (n := 12)
    (lo := (341888257 / 1000000000)) (hi := (170944129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407603 / 1000000) = 1/(1000000 / 1407603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341888257 / 1000000000) (170944129 / 500000000) (Real.log (1407603 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1407603 / 1000000) = -Real.log (1000000 / 1407603) := by
    rw [show ((1407603 / 1000000) : ℝ) = ((1000000 / 1407603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (26178913 / 50000000) ≤ -Real.log (592397 / 1000000) ∧
    -Real.log (592397 / 1000000) ≤ (523578261 / 1000000000) := by
  have h := checkLog_sound (w := (407603 / 1592397)) (n := 12)
    (lo := (26178913 / 50000000)) (hi := (523578261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 592397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 592397) = 1/(592397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-523578261 / 1000000000) (-26178913 / 50000000) (Real.log (592397 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85627067 / 250000000) ≤ -Real.log (250000 / 352119) ∧
    -Real.log (250000 / 352119) ≤ (342508269 / 1000000000) := by
  have h := checkLog_sound (w := (102119 / 602119)) (n := 12)
    (lo := (85627067 / 250000000)) (hi := (342508269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352119 / 250000) = 1/(250000 / 352119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85627067 / 250000000) (342508269 / 1000000000) (Real.log (352119 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (352119 / 250000) = -Real.log (250000 / 352119) := by
    rw [show ((352119 / 250000) : ℝ) = ((250000 / 352119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (525053021 / 1000000000) ≤ -Real.log (147881 / 250000) ∧
    -Real.log (147881 / 250000) ≤ (262526511 / 500000000) := by
  have h := checkLog_sound (w := (102119 / 397881)) (n := 12)
    (lo := (525053021 / 1000000000)) (hi := (262526511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147881) = 1/(147881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-262526511 / 500000000) (-525053021 / 1000000000) (Real.log (147881 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263972201 / 1000000000) ≤ -Real.log (250000 / 325523) ∧
    -Real.log (250000 / 325523) ≤ (131986101 / 500000000) := by
  have h := checkLog_sound (w := (75523 / 575523)) (n := 12)
    (lo := (263972201 / 1000000000)) (hi := (131986101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325523 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325523 / 250000) = 1/(250000 / 325523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263972201 / 1000000000) (131986101 / 500000000) (Real.log (325523 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (325523 / 250000) = -Real.log (250000 / 325523) := by
    rw [show ((325523 / 250000) : ℝ) = ((250000 / 325523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35966799 / 100000000) ≤ -Real.log (174477 / 250000) ∧
    -Real.log (174477 / 250000) ≤ (359667991 / 1000000000) := by
  have h := checkLog_sound (w := (75523 / 424477)) (n := 12)
    (lo := (35966799 / 100000000)) (hi := (359667991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174477) = 1/(174477 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-359667991 / 1000000000) (-35966799 / 100000000) (Real.log (174477 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (264516561 / 1000000000) ≤ -Real.log (1000000 / 1302801) ∧
    -Real.log (1000000 / 1302801) ≤ (132258281 / 500000000) := by
  have h := checkLog_sound (w := (302801 / 2302801)) (n := 12)
    (lo := (264516561 / 1000000000)) (hi := (132258281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302801 / 1000000) = 1/(1000000 / 1302801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (264516561 / 1000000000) (132258281 / 500000000) (Real.log (1302801 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1302801 / 1000000) = -Real.log (1000000 / 1302801) := by
    rw [show ((1302801 / 1000000) : ℝ) = ((1000000 / 1302801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (360684399 / 1000000000) ≤ -Real.log (697199 / 1000000) ∧
    -Real.log (697199 / 1000000) ≤ (901711 / 2500000) := by
  have h := checkLog_sound (w := (302801 / 1697199)) (n := 12)
    (lo := (360684399 / 1000000000)) (hi := (901711 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697199) = 1/(697199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-901711 / 2500000) (-360684399 / 1000000000) (Real.log (697199 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (865466517 / 1000000000) ≤ -Real.log (500000000000 / 1188057164367) ∧
    -Real.log (500000000000 / 1188057164367) ≤ (865466519 / 1000000000) := by
  have h := checkLog_sound (w := (188057164367 / 2188057164367)) (n := 12)
    (lo := (172319337 / 1000000000)) (hi := (86159669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188057164367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1188057164367 / 1000000000000) = 1/(500000000000 / 1188057164367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (865466517 / 1000000000) (865466519 / 1000000000) (Real.log (1188057164367 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1188057164367 / 500000000000) = -Real.log (500000000000 / 1188057164367) := by
    rw [show ((1188057164367 / 500000000000) : ℝ) = ((500000000000 / 1188057164367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (867561289 / 1000000000) ≤ -Real.log (10000000000 / 23810969631) ∧
    -Real.log (10000000000 / 23810969631) ≤ (867561291 / 1000000000) := by
  have h := checkLog_sound (w := (3810969631 / 43810969631)) (n := 12)
    (lo := (174414109 / 1000000000)) (hi := (17441411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23810969631 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23810969631 / 20000000000) = 1/(10000000000 / 23810969631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (867561289 / 1000000000) (867561291 / 1000000000) (Real.log (23810969631 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23810969631 / 10000000000) = -Real.log (10000000000 / 23810969631) := by
    rw [show ((23810969631 / 10000000000) : ℝ) = ((10000000000 / 23810969631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (623640191 / 1000000000) ≤ -Real.log (500000000000 / 932853613943) ∧
    -Real.log (500000000000 / 932853613943) ≤ (4872189 / 7812500) := by
  have h := checkLog_sound (w := (432853613943 / 1432853613943)) (n := 12)
    (lo := (623640191 / 1000000000)) (hi := (4872189 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932853613943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932853613943 / 500000000000) = 1/(500000000000 / 932853613943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (623640191 / 1000000000) (4872189 / 7812500) (Real.log (932853613943 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (932853613943 / 500000000000) = -Real.log (500000000000 / 932853613943) := by
    rw [show ((932853613943 / 500000000000) : ℝ) = ((500000000000 / 932853613943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (625200961 / 1000000000) ≤ -Real.log (500000000000 / 934310720469) ∧
    -Real.log (500000000000 / 934310720469) ≤ (312600481 / 500000000) := by
  have h := checkLog_sound (w := (434310720469 / 1434310720469)) (n := 12)
    (lo := (625200961 / 1000000000)) (hi := (312600481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934310720469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934310720469 / 500000000000) = 1/(500000000000 / 934310720469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (625200961 / 1000000000) (312600481 / 500000000) (Real.log (934310720469 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (934310720469 / 500000000000) = -Real.log (500000000000 / 934310720469) := by
    rw [show ((934310720469 / 500000000000) : ℝ) = ((500000000000 / 934310720469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0234
