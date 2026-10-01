import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0057
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

theorem reflection_log_1_neg : (73773191 / 200000000) ≤ -Real.log (1280 / 1851) ∧
    -Real.log (1280 / 1851) ≤ (92216489 / 250000000) := by
  have h := checkLog_sound (w := (571 / 3131)) (n := 12)
    (lo := (73773191 / 200000000)) (hi := (92216489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1280) = 1/(1280 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73773191 / 200000000) (92216489 / 250000000) (Real.log (1851 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1851 / 1280) = -Real.log (1280 / 1851) := by
    rw [show ((1851 / 1280) : ℝ) = ((1280 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (59075983 / 100000000) ≤ -Real.log (709 / 1280) ∧
    -Real.log (709 / 1280) ≤ (590759831 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 1989)) (n := 12)
    (lo := (59075983 / 100000000)) (hi := (590759831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 709) = 1/(709 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-590759831 / 1000000000) (-59075983 / 100000000) (Real.log (709 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184027627 / 500000000) ≤ -Real.log (2560 / 3699) ∧
    -Real.log (2560 / 3699) ≤ (73611051 / 200000000) := by
  have h := checkLog_sound (w := (1139 / 6259)) (n := 12)
    (lo := (184027627 / 500000000)) (hi := (73611051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3699 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3699 / 2560) = 1/(2560 / 3699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184027627 / 500000000) (73611051 / 200000000) (Real.log (3699 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3699 / 2560) = -Real.log (2560 / 3699) := by
    rw [show ((3699 / 2560) : ℝ) = ((2560 / 3699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (588646409 / 1000000000) ≤ -Real.log (1421 / 2560) ∧
    -Real.log (1421 / 2560) ≤ (58864641 / 100000000) := by
  have h := checkLog_sound (w := (1139 / 3981)) (n := 12)
    (lo := (588646409 / 1000000000)) (hi := (58864641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1421) = 1/(1421 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58864641 / 100000000) (-588646409 / 1000000000) (Real.log (1421 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (637733567 / 1000000000) ≤ -Real.log (640 / 1211) ∧
    -Real.log (640 / 1211) ≤ (9964587 / 15625000) := by
  have h := checkLog_sound (w := (571 / 1851)) (n := 12)
    (lo := (637733567 / 1000000000)) (hi := (9964587 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 640) = 1/(640 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (637733567 / 1000000000) (9964587 / 15625000) (Real.log (1211 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211 / 640) = -Real.log (640 / 1211) := by
    rw [show ((1211 / 640) : ℝ) = ((640 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222736167 / 100000000) ≤ -Real.log (69 / 640) ∧
    -Real.log (69 / 640) ≤ (1113680837 / 500000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 69) = 1/(69 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1113680837 / 500000000) (-222736167 / 100000000) (Real.log (69 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (636494153 / 1000000000) ≤ -Real.log (1280 / 2419) ∧
    -Real.log (1280 / 2419) ≤ (318247077 / 500000000) := by
  have h := checkLog_sound (w := (1139 / 3699)) (n := 12)
    (lo := (636494153 / 1000000000)) (hi := (318247077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 1280) = 1/(1280 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (636494153 / 1000000000) (318247077 / 500000000) (Real.log (2419 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2419 / 1280) = -Real.log (1280 / 2419) := by
    rw [show ((2419 / 1280) : ℝ) = ((1280 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (275731933 / 125000000) ≤ -Real.log (141 / 1280) ∧
    -Real.log (141 / 1280) ≤ (551463867 / 250000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 141) = 1/(141 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-551463867 / 250000000) (-275731933 / 125000000) (Real.log (141 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254433353 / 500000000) ≤ -Real.log (200000 / 332681) ∧
    -Real.log (200000 / 332681) ≤ (508866707 / 1000000000) := by
  have h := checkLog_sound (w := (132681 / 532681)) (n := 12)
    (lo := (254433353 / 500000000)) (hi := (508866707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332681 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332681 / 200000) = 1/(200000 / 332681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254433353 / 500000000) (508866707 / 1000000000) (Real.log (332681 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (332681 / 200000) = -Real.log (200000 / 332681) := by
    rw [show ((332681 / 200000) : ℝ) = ((200000 / 332681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1088874851 / 1000000000) ≤ -Real.log (67319 / 200000) ∧
    -Real.log (67319 / 200000) ≤ (1088874853 / 1000000000) := by
  have h := checkLog_sound (w := (32681 / 167319)) (n := 12)
    (lo := (395727671 / 1000000000)) (hi := (49465959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 67319) = 1/(67319 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1088874853 / 1000000000) (-1088874851 / 1000000000) (Real.log (67319 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63765297 / 125000000) ≤ -Real.log (200000 / 333099) ∧
    -Real.log (200000 / 333099) ≤ (510122377 / 1000000000) := by
  have h := checkLog_sound (w := (133099 / 533099)) (n := 12)
    (lo := (63765297 / 125000000)) (hi := (510122377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333099 / 200000) = 1/(200000 / 333099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63765297 / 125000000) (510122377 / 1000000000) (Real.log (333099 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (333099 / 200000) = -Real.log (200000 / 333099) := by
    rw [show ((333099 / 200000) : ℝ) = ((200000 / 333099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1095103451 / 1000000000) ≤ -Real.log (66901 / 200000) ∧
    -Real.log (66901 / 200000) ≤ (1095103453 / 1000000000) := by
  have h := checkLog_sound (w := (33099 / 166901)) (n := 12)
    (lo := (401956271 / 1000000000)) (hi := (25122267 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66901) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 66901) = 1/(66901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1095103453 / 1000000000) (-1095103451 / 1000000000) (Real.log (66901 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213731029 / 500000000) ≤ -Real.log (1000000 / 1533361) ∧
    -Real.log (1000000 / 1533361) ≤ (427462059 / 1000000000) := by
  have h := checkLog_sound (w := (533361 / 2533361)) (n := 12)
    (lo := (213731029 / 500000000)) (hi := (427462059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533361 / 1000000) = 1/(1000000 / 1533361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213731029 / 500000000) (427462059 / 1000000000) (Real.log (1533361 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1533361 / 1000000) = -Real.log (1000000 / 1533361) := by
    rw [show ((1533361 / 1000000) : ℝ) = ((1000000 / 1533361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (381099669 / 500000000) ≤ -Real.log (466639 / 1000000) ∧
    -Real.log (466639 / 1000000) ≤ (38109967 / 50000000) := by
  have h := checkLog_sound (w := (33361 / 966639)) (n := 12)
    (lo := (34526079 / 500000000)) (hi := (69052159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 466639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 466639) = 1/(466639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38109967 / 50000000) (-381099669 / 500000000) (Real.log (466639 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (8577017 / 20000000) ≤ -Real.log (250000 / 383873) ∧
    -Real.log (250000 / 383873) ≤ (428850851 / 1000000000) := by
  have h := checkLog_sound (w := (133873 / 633873)) (n := 12)
    (lo := (8577017 / 20000000)) (hi := (428850851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383873 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383873 / 250000) = 1/(250000 / 383873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8577017 / 20000000) (428850851 / 1000000000) (Real.log (383873 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (383873 / 250000) = -Real.log (250000 / 383873) := by
    rw [show ((383873 / 250000) : ℝ) = ((250000 / 383873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (766776497 / 1000000000) ≤ -Real.log (116127 / 250000) ∧
    -Real.log (116127 / 250000) ≤ (766776499 / 1000000000) := by
  have h := checkLog_sound (w := (8873 / 241127)) (n := 12)
    (lo := (73629317 / 1000000000)) (hi := (36814659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 116127) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 116127) = 1/(116127 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-766776499 / 1000000000) (-766776497 / 1000000000) (Real.log (116127 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (399435389 / 250000000) ≤ -Real.log (6250000000 / 30886618191) ∧
    -Real.log (6250000000 / 30886618191) ≤ (1597741559 / 1000000000) := by
  have h := checkLog_sound (w := (5886618191 / 55886618191)) (n := 12)
    (lo := (52861799 / 250000000)) (hi := (211447197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30886618191 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(30886618191 / 25000000000) = 1/(6250000000 / 30886618191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (399435389 / 250000000) (1597741559 / 1000000000) (Real.log (30886618191 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (30886618191 / 6250000000) = -Real.log (6250000000 / 30886618191) := by
    rw [show ((30886618191 / 6250000000) : ℝ) = ((6250000000 / 30886618191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1605225827 / 1000000000) ≤ -Real.log (250000000000 / 1244745967923) ∧
    -Real.log (250000000000 / 1244745967923) ≤ (160522583 / 100000000) := by
  have h := checkLog_sound (w := (244745967923 / 2244745967923)) (n := 12)
    (lo := (218931467 / 1000000000)) (hi := (54732867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244745967923 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1244745967923 / 1000000000000) = 1/(250000000000 / 1244745967923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1605225827 / 1000000000) (160522583 / 100000000) (Real.log (1244745967923 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1244745967923 / 250000000000) = -Real.log (250000000000 / 1244745967923) := by
    rw [show ((1244745967923 / 250000000000) : ℝ) = ((250000000000 / 1244745967923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1189661397 / 1000000000) ≤ -Real.log (100000000000 / 328596838241) ∧
    -Real.log (100000000000 / 328596838241) ≤ (1189661399 / 1000000000) := by
  have h := checkLog_sound (w := (128596838241 / 528596838241)) (n := 12)
    (lo := (496514217 / 1000000000)) (hi := (248257109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328596838241 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328596838241 / 200000000000) = 1/(100000000000 / 328596838241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1189661397 / 1000000000) (1189661399 / 1000000000) (Real.log (328596838241 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (328596838241 / 100000000000) = -Real.log (100000000000 / 328596838241) := by
    rw [show ((328596838241 / 100000000000) : ℝ) = ((100000000000 / 328596838241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (298906837 / 250000000) ≤ -Real.log (500000000000 / 1652815452049) ∧
    -Real.log (500000000000 / 1652815452049) ≤ (23912547 / 20000000) := by
  have h := checkLog_sound (w := (652815452049 / 2652815452049)) (n := 12)
    (lo := (62810021 / 125000000)) (hi := (502480169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652815452049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652815452049 / 1000000000000) = 1/(500000000000 / 1652815452049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (298906837 / 250000000) (23912547 / 20000000) (Real.log (1652815452049 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1652815452049 / 500000000000) = -Real.log (500000000000 / 1652815452049) := by
    rw [show ((1652815452049 / 500000000000) : ℝ) = ((500000000000 / 1652815452049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0057
