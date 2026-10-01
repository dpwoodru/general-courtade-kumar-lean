import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell245
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

theorem reflection_log_1_neg : (166139093 / 500000000) ≤ -Real.log (2560 / 3569) ∧
    -Real.log (2560 / 3569) ≤ (332278187 / 1000000000) := by
  have h := checkLog_sound (w := (1009 / 6129)) (n := 12)
    (lo := (166139093 / 500000000)) (hi := (332278187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3569 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3569 / 2560) = 1/(2560 / 3569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166139093 / 500000000) (332278187 / 1000000000) (Real.log (3569 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3569 / 2560) = -Real.log (2560 / 3569) := by
    rw [show ((3569 / 2560) : ℝ) = ((2560 / 3569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (250553687 / 500000000) ≤ -Real.log (1551 / 2560) ∧
    -Real.log (1551 / 2560) ≤ (4008859 / 8000000) := by
  have h := checkLog_sound (w := (1009 / 4111)) (n := 12)
    (lo := (250553687 / 500000000)) (hi := (4008859 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1551) = 1/(1551 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4008859 / 8000000) (-250553687 / 500000000) (Real.log (1551 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331857811 / 1000000000) ≤ -Real.log (1024 / 1427) ∧
    -Real.log (1024 / 1427) ≤ (82964453 / 250000000) := by
  have h := checkLog_sound (w := (403 / 2451)) (n := 12)
    (lo := (331857811 / 1000000000)) (hi := (82964453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1024) = 1/(1024 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331857811 / 1000000000) (82964453 / 250000000) (Real.log (1427 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1427 / 1024) = -Real.log (1024 / 1427) := by
    rw [show ((1427 / 1024) : ℝ) = ((1024 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (500140723 / 1000000000) ≤ -Real.log (621 / 1024) ∧
    -Real.log (621 / 1024) ≤ (125035181 / 250000000) := by
  have h := checkLog_sound (w := (403 / 1645)) (n := 12)
    (lo := (500140723 / 1000000000)) (hi := (125035181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 621) = 1/(621 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125035181 / 250000000) (-500140723 / 1000000000) (Real.log (621 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (123510501 / 500000000) ≤ -Real.log (500000 / 640103) ∧
    -Real.log (500000 / 640103) ≤ (247021003 / 1000000000) := by
  have h := checkLog_sound (w := (140103 / 1140103)) (n := 12)
    (lo := (123510501 / 500000000)) (hi := (247021003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640103 / 500000) = 1/(500000 / 640103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (123510501 / 500000000) (247021003 / 1000000000) (Real.log (640103 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (640103 / 500000) = -Real.log (500000 / 640103) := by
    rw [show ((640103 / 500000) : ℝ) = ((500000 / 640103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328790219 / 1000000000) ≤ -Real.log (359897 / 500000) ∧
    -Real.log (359897 / 500000) ≤ (16439511 / 50000000) := by
  have h := checkLog_sound (w := (140103 / 859897)) (n := 12)
    (lo := (328790219 / 1000000000)) (hi := (16439511 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359897) = 1/(359897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-16439511 / 50000000) (-328790219 / 1000000000) (Real.log (359897 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9894117 / 40000000) ≤ -Real.log (1000000 / 1280631) ∧
    -Real.log (1000000 / 1280631) ≤ (123676463 / 500000000) := by
  have h := checkLog_sound (w := (280631 / 2280631)) (n := 12)
    (lo := (9894117 / 40000000)) (hi := (123676463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280631 / 1000000) = 1/(1000000 / 1280631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9894117 / 40000000) (123676463 / 500000000) (Real.log (1280631 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1280631 / 1000000) = -Real.log (1000000 / 1280631) := by
    rw [show ((1280631 / 1000000) : ℝ) = ((1000000 / 1280631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8234521 / 25000000) ≤ -Real.log (719369 / 1000000) ∧
    -Real.log (719369 / 1000000) ≤ (329380841 / 1000000000) := by
  have h := checkLog_sound (w := (280631 / 1719369)) (n := 12)
    (lo := (8234521 / 25000000)) (hi := (329380841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719369) = 1/(719369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-329380841 / 1000000000) (-8234521 / 25000000) (Real.log (719369 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (92217993 / 500000000) ≤ -Real.log (50000 / 60127) ∧
    -Real.log (50000 / 60127) ≤ (184435987 / 1000000000) := by
  have h := checkLog_sound (w := (10127 / 110127)) (n := 12)
    (lo := (92217993 / 500000000)) (hi := (184435987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60127 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60127 / 50000) = 1/(50000 / 60127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (92217993 / 500000000) (184435987 / 1000000000) (Real.log (60127 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60127 / 50000) = -Real.log (50000 / 60127) := by
    rw [show ((60127 / 50000) : ℝ) = ((50000 / 60127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113161801 / 500000000) ≤ -Real.log (39873 / 50000) ∧
    -Real.log (39873 / 50000) ≤ (226323603 / 1000000000) := by
  have h := checkLog_sound (w := (10127 / 89873)) (n := 12)
    (lo := (113161801 / 500000000)) (hi := (226323603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39873) = 1/(39873 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-226323603 / 1000000000) (-113161801 / 500000000) (Real.log (39873 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92351027 / 500000000) ≤ -Real.log (50000 / 60143) ∧
    -Real.log (50000 / 60143) ≤ (36940411 / 200000000) := by
  have h := checkLog_sound (w := (10143 / 110143)) (n := 12)
    (lo := (92351027 / 500000000)) (hi := (36940411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60143 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60143 / 50000) = 1/(50000 / 60143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92351027 / 500000000) (36940411 / 200000000) (Real.log (60143 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60143 / 50000) = -Real.log (50000 / 60143) := by
    rw [show ((60143 / 50000) : ℝ) = ((50000 / 60143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56681239 / 250000000) ≤ -Real.log (39857 / 50000) ∧
    -Real.log (39857 / 50000) ≤ (226724957 / 1000000000) := by
  have h := checkLog_sound (w := (10143 / 89857)) (n := 12)
    (lo := (56681239 / 250000000)) (hi := (226724957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39857) = 1/(39857 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-226724957 / 1000000000) (-56681239 / 250000000) (Real.log (39857 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (415999267 / 500000000) ≤ -Real.log (500000000000 / 1148953301127) ∧
    -Real.log (500000000000 / 1148953301127) ≤ (103999817 / 125000000) := by
  have h := checkLog_sound (w := (148953301127 / 2148953301127)) (n := 12)
    (lo := (69425677 / 500000000)) (hi := (27770271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148953301127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1148953301127 / 1000000000000) = 1/(500000000000 / 1148953301127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (415999267 / 500000000) (103999817 / 125000000) (Real.log (1148953301127 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1148953301127 / 500000000000) = -Real.log (500000000000 / 1148953301127) := by
    rw [show ((1148953301127 / 500000000000) : ℝ) = ((500000000000 / 1148953301127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (833385559 / 1000000000) ≤ -Real.log (500000000000 / 1150548033527) ∧
    -Real.log (500000000000 / 1150548033527) ≤ (833385561 / 1000000000) := by
  have h := checkLog_sound (w := (150548033527 / 2150548033527)) (n := 12)
    (lo := (140238379 / 1000000000)) (hi := (7011919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150548033527 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1150548033527 / 1000000000000) = 1/(500000000000 / 1150548033527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (833385559 / 1000000000) (833385561 / 1000000000) (Real.log (1150548033527 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1150548033527 / 500000000000) = -Real.log (500000000000 / 1150548033527) := by
    rw [show ((1150548033527 / 500000000000) : ℝ) = ((500000000000 / 1150548033527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (575811221 / 1000000000) ≤ -Real.log (250000000000 / 444643189579) ∧
    -Real.log (250000000000 / 444643189579) ≤ (287905611 / 500000000) := by
  have h := checkLog_sound (w := (194643189579 / 694643189579)) (n := 12)
    (lo := (575811221 / 1000000000)) (hi := (287905611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444643189579 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444643189579 / 250000000000) = 1/(250000000000 / 444643189579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (575811221 / 1000000000) (287905611 / 500000000) (Real.log (444643189579 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (444643189579 / 250000000000) = -Real.log (250000000000 / 444643189579) := by
    rw [show ((444643189579 / 250000000000) : ℝ) = ((250000000000 / 444643189579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (115346753 / 200000000) ≤ -Real.log (250000000000 / 445053581681) ∧
    -Real.log (250000000000 / 445053581681) ≤ (288366883 / 500000000) := by
  have h := checkLog_sound (w := (195053581681 / 695053581681)) (n := 12)
    (lo := (115346753 / 200000000)) (hi := (288366883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445053581681 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445053581681 / 250000000000) = 1/(250000000000 / 445053581681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (115346753 / 200000000) (288366883 / 500000000) (Real.log (445053581681 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (445053581681 / 250000000000) = -Real.log (250000000000 / 445053581681) := by
    rw [show ((445053581681 / 250000000000) : ℝ) = ((250000000000 / 445053581681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (102689897 / 250000000) ≤ -Real.log (125000000000 / 188495347729) ∧
    -Real.log (125000000000 / 188495347729) ≤ (410759589 / 1000000000) := by
  have h := checkLog_sound (w := (63495347729 / 313495347729)) (n := 12)
    (lo := (102689897 / 250000000)) (hi := (410759589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188495347729 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188495347729 / 125000000000) = 1/(125000000000 / 188495347729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (102689897 / 250000000) (410759589 / 1000000000) (Real.log (188495347729 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (188495347729 / 125000000000) = -Real.log (125000000000 / 188495347729) := by
    rw [show ((188495347729 / 125000000000) : ℝ) = ((125000000000 / 188495347729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (411427011 / 1000000000) ≤ -Real.log (5000000000 / 7544847831) ∧
    -Real.log (5000000000 / 7544847831) ≤ (102856753 / 250000000) := by
  have h := checkLog_sound (w := (2544847831 / 12544847831)) (n := 12)
    (lo := (411427011 / 1000000000)) (hi := (102856753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7544847831 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7544847831 / 5000000000) = 1/(5000000000 / 7544847831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (411427011 / 1000000000) (102856753 / 250000000) (Real.log (7544847831 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7544847831 / 5000000000) = -Real.log (5000000000 / 7544847831) := by
    rw [show ((7544847831 / 5000000000) : ℝ) = ((5000000000 / 7544847831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21011451 / 500000000) ≤ -Real.log (2397119551 / 2500000000) ∧
    -Real.log (2397119551 / 2500000000) ≤ (42022903 / 1000000000) := by
  have h := checkLog_sound (w := (102880449 / 4897119551)) (n := 12)
    (lo := (21011451 / 500000000)) (hi := (42022903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397119551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397119551) = 1/(2397119551 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42022903 / 1000000000) (-21011451 / 500000000) (Real.log (2397119551 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8377523 / 200000000) ≤ -Real.log (2397443871 / 2500000000) ∧
    -Real.log (2397443871 / 2500000000) ≤ (327247 / 7812500) := by
  have h := checkLog_sound (w := (102556129 / 4897443871)) (n := 12)
    (lo := (8377523 / 200000000)) (hi := (327247 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397443871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397443871) = 1/(2397443871 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-327247 / 7812500) (-8377523 / 200000000) (Real.log (2397443871 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell245
