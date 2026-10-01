import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell126
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

theorem reflection_log_1_neg : (8780317 / 31250000) ≤ -Real.log (5120 / 6781) ∧
    -Real.log (5120 / 6781) ≤ (56194029 / 200000000) := by
  have h := checkLog_sound (w := (1661 / 11901)) (n := 12)
    (lo := (8780317 / 31250000)) (hi := (56194029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6781 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6781 / 5120) = 1/(5120 / 6781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8780317 / 31250000) (56194029 / 200000000) (Real.log (6781 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6781 / 5120) = -Real.log (5120 / 6781) := by
    rw [show ((6781 / 5120) : ℝ) = ((5120 / 6781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (392174909 / 1000000000) ≤ -Real.log (3459 / 5120) ∧
    -Real.log (3459 / 5120) ≤ (39217491 / 100000000) := by
  have h := checkLog_sound (w := (1661 / 8579)) (n := 12)
    (lo := (392174909 / 1000000000)) (hi := (39217491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3459) = 1/(3459 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-39217491 / 100000000) (-392174909 / 1000000000) (Real.log (3459 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140263817 / 500000000) ≤ -Real.log (2560 / 3389) ∧
    -Real.log (2560 / 3389) ≤ (56105527 / 200000000) := by
  have h := checkLog_sound (w := (829 / 5949)) (n := 12)
    (lo := (140263817 / 500000000)) (hi := (56105527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3389 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3389 / 2560) = 1/(2560 / 3389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140263817 / 500000000) (56105527 / 200000000) (Real.log (3389 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3389 / 2560) = -Real.log (2560 / 3389) := by
    rw [show ((3389 / 2560) : ℝ) = ((2560 / 3389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (195653991 / 500000000) ≤ -Real.log (1731 / 2560) ∧
    -Real.log (1731 / 2560) ≤ (391307983 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 4291)) (n := 12)
    (lo := (195653991 / 500000000)) (hi := (391307983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1731) = 1/(1731 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-391307983 / 1000000000) (-195653991 / 500000000) (Real.log (1731 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5175903 / 25000000) ≤ -Real.log (1000000 / 1230027) ∧
    -Real.log (1000000 / 1230027) ≤ (207036121 / 1000000000) := by
  have h := checkLog_sound (w := (230027 / 2230027)) (n := 12)
    (lo := (5175903 / 25000000)) (hi := (207036121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230027 / 1000000) = 1/(1000000 / 1230027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5175903 / 25000000) (207036121 / 1000000000) (Real.log (1230027 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230027 / 1000000) = -Real.log (1000000 / 1230027) := by
    rw [show ((1230027 / 1000000) : ℝ) = ((1000000 / 1230027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (261399829 / 1000000000) ≤ -Real.log (769973 / 1000000) ∧
    -Real.log (769973 / 1000000) ≤ (26139983 / 100000000) := by
  have h := checkLog_sound (w := (230027 / 1769973)) (n := 12)
    (lo := (261399829 / 1000000000)) (hi := (26139983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769973) = 1/(769973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26139983 / 100000000) (-261399829 / 1000000000) (Real.log (769973 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20737833 / 100000000) ≤ -Real.log (62500 / 76903) ∧
    -Real.log (62500 / 76903) ≤ (207378331 / 1000000000) := by
  have h := checkLog_sound (w := (14403 / 139403)) (n := 12)
    (lo := (20737833 / 100000000)) (hi := (207378331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76903 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76903 / 62500) = 1/(62500 / 76903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20737833 / 100000000) (207378331 / 1000000000) (Real.log (76903 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (76903 / 62500) = -Real.log (62500 / 76903) := by
    rw [show ((76903 / 62500) : ℝ) = ((62500 / 76903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (261946751 / 1000000000) ≤ -Real.log (48097 / 62500) ∧
    -Real.log (48097 / 62500) ≤ (2046459 / 7812500) := by
  have h := checkLog_sound (w := (14403 / 110597)) (n := 12)
    (lo := (261946751 / 1000000000)) (hi := (2046459 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48097) = 1/(48097 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2046459 / 7812500) (-261946751 / 1000000000) (Real.log (48097 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38196151 / 250000000) ≤ -Real.log (500000 / 582537) ∧
    -Real.log (500000 / 582537) ≤ (30556921 / 200000000) := by
  have h := checkLog_sound (w := (82537 / 1082537)) (n := 12)
    (lo := (38196151 / 250000000)) (hi := (30556921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582537 / 500000) = 1/(500000 / 582537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38196151 / 250000000) (30556921 / 200000000) (Real.log (582537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (582537 / 500000) = -Real.log (500000 / 582537) := by
    rw [show ((582537 / 500000) : ℝ) = ((500000 / 582537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9020609 / 50000000) ≤ -Real.log (417463 / 500000) ∧
    -Real.log (417463 / 500000) ≤ (180412181 / 1000000000) := by
  have h := checkLog_sound (w := (82537 / 917463)) (n := 12)
    (lo := (9020609 / 50000000)) (hi := (180412181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417463) = 1/(417463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180412181 / 1000000000) (-9020609 / 50000000) (Real.log (417463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9565719 / 62500000) ≤ -Real.log (200000 / 233077) ∧
    -Real.log (200000 / 233077) ≤ (30610301 / 200000000) := by
  have h := checkLog_sound (w := (33077 / 433077)) (n := 12)
    (lo := (9565719 / 62500000)) (hi := (30610301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233077 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233077 / 200000) = 1/(200000 / 233077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9565719 / 62500000) (30610301 / 200000000) (Real.log (233077 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (233077 / 200000) = -Real.log (200000 / 233077) := by
    rw [show ((233077 / 200000) : ℝ) = ((200000 / 233077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90392369 / 500000000) ≤ -Real.log (166923 / 200000) ∧
    -Real.log (166923 / 200000) ≤ (180784739 / 1000000000) := by
  have h := checkLog_sound (w := (33077 / 366923)) (n := 12)
    (lo := (90392369 / 500000000)) (hi := (180784739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166923) = 1/(166923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180784739 / 1000000000) (-90392369 / 500000000) (Real.log (166923 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20994863 / 31250000) ≤ -Real.log (125000000000 / 244728480647) ∧
    -Real.log (125000000000 / 244728480647) ≤ (671835617 / 1000000000) := by
  have h := checkLog_sound (w := (119728480647 / 369728480647)) (n := 12)
    (lo := (20994863 / 31250000)) (hi := (671835617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244728480647 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244728480647 / 125000000000) = 1/(125000000000 / 244728480647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20994863 / 31250000) (671835617 / 1000000000) (Real.log (244728480647 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (244728480647 / 125000000000) = -Real.log (125000000000 / 244728480647) := by
    rw [show ((244728480647 / 125000000000) : ℝ) = ((125000000000 / 244728480647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (673145053 / 1000000000) ≤ -Real.log (50000000000 / 98019658861) ∧
    -Real.log (50000000000 / 98019658861) ≤ (336572527 / 500000000) := by
  have h := checkLog_sound (w := (48019658861 / 148019658861)) (n := 12)
    (lo := (673145053 / 1000000000)) (hi := (336572527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98019658861 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98019658861 / 50000000000) = 1/(50000000000 / 98019658861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (673145053 / 1000000000) (336572527 / 500000000) (Real.log (98019658861 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (98019658861 / 50000000000) = -Real.log (50000000000 / 98019658861) := by
    rw [show ((98019658861 / 50000000000) : ℝ) = ((50000000000 / 98019658861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (9368719 / 20000000) ≤ -Real.log (250000000000 / 399373419587) ∧
    -Real.log (250000000000 / 399373419587) ≤ (468435951 / 1000000000) := by
  have h := checkLog_sound (w := (149373419587 / 649373419587)) (n := 12)
    (lo := (9368719 / 20000000)) (hi := (468435951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399373419587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399373419587 / 250000000000) = 1/(250000000000 / 399373419587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9368719 / 20000000) (468435951 / 1000000000) (Real.log (399373419587 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399373419587 / 250000000000) = -Real.log (250000000000 / 399373419587) := by
    rw [show ((399373419587 / 250000000000) : ℝ) = ((250000000000 / 399373419587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (234662541 / 500000000) ≤ -Real.log (500000000000 / 799457346613) ∧
    -Real.log (500000000000 / 799457346613) ≤ (469325083 / 1000000000) := by
  have h := checkLog_sound (w := (299457346613 / 1299457346613)) (n := 12)
    (lo := (234662541 / 500000000)) (hi := (469325083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799457346613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799457346613 / 500000000000) = 1/(500000000000 / 799457346613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (234662541 / 500000000) (469325083 / 1000000000) (Real.log (799457346613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (799457346613 / 500000000000) = -Real.log (500000000000 / 799457346613) := by
    rw [show ((799457346613 / 500000000000) : ℝ) = ((500000000000 / 799457346613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (66639357 / 200000000) ≤ -Real.log (500000000000 / 697710934861) ∧
    -Real.log (500000000000 / 697710934861) ≤ (166598393 / 500000000) := by
  have h := checkLog_sound (w := (197710934861 / 1197710934861)) (n := 12)
    (lo := (66639357 / 200000000)) (hi := (166598393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697710934861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697710934861 / 500000000000) = 1/(500000000000 / 697710934861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (66639357 / 200000000) (166598393 / 500000000) (Real.log (697710934861 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (697710934861 / 500000000000) = -Real.log (500000000000 / 697710934861) := by
    rw [show ((697710934861 / 500000000000) : ℝ) = ((500000000000 / 697710934861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (166918121 / 500000000) ≤ -Real.log (250000000000 / 349078617087) ∧
    -Real.log (250000000000 / 349078617087) ≤ (333836243 / 1000000000) := by
  have h := checkLog_sound (w := (99078617087 / 599078617087)) (n := 12)
    (lo := (166918121 / 500000000)) (hi := (333836243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349078617087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349078617087 / 250000000000) = 1/(250000000000 / 349078617087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (166918121 / 500000000) (333836243 / 1000000000) (Real.log (349078617087 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (349078617087 / 250000000000) = -Real.log (250000000000 / 349078617087) := by
    rw [show ((349078617087 / 250000000000) : ℝ) = ((250000000000 / 349078617087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27733233 / 1000000000) ≤ -Real.log (38905912071 / 40000000000) ∧
    -Real.log (38905912071 / 40000000000) ≤ (13866617 / 500000000) := by
  have h := checkLog_sound (w := (1094087929 / 78905912071)) (n := 12)
    (lo := (27733233 / 1000000000)) (hi := (13866617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38905912071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38905912071) = 1/(38905912071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13866617 / 500000000) (-27733233 / 1000000000) (Real.log (38905912071 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3453447 / 125000000) ≤ -Real.log (243187643631 / 250000000000) ∧
    -Real.log (243187643631 / 250000000000) ≤ (27627577 / 1000000000) := by
  have h := checkLog_sound (w := (6812356369 / 493187643631)) (n := 12)
    (lo := (3453447 / 125000000)) (hi := (27627577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243187643631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243187643631) = 1/(243187643631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27627577 / 1000000000) (-3453447 / 125000000) (Real.log (243187643631 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell126
