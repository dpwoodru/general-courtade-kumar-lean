import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0205
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

theorem reflection_log_1_neg : (287779719 / 500000000) ≤ -Real.log (320 / 569) ∧
    -Real.log (320 / 569) ≤ (575559439 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 889)) (n := 12)
    (lo := (287779719 / 500000000)) (hi := (575559439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569 / 320) = 1/(320 / 569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (287779719 / 500000000) (575559439 / 1000000000) (Real.log (569 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (569 / 320) = -Real.log (320 / 569) := by
    rw [show ((569 / 320) : ℝ) = ((320 / 569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1505641117 / 1000000000) ≤ -Real.log (71 / 320) ∧
    -Real.log (71 / 320) ≤ (9410257 / 6250000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 71) = 1/(71 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-9410257 / 6250000) (-1505641117 / 1000000000) (Real.log (71 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (572214659 / 1000000000) ≤ -Real.log (3200 / 5671) ∧
    -Real.log (3200 / 5671) ≤ (28610733 / 50000000) := by
  have h := checkLog_sound (w := (2471 / 8871)) (n := 12)
    (lo := (572214659 / 1000000000)) (hi := (28610733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5671 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5671 / 3200) = 1/(3200 / 5671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (572214659 / 1000000000) (28610733 / 50000000) (Real.log (5671 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5671 / 3200) = -Real.log (3200 / 5671) := by
    rw [show ((5671 / 3200) : ℝ) = ((3200 / 5671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295846471 / 200000000) ≤ -Real.log (729 / 3200) ∧
    -Real.log (729 / 3200) ≤ (739616179 / 500000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 729) = 1/(729 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-739616179 / 500000000) (-295846471 / 200000000) (Real.log (729 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (442279081 / 1000000000) ≤ -Real.log (160 / 249) ∧
    -Real.log (160 / 249) ≤ (221139541 / 500000000) := by
  have h := checkLog_sound (w := (89 / 409)) (n := 12)
    (lo := (442279081 / 1000000000)) (hi := (221139541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 160) = 1/(160 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (442279081 / 1000000000) (221139541 / 500000000) (Real.log (249 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (249 / 160) = -Real.log (160 / 249) := by
    rw [show ((249 / 160) : ℝ) = ((160 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (812493937 / 1000000000) ≤ -Real.log (71 / 160) ∧
    -Real.log (71 / 160) ≤ (812493939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 71) = 1/(71 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-812493939 / 1000000000) (-812493937 / 1000000000) (Real.log (71 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (434619297 / 1000000000) ≤ -Real.log (1600 / 2471) ∧
    -Real.log (1600 / 2471) ≤ (217309649 / 500000000) := by
  have h := checkLog_sound (w := (871 / 4071)) (n := 12)
    (lo := (434619297 / 1000000000)) (hi := (217309649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 1600) = 1/(1600 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (434619297 / 1000000000) (217309649 / 500000000) (Real.log (2471 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2471 / 1600) = -Real.log (1600 / 2471) := by
    rw [show ((2471 / 1600) : ℝ) = ((1600 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31443407 / 40000000) ≤ -Real.log (729 / 1600) ∧
    -Real.log (729 / 1600) ≤ (786085177 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 729) = 1/(729 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-786085177 / 1000000000) (-31443407 / 40000000) (Real.log (729 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (307177241 / 500000000) ≤ -Real.log (1000000 / 1848463) ∧
    -Real.log (1000000 / 1848463) ≤ (614354483 / 1000000000) := by
  have h := checkLog_sound (w := (848463 / 2848463)) (n := 12)
    (lo := (307177241 / 500000000)) (hi := (614354483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1848463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1848463 / 1000000) = 1/(1000000 / 1848463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (307177241 / 500000000) (614354483 / 1000000000) (Real.log (1848463 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1848463 / 1000000) = -Real.log (1000000 / 1848463) := by
    rw [show ((1848463 / 1000000) : ℝ) = ((1000000 / 1848463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (943462729 / 500000000) ≤ -Real.log (151537 / 1000000) ∧
    -Real.log (151537 / 1000000) ≤ (1886925461 / 1000000000) := by
  have h := checkLog_sound (w := (98463 / 401537)) (n := 12)
    (lo := (250315549 / 500000000)) (hi := (500631099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 151537) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 151537) = 1/(151537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1886925461 / 1000000000) (-943462729 / 500000000) (Real.log (151537 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153984177 / 250000000) ≤ -Real.log (100000 / 185139) ∧
    -Real.log (100000 / 185139) ≤ (615936709 / 1000000000) := by
  have h := checkLog_sound (w := (85139 / 285139)) (n := 12)
    (lo := (153984177 / 250000000)) (hi := (615936709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185139 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185139 / 100000) = 1/(100000 / 185139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153984177 / 250000000) (615936709 / 1000000000) (Real.log (185139 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (185139 / 100000) = -Real.log (100000 / 185139) := by
    rw [show ((185139 / 100000) : ℝ) = ((100000 / 185139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1906429853 / 1000000000) ≤ -Real.log (14861 / 100000) ∧
    -Real.log (14861 / 100000) ≤ (59575933 / 31250000) := by
  have h := checkLog_sound (w := (10139 / 39861)) (n := 12)
    (lo := (520135493 / 1000000000)) (hi := (260067747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 14861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 14861) = 1/(14861 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59575933 / 31250000) (-1906429853 / 1000000000) (Real.log (14861 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151293517 / 250000000) ≤ -Real.log (1000000 / 1831571) ∧
    -Real.log (1000000 / 1831571) ≤ (605174069 / 1000000000) := by
  have h := checkLog_sound (w := (831571 / 2831571)) (n := 12)
    (lo := (151293517 / 250000000)) (hi := (605174069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831571 / 1000000) = 1/(1000000 / 1831571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151293517 / 250000000) (605174069 / 1000000000) (Real.log (1831571 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1831571 / 1000000) = -Real.log (1000000 / 1831571) := by
    rw [show ((1831571 / 1000000) : ℝ) = ((1000000 / 1831571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1781240981 / 1000000000) ≤ -Real.log (168429 / 1000000) ∧
    -Real.log (168429 / 1000000) ≤ (222655123 / 125000000) := by
  have h := checkLog_sound (w := (81571 / 418429)) (n := 12)
    (lo := (394946621 / 1000000000)) (hi := (197473311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168429) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 168429) = 1/(168429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-222655123 / 125000000) (-1781240981 / 1000000000) (Real.log (168429 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (607346343 / 1000000000) ≤ -Real.log (500000 / 917777) ∧
    -Real.log (500000 / 917777) ≤ (75918293 / 125000000) := by
  have h := checkLog_sound (w := (417777 / 1417777)) (n := 12)
    (lo := (607346343 / 1000000000)) (hi := (75918293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917777 / 500000) = 1/(500000 / 917777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (607346343 / 1000000000) (75918293 / 125000000) (Real.log (917777 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (917777 / 500000) = -Real.log (500000 / 917777) := by
    rw [show ((917777 / 500000) : ℝ) = ((500000 / 917777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1805173029 / 1000000000) ≤ -Real.log (82223 / 500000) ∧
    -Real.log (82223 / 500000) ≤ (225646629 / 125000000) := by
  have h := checkLog_sound (w := (42777 / 207223)) (n := 12)
    (lo := (418878669 / 1000000000)) (hi := (41887867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82223) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 82223) = 1/(82223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-225646629 / 125000000) (-1805173029 / 1000000000) (Real.log (82223 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (125063997 / 50000000) ≤ -Real.log (250000000000 / 3049524208609) ∧
    -Real.log (250000000000 / 3049524208609) ≤ (312659993 / 125000000) := by
  have h := checkLog_sound (w := (1049524208609 / 5049524208609)) (n := 12)
    (lo := (263649 / 625000)) (hi := (421838401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3049524208609 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3049524208609 / 2000000000000) = 1/(250000000000 / 3049524208609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (125063997 / 50000000) (312659993 / 125000000) (Real.log (3049524208609 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3049524208609 / 250000000000) = -Real.log (250000000000 / 3049524208609) := by
    rw [show ((3049524208609 / 250000000000) : ℝ) = ((250000000000 / 3049524208609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15764791 / 6250000) ≤ -Real.log (62500000000 / 778627784133) ∧
    -Real.log (62500000000 / 778627784133) ≤ (630591641 / 250000000) := by
  have h := checkLog_sound (w := (278627784133 / 1278627784133)) (n := 12)
    (lo := (22146251 / 50000000)) (hi := (442925021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778627784133 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(778627784133 / 500000000000) = 1/(62500000000 / 778627784133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15764791 / 6250000) (630591641 / 250000000) (Real.log (778627784133 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (778627784133 / 62500000000) = -Real.log (62500000000 / 778627784133) := by
    rw [show ((778627784133 / 62500000000) : ℝ) = ((62500000000 / 778627784133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2386415049 / 1000000000) ≤ -Real.log (250000000000 / 2718609918719) ∧
    -Real.log (250000000000 / 2718609918719) ≤ (2386415053 / 1000000000) := by
  have h := checkLog_sound (w := (718609918719 / 4718609918719)) (n := 12)
    (lo := (306973509 / 1000000000)) (hi := (30697351 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2718609918719 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2718609918719 / 2000000000000) = 1/(250000000000 / 2718609918719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2386415049 / 1000000000) (2386415053 / 1000000000) (Real.log (2718609918719 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2718609918719 / 250000000000) = -Real.log (250000000000 / 2718609918719) := by
    rw [show ((2718609918719 / 250000000000) : ℝ) = ((250000000000 / 2718609918719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2412519371 / 1000000000) ≤ -Real.log (250000000000 / 2790511778943) ∧
    -Real.log (250000000000 / 2790511778943) ≤ (3860031 / 1600000) := by
  have h := checkLog_sound (w := (790511778943 / 4790511778943)) (n := 12)
    (lo := (333077831 / 1000000000)) (hi := (41634729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2790511778943 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2790511778943 / 2000000000000) = 1/(250000000000 / 2790511778943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2412519371 / 1000000000) (3860031 / 1600000) (Real.log (2790511778943 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2790511778943 / 250000000000) = -Real.log (250000000000 / 2790511778943) := by
    rw [show ((2790511778943 / 250000000000) : ℝ) = ((250000000000 / 2790511778943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0205
