import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0405
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

theorem reflection_log_1_neg : (777449 / 3906250) ≤ -Real.log (2048 / 2499) ∧
    -Real.log (2048 / 2499) ≤ (39805389 / 200000000) := by
  have h := checkLog_sound (w := (451 / 4547)) (n := 12)
    (lo := (777449 / 3906250)) (hi := (39805389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2048) = 1/(2048 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (777449 / 3906250) (39805389 / 200000000) (Real.log (2499 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2499 / 2048) = -Real.log (2048 / 2499) := by
    rw [show ((2499 / 2048) : ℝ) = ((2048 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (248736837 / 1000000000) ≤ -Real.log (1597 / 2048) ∧
    -Real.log (1597 / 2048) ≤ (124368419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3645)) (n := 12)
    (lo := (248736837 / 1000000000)) (hi := (124368419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1597) = 1/(1597 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-124368419 / 500000000) (-248736837 / 1000000000) (Real.log (1597 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198786819 / 1000000000) ≤ -Real.log (2560 / 3123) ∧
    -Real.log (2560 / 3123) ≤ (9939341 / 50000000) := by
  have h := checkLog_sound (w := (563 / 5683)) (n := 12)
    (lo := (198786819 / 1000000000)) (hi := (9939341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123 / 2560) = 1/(2560 / 3123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198786819 / 1000000000) (9939341 / 50000000) (Real.log (3123 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3123 / 2560) = -Real.log (2560 / 3123) := by
    rw [show ((3123 / 2560) : ℝ) = ((2560 / 3123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (62090301 / 250000000) ≤ -Real.log (1997 / 2560) ∧
    -Real.log (1997 / 2560) ≤ (49672241 / 200000000) := by
  have h := checkLog_sound (w := (563 / 4557)) (n := 12)
    (lo := (62090301 / 250000000)) (hi := (49672241 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1997) = 1/(1997 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49672241 / 200000000) (-62090301 / 250000000) (Real.log (1997 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (364941463 / 1000000000) ≤ -Real.log (1024 / 1475) ∧
    -Real.log (1024 / 1475) ≤ (45617683 / 125000000) := by
  have h := checkLog_sound (w := (451 / 2499)) (n := 12)
    (lo := (364941463 / 1000000000)) (hi := (45617683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475 / 1024) = 1/(1024 / 1475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (364941463 / 1000000000) (45617683 / 125000000) (Real.log (1475 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1475 / 1024) = -Real.log (1024 / 1475) := by
    rw [show ((1475 / 1024) : ℝ) = ((1024 / 1475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (72573261 / 125000000) ≤ -Real.log (573 / 1024) ∧
    -Real.log (573 / 1024) ≤ (580586089 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 1597)) (n := 12)
    (lo := (72573261 / 125000000)) (hi := (580586089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 573) = 1/(573 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-580586089 / 1000000000) (-72573261 / 125000000) (Real.log (573 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1822673 / 5000000) ≤ -Real.log (1280 / 1843) ∧
    -Real.log (1280 / 1843) ≤ (364534601 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3123)) (n := 12)
    (lo := (1822673 / 5000000)) (hi := (364534601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843 / 1280) = 1/(1280 / 1843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1822673 / 5000000) (364534601 / 1000000000) (Real.log (1843 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1843 / 1280) = -Real.log (1280 / 1843) := by
    rw [show ((1843 / 1280) : ℝ) = ((1280 / 1843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144884879 / 250000000) ≤ -Real.log (717 / 1280) ∧
    -Real.log (717 / 1280) ≤ (579539517 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1997)) (n := 12)
    (lo := (144884879 / 250000000)) (hi := (579539517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 717) = 1/(717 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-579539517 / 1000000000) (-144884879 / 250000000) (Real.log (717 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6822103 / 25000000) ≤ -Real.log (250000 / 328437) ∧
    -Real.log (250000 / 328437) ≤ (272884121 / 1000000000) := by
  have h := checkLog_sound (w := (78437 / 578437)) (n := 12)
    (lo := (6822103 / 25000000)) (hi := (272884121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328437 / 250000) = 1/(250000 / 328437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6822103 / 25000000) (272884121 / 1000000000) (Real.log (328437 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328437 / 250000) = -Real.log (250000 / 328437) := by
    rw [show ((328437 / 250000) : ℝ) = ((250000 / 328437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (376510371 / 1000000000) ≤ -Real.log (171563 / 250000) ∧
    -Real.log (171563 / 250000) ≤ (94127593 / 250000000) := by
  have h := checkLog_sound (w := (78437 / 421563)) (n := 12)
    (lo := (376510371 / 1000000000)) (hi := (94127593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171563) = 1/(171563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94127593 / 250000000) (-376510371 / 1000000000) (Real.log (171563 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68302273 / 250000000) ≤ -Real.log (40000 / 52567) ∧
    -Real.log (40000 / 52567) ≤ (273209093 / 1000000000) := by
  have h := checkLog_sound (w := (12567 / 92567)) (n := 12)
    (lo := (68302273 / 250000000)) (hi := (273209093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52567 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52567 / 40000) = 1/(40000 / 52567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68302273 / 250000000) (273209093 / 1000000000) (Real.log (52567 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (52567 / 40000) = -Real.log (40000 / 52567) := by
    rw [show ((52567 / 40000) : ℝ) = ((40000 / 52567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75426557 / 200000000) ≤ -Real.log (27433 / 40000) ∧
    -Real.log (27433 / 40000) ≤ (188566393 / 500000000) := by
  have h := checkLog_sound (w := (12567 / 67433)) (n := 12)
    (lo := (75426557 / 200000000)) (hi := (188566393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27433) = 1/(27433 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188566393 / 500000000) (-75426557 / 200000000) (Real.log (27433 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102721101 / 500000000) ≤ -Real.log (250000 / 307017) ∧
    -Real.log (250000 / 307017) ≤ (205442203 / 1000000000) := by
  have h := checkLog_sound (w := (57017 / 557017)) (n := 12)
    (lo := (102721101 / 500000000)) (hi := (205442203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307017 / 250000) = 1/(250000 / 307017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102721101 / 500000000) (205442203 / 1000000000) (Real.log (307017 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (307017 / 250000) = -Real.log (250000 / 307017) := by
    rw [show ((307017 / 250000) : ℝ) = ((250000 / 307017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51771763 / 200000000) ≤ -Real.log (192983 / 250000) ∧
    -Real.log (192983 / 250000) ≤ (4044669 / 15625000) := by
  have h := checkLog_sound (w := (57017 / 442983)) (n := 12)
    (lo := (51771763 / 200000000)) (hi := (4044669 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192983) = 1/(192983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4044669 / 15625000) (-51771763 / 200000000) (Real.log (192983 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205709253 / 1000000000) ≤ -Real.log (250000 / 307099) ∧
    -Real.log (250000 / 307099) ≤ (102854627 / 500000000) := by
  have h := checkLog_sound (w := (57099 / 557099)) (n := 12)
    (lo := (205709253 / 1000000000)) (hi := (102854627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307099 / 250000) = 1/(250000 / 307099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205709253 / 1000000000) (102854627 / 500000000) (Real.log (307099 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (307099 / 250000) = -Real.log (250000 / 307099) := by
    rw [show ((307099 / 250000) : ℝ) = ((250000 / 307099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (259283813 / 1000000000) ≤ -Real.log (192901 / 250000) ∧
    -Real.log (192901 / 250000) ≤ (129641907 / 500000000) := by
  have h := checkLog_sound (w := (57099 / 442901)) (n := 12)
    (lo := (259283813 / 1000000000)) (hi := (129641907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192901) = 1/(192901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-129641907 / 500000000) (-259283813 / 1000000000) (Real.log (192901 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (162348623 / 250000000) ≤ -Real.log (125000000000 / 239297663249) ∧
    -Real.log (125000000000 / 239297663249) ≤ (649394493 / 1000000000) := by
  have h := checkLog_sound (w := (114297663249 / 364297663249)) (n := 12)
    (lo := (162348623 / 250000000)) (hi := (649394493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239297663249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239297663249 / 125000000000) = 1/(125000000000 / 239297663249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (162348623 / 250000000) (649394493 / 1000000000) (Real.log (239297663249 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239297663249 / 125000000000) = -Real.log (125000000000 / 239297663249) := by
    rw [show ((239297663249 / 125000000000) : ℝ) = ((125000000000 / 239297663249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (325170939 / 500000000) ≤ -Real.log (20000000000 / 38323916451) ∧
    -Real.log (20000000000 / 38323916451) ≤ (650341879 / 1000000000) := by
  have h := checkLog_sound (w := (18323916451 / 58323916451)) (n := 12)
    (lo := (325170939 / 500000000)) (hi := (650341879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38323916451 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38323916451 / 20000000000) = 1/(20000000000 / 38323916451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (325170939 / 500000000) (650341879 / 1000000000) (Real.log (38323916451 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (38323916451 / 20000000000) = -Real.log (20000000000 / 38323916451) := by
    rw [show ((38323916451 / 20000000000) : ℝ) = ((20000000000 / 38323916451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (232150509 / 500000000) ≤ -Real.log (250000000000 / 397725447319) ∧
    -Real.log (250000000000 / 397725447319) ≤ (464301019 / 1000000000) := by
  have h := checkLog_sound (w := (147725447319 / 647725447319)) (n := 12)
    (lo := (232150509 / 500000000)) (hi := (464301019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397725447319 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397725447319 / 250000000000) = 1/(250000000000 / 397725447319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (232150509 / 500000000) (464301019 / 1000000000) (Real.log (397725447319 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (397725447319 / 250000000000) = -Real.log (250000000000 / 397725447319) := by
    rw [show ((397725447319 / 250000000000) : ℝ) = ((250000000000 / 397725447319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (464993067 / 1000000000) ≤ -Real.log (250000000000 / 398000787969) ∧
    -Real.log (250000000000 / 398000787969) ≤ (116248267 / 250000000) := by
  have h := checkLog_sound (w := (148000787969 / 648000787969)) (n := 12)
    (lo := (464993067 / 1000000000)) (hi := (116248267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398000787969 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398000787969 / 250000000000) = 1/(250000000000 / 398000787969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (464993067 / 1000000000) (116248267 / 250000000) (Real.log (398000787969 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398000787969 / 250000000000) = -Real.log (250000000000 / 398000787969) := by
    rw [show ((398000787969 / 250000000000) : ℝ) = ((250000000000 / 398000787969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0405
