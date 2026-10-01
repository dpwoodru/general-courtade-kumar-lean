import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0160
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

theorem reflection_log_1_neg : (70868503 / 250000000) ≤ -Real.log (2560 / 3399) ∧
    -Real.log (2560 / 3399) ≤ (283474013 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 5959)) (n := 12)
    (lo := (70868503 / 250000000)) (hi := (283474013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3399 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3399 / 2560) = 1/(2560 / 3399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (70868503 / 250000000) (283474013 / 1000000000) (Real.log (3399 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3399 / 2560) = -Real.log (2560 / 3399) := by
    rw [show ((3399 / 2560) : ℝ) = ((2560 / 3399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (397101741 / 1000000000) ≤ -Real.log (1721 / 2560) ∧
    -Real.log (1721 / 2560) ≤ (198550871 / 500000000) := by
  have h := checkLog_sound (w := (839 / 4281)) (n := 12)
    (lo := (397101741 / 1000000000)) (hi := (198550871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1721) = 1/(1721 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-198550871 / 500000000) (-397101741 / 1000000000) (Real.log (1721 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8844769 / 31250000) ≤ -Real.log (1024 / 1359) ∧
    -Real.log (1024 / 1359) ≤ (283032609 / 1000000000) := by
  have h := checkLog_sound (w := (335 / 2383)) (n := 12)
    (lo := (8844769 / 31250000)) (hi := (283032609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1024) = 1/(1024 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8844769 / 31250000) (283032609 / 1000000000) (Real.log (1359 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1359 / 1024) = -Real.log (1024 / 1359) := by
    rw [show ((1359 / 1024) : ℝ) = ((1024 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (198115267 / 500000000) ≤ -Real.log (689 / 1024) ∧
    -Real.log (689 / 1024) ≤ (79246107 / 200000000) := by
  have h := checkLog_sound (w := (335 / 1713)) (n := 12)
    (lo := (198115267 / 500000000)) (hi := (79246107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 689) = 1/(689 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-79246107 / 200000000) (-198115267 / 500000000) (Real.log (689 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (504084201 / 1000000000) ≤ -Real.log (1280 / 2119) ∧
    -Real.log (1280 / 2119) ≤ (252042101 / 500000000) := by
  have h := checkLog_sound (w := (839 / 3399)) (n := 12)
    (lo := (504084201 / 1000000000)) (hi := (252042101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2119 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2119 / 1280) = 1/(1280 / 2119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (504084201 / 1000000000) (252042101 / 500000000) (Real.log (2119 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2119 / 1280) = -Real.log (1280 / 2119) := by
    rw [show ((2119 / 1280) : ℝ) = ((1280 / 2119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13319631 / 12500000) ≤ -Real.log (441 / 1280) ∧
    -Real.log (441 / 1280) ≤ (532785241 / 500000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 441) = 1/(441 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-532785241 / 500000000) (-13319631 / 12500000) (Real.log (441 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (503376069 / 1000000000) ≤ -Real.log (512 / 847) ∧
    -Real.log (512 / 847) ≤ (50337607 / 100000000) := by
  have h := checkLog_sound (w := (335 / 1359)) (n := 12)
    (lo := (503376069 / 1000000000)) (hi := (50337607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847 / 512) = 1/(512 / 847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (503376069 / 1000000000) (50337607 / 100000000) (Real.log (847 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (847 / 512) = -Real.log (512 / 847) := by
    rw [show ((847 / 512) : ℝ) = ((512 / 847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1062174891 / 1000000000) ≤ -Real.log (177 / 512) ∧
    -Real.log (177 / 512) ≤ (1062174893 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 177) = 1/(177 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1062174893 / 1000000000) (-1062174891 / 1000000000) (Real.log (177 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (387199299 / 1000000000) ≤ -Real.log (20000 / 29457) ∧
    -Real.log (20000 / 29457) ≤ (3871993 / 10000000) := by
  have h := checkLog_sound (w := (9457 / 49457)) (n := 12)
    (lo := (387199299 / 1000000000)) (hi := (3871993 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29457 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29457 / 20000) = 1/(20000 / 29457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (387199299 / 1000000000) (3871993 / 10000000) (Real.log (29457 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29457 / 20000) = -Real.log (20000 / 29457) := by
    rw [show ((29457 / 20000) : ℝ) = ((20000 / 29457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (32013507 / 50000000) ≤ -Real.log (10543 / 20000) ∧
    -Real.log (10543 / 20000) ≤ (640270141 / 1000000000) := by
  have h := checkLog_sound (w := (9457 / 30543)) (n := 12)
    (lo := (32013507 / 50000000)) (hi := (640270141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 10543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 10543) = 1/(10543 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-640270141 / 1000000000) (-32013507 / 50000000) (Real.log (10543 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (387806101 / 1000000000) ≤ -Real.log (62500 / 92109) ∧
    -Real.log (62500 / 92109) ≤ (193903051 / 500000000) := by
  have h := checkLog_sound (w := (29609 / 154609)) (n := 12)
    (lo := (387806101 / 1000000000)) (hi := (193903051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92109 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92109 / 62500) = 1/(62500 / 92109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (387806101 / 1000000000) (193903051 / 500000000) (Real.log (92109 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (92109 / 62500) = -Real.log (62500 / 92109) := by
    rw [show ((92109 / 62500) : ℝ) = ((62500 / 92109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (160491873 / 250000000) ≤ -Real.log (32891 / 62500) ∧
    -Real.log (32891 / 62500) ≤ (641967493 / 1000000000) := by
  have h := checkLog_sound (w := (29609 / 95391)) (n := 12)
    (lo := (160491873 / 250000000)) (hi := (641967493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 32891) = 1/(32891 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-641967493 / 1000000000) (-160491873 / 250000000) (Real.log (32891 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (304794319 / 1000000000) ≤ -Real.log (500000 / 678173) ∧
    -Real.log (500000 / 678173) ≤ (3809929 / 12500000) := by
  have h := checkLog_sound (w := (178173 / 1178173)) (n := 12)
    (lo := (304794319 / 1000000000)) (hi := (3809929 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678173 / 500000) = 1/(500000 / 678173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (304794319 / 1000000000) (3809929 / 12500000) (Real.log (678173 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (678173 / 500000) = -Real.log (500000 / 678173) := by
    rw [show ((678173 / 500000) : ℝ) = ((500000 / 678173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (110148491 / 250000000) ≤ -Real.log (321827 / 500000) ∧
    -Real.log (321827 / 500000) ≤ (88118793 / 200000000) := by
  have h := checkLog_sound (w := (178173 / 821827)) (n := 12)
    (lo := (110148491 / 250000000)) (hi := (88118793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321827) = 1/(321827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-88118793 / 200000000) (-110148491 / 250000000) (Real.log (321827 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61071193 / 200000000) ≤ -Real.log (250000 / 339277) ∧
    -Real.log (250000 / 339277) ≤ (152677983 / 500000000) := by
  have h := checkLog_sound (w := (89277 / 589277)) (n := 12)
    (lo := (61071193 / 200000000)) (hi := (152677983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339277 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339277 / 250000) = 1/(250000 / 339277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61071193 / 200000000) (152677983 / 500000000) (Real.log (339277 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (339277 / 250000) = -Real.log (250000 / 339277) := by
    rw [show ((339277 / 250000) : ℝ) = ((250000 / 339277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (441778531 / 1000000000) ≤ -Real.log (160723 / 250000) ∧
    -Real.log (160723 / 250000) ≤ (110444633 / 250000000) := by
  have h := checkLog_sound (w := (89277 / 410723)) (n := 12)
    (lo := (441778531 / 1000000000)) (hi := (110444633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160723) = 1/(160723 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-110444633 / 250000000) (-441778531 / 1000000000) (Real.log (160723 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1027469439 / 1000000000) ≤ -Real.log (500000000000 / 1396993265673) ∧
    -Real.log (500000000000 / 1396993265673) ≤ (1027469441 / 1000000000) := by
  have h := checkLog_sound (w := (396993265673 / 2396993265673)) (n := 12)
    (lo := (334322259 / 1000000000)) (hi := (16716113 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1396993265673 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1396993265673 / 1000000000000) = 1/(500000000000 / 1396993265673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1027469439 / 1000000000) (1027469441 / 1000000000) (Real.log (1396993265673 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1396993265673 / 500000000000) = -Real.log (500000000000 / 1396993265673) := by
    rw [show ((1396993265673 / 500000000000) : ℝ) = ((500000000000 / 1396993265673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1029773593 / 1000000000) ≤ -Real.log (500000000000 / 1400215864523) ∧
    -Real.log (500000000000 / 1400215864523) ≤ (205954719 / 200000000) := by
  have h := checkLog_sound (w := (400215864523 / 2400215864523)) (n := 12)
    (lo := (336626413 / 1000000000)) (hi := (168313207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1400215864523 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1400215864523 / 1000000000000) = 1/(500000000000 / 1400215864523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1029773593 / 1000000000) (205954719 / 200000000) (Real.log (1400215864523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1400215864523 / 500000000000) = -Real.log (500000000000 / 1400215864523) := by
    rw [show ((1400215864523 / 500000000000) : ℝ) = ((500000000000 / 1400215864523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (372694141 / 500000000) ≤ -Real.log (500000000000 / 1053629745173) ∧
    -Real.log (500000000000 / 1053629745173) ≤ (186347071 / 250000000) := by
  have h := checkLog_sound (w := (53629745173 / 2053629745173)) (n := 12)
    (lo := (26120551 / 500000000)) (hi := (52241103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053629745173 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1053629745173 / 1000000000000) = 1/(500000000000 / 1053629745173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (372694141 / 500000000) (186347071 / 250000000) (Real.log (1053629745173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1053629745173 / 500000000000) = -Real.log (500000000000 / 1053629745173) := by
    rw [show ((1053629745173 / 500000000000) : ℝ) = ((500000000000 / 1053629745173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (149426899 / 200000000) ≤ -Real.log (10000000000 / 21109424289) ∧
    -Real.log (10000000000 / 21109424289) ≤ (747134497 / 1000000000) := by
  have h := checkLog_sound (w := (1109424289 / 41109424289)) (n := 12)
    (lo := (10797463 / 200000000)) (hi := (13496829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21109424289 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21109424289 / 20000000000) = 1/(10000000000 / 21109424289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (149426899 / 200000000) (747134497 / 1000000000) (Real.log (21109424289 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21109424289 / 10000000000) = -Real.log (10000000000 / 21109424289) := by
    rw [show ((21109424289 / 10000000000) : ℝ) = ((10000000000 / 21109424289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0160
