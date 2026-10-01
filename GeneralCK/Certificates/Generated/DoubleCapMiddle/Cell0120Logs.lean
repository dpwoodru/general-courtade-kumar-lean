import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0120
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

theorem reflection_log_1_neg : (158231557 / 500000000) ≤ -Real.log (2560 / 3513) ∧
    -Real.log (2560 / 3513) ≤ (63292623 / 200000000) := by
  have h := checkLog_sound (w := (953 / 6073)) (n := 12)
    (lo := (158231557 / 500000000)) (hi := (63292623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3513 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3513 / 2560) = 1/(2560 / 3513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (158231557 / 500000000) (63292623 / 200000000) (Real.log (3513 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3513 / 2560) = -Real.log (2560 / 3513) := by
    rw [show ((3513 / 2560) : ℝ) = ((2560 / 3513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (465638171 / 1000000000) ≤ -Real.log (1607 / 2560) ∧
    -Real.log (1607 / 2560) ≤ (116409543 / 250000000) := by
  have h := checkLog_sound (w := (953 / 4167)) (n := 12)
    (lo := (465638171 / 1000000000)) (hi := (116409543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1607) = 1/(1607 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-116409543 / 250000000) (-465638171 / 1000000000) (Real.log (1607 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157804389 / 500000000) ≤ -Real.log (256 / 351) ∧
    -Real.log (256 / 351) ≤ (315608779 / 1000000000) := by
  have h := checkLog_sound (w := (95 / 607)) (n := 12)
    (lo := (157804389 / 500000000)) (hi := (315608779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 256) = 1/(256 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157804389 / 500000000) (315608779 / 1000000000) (Real.log (351 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (351 / 256) = -Real.log (256 / 351) := by
    rw [show ((351 / 256) : ℝ) = ((256 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (463773079 / 1000000000) ≤ -Real.log (161 / 256) ∧
    -Real.log (161 / 256) ≤ (11594327 / 25000000) := by
  have h := checkLog_sound (w := (95 / 417)) (n := 12)
    (lo := (463773079 / 1000000000)) (hi := (11594327 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 161) = 1/(161 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11594327 / 25000000) (-463773079 / 1000000000) (Real.log (161 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (278242947 / 500000000) ≤ -Real.log (1280 / 2233) ∧
    -Real.log (1280 / 2233) ≤ (111297179 / 200000000) := by
  have h := checkLog_sound (w := (953 / 3513)) (n := 12)
    (lo := (278242947 / 500000000)) (hi := (111297179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2233 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2233 / 1280) = 1/(1280 / 2233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (278242947 / 500000000) (111297179 / 200000000) (Real.log (2233 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2233 / 1280) = -Real.log (1280 / 2233) := by
    rw [show ((2233 / 1280) : ℝ) = ((1280 / 2233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (272931037 / 200000000) ≤ -Real.log (327 / 1280) ∧
    -Real.log (327 / 1280) ≤ (1364655187 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 327) = 1/(327 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1364655187 / 1000000000) (-272931037 / 200000000) (Real.log (327 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (555141507 / 1000000000) ≤ -Real.log (128 / 223) ∧
    -Real.log (128 / 223) ≤ (138785377 / 250000000) := by
  have h := checkLog_sound (w := (95 / 351)) (n := 12)
    (lo := (555141507 / 1000000000)) (hi := (138785377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223 / 128) = 1/(128 / 223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (555141507 / 1000000000) (138785377 / 250000000) (Real.log (223 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (223 / 128) = -Real.log (128 / 223) := by
    rw [show ((223 / 128) : ℝ) = ((128 / 223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1355522701 / 1000000000) ≤ -Real.log (33 / 128) ∧
    -Real.log (33 / 128) ≤ (1355522703 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 33) = 1/(33 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1355522703 / 1000000000) (-1355522701 / 1000000000) (Real.log (33 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27023403 / 62500000) ≤ -Real.log (62500 / 96307) ∧
    -Real.log (62500 / 96307) ≤ (432374449 / 1000000000) := by
  have h := checkLog_sound (w := (33807 / 158807)) (n := 12)
    (lo := (27023403 / 62500000)) (hi := (432374449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96307 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96307 / 62500) = 1/(62500 / 96307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27023403 / 62500000) (432374449 / 1000000000) (Real.log (96307 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (96307 / 62500) = -Real.log (62500 / 96307) := by
    rw [show ((96307 / 62500) : ℝ) = ((62500 / 96307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155702673 / 200000000) ≤ -Real.log (28693 / 62500) ∧
    -Real.log (28693 / 62500) ≤ (778513367 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 59943)) (n := 12)
    (lo := (17073237 / 200000000)) (hi := (42683093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28693) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 28693) = 1/(28693 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-778513367 / 1000000000) (-155702673 / 200000000) (Real.log (28693 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (108393741 / 250000000) ≤ -Real.log (1000000 / 1542763) ∧
    -Real.log (1000000 / 1542763) ≤ (86714993 / 200000000) := by
  have h := checkLog_sound (w := (542763 / 2542763)) (n := 12)
    (lo := (108393741 / 250000000)) (hi := (86714993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1542763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1542763 / 1000000) = 1/(1000000 / 1542763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (108393741 / 250000000) (86714993 / 200000000) (Real.log (1542763 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1542763 / 1000000) = -Real.log (1000000 / 1542763) := by
    rw [show ((1542763 / 1000000) : ℝ) = ((1000000 / 1542763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (391276711 / 500000000) ≤ -Real.log (457237 / 1000000) ∧
    -Real.log (457237 / 1000000) ≤ (48909589 / 62500000) := by
  have h := checkLog_sound (w := (42763 / 957237)) (n := 12)
    (lo := (44703121 / 500000000)) (hi := (89406243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 457237) = 1/(457237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48909589 / 62500000) (-391276711 / 500000000) (Real.log (457237 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86960411 / 250000000) ≤ -Real.log (125000 / 177001) ∧
    -Real.log (125000 / 177001) ≤ (69568329 / 200000000) := by
  have h := checkLog_sound (w := (52001 / 302001)) (n := 12)
    (lo := (86960411 / 250000000)) (hi := (69568329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177001 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177001 / 125000) = 1/(125000 / 177001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86960411 / 250000000) (69568329 / 200000000) (Real.log (177001 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (177001 / 125000) = -Real.log (125000 / 177001) := by
    rw [show ((177001 / 125000) : ℝ) = ((125000 / 177001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268933997 / 500000000) ≤ -Real.log (72999 / 125000) ∧
    -Real.log (72999 / 125000) ≤ (107573599 / 200000000) := by
  have h := checkLog_sound (w := (52001 / 197999)) (n := 12)
    (lo := (268933997 / 500000000)) (hi := (107573599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72999) = 1/(72999 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-107573599 / 200000000) (-268933997 / 500000000) (Real.log (72999 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (174511219 / 500000000) ≤ -Real.log (1000000 / 1417681) ∧
    -Real.log (1000000 / 1417681) ≤ (349022439 / 1000000000) := by
  have h := checkLog_sound (w := (417681 / 2417681)) (n := 12)
    (lo := (174511219 / 500000000)) (hi := (349022439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417681 / 1000000) = 1/(1000000 / 1417681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (174511219 / 500000000) (349022439 / 1000000000) (Real.log (1417681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1417681 / 1000000) = -Real.log (1000000 / 1417681) := by
    rw [show ((1417681 / 1000000) : ℝ) = ((1000000 / 1417681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (540736871 / 1000000000) ≤ -Real.log (582319 / 1000000) ∧
    -Real.log (582319 / 1000000) ≤ (67592109 / 125000000) := by
  have h := checkLog_sound (w := (417681 / 1582319)) (n := 12)
    (lo := (540736871 / 1000000000)) (hi := (67592109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 582319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 582319) = 1/(582319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-67592109 / 125000000) (-540736871 / 1000000000) (Real.log (582319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (605443907 / 500000000) ≤ -Real.log (250000000000 / 839115812219) ∧
    -Real.log (250000000000 / 839115812219) ≤ (151360977 / 125000000) := by
  have h := checkLog_sound (w := (339115812219 / 1339115812219)) (n := 12)
    (lo := (258870317 / 500000000)) (hi := (103548127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839115812219 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(839115812219 / 500000000000) = 1/(250000000000 / 839115812219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (605443907 / 500000000) (151360977 / 125000000) (Real.log (839115812219 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (839115812219 / 250000000000) = -Real.log (250000000000 / 839115812219) := by
    rw [show ((839115812219 / 250000000000) : ℝ) = ((250000000000 / 839115812219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1216128387 / 1000000000) ≤ -Real.log (500000000000 / 1687049604473) ∧
    -Real.log (500000000000 / 1687049604473) ≤ (1216128389 / 1000000000) := by
  have h := checkLog_sound (w := (687049604473 / 2687049604473)) (n := 12)
    (lo := (522981207 / 1000000000)) (hi := (65372651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687049604473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1687049604473 / 1000000000000) = 1/(500000000000 / 1687049604473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1216128387 / 1000000000) (1216128389 / 1000000000) (Real.log (1687049604473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1687049604473 / 500000000000) = -Real.log (500000000000 / 1687049604473) := by
    rw [show ((1687049604473 / 500000000000) : ℝ) = ((500000000000 / 1687049604473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (885709639 / 1000000000) ≤ -Real.log (500000000000 / 1212352224003) ∧
    -Real.log (500000000000 / 1212352224003) ≤ (885709641 / 1000000000) := by
  have h := checkLog_sound (w := (212352224003 / 2212352224003)) (n := 12)
    (lo := (192562459 / 1000000000)) (hi := (9628123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212352224003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212352224003 / 1000000000000) = 1/(500000000000 / 1212352224003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (885709639 / 1000000000) (885709641 / 1000000000) (Real.log (1212352224003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1212352224003 / 500000000000) = -Real.log (500000000000 / 1212352224003) := by
    rw [show ((1212352224003 / 500000000000) : ℝ) = ((500000000000 / 1212352224003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222439827 / 250000000) ≤ -Real.log (50000000000 / 121727180463) ∧
    -Real.log (50000000000 / 121727180463) ≤ (88975931 / 100000000) := by
  have h := checkLog_sound (w := (21727180463 / 221727180463)) (n := 12)
    (lo := (6144129 / 31250000)) (hi := (196612129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121727180463 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121727180463 / 100000000000) = 1/(50000000000 / 121727180463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222439827 / 250000000) (88975931 / 100000000) (Real.log (121727180463 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (121727180463 / 50000000000) = -Real.log (50000000000 / 121727180463) := by
    rw [show ((121727180463 / 50000000000) : ℝ) = ((50000000000 / 121727180463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0120
