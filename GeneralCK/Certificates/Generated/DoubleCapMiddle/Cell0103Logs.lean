import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0103
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

theorem reflection_log_1_neg : (330876251 / 1000000000) ≤ -Real.log (640 / 891) ∧
    -Real.log (640 / 891) ≤ (82719063 / 250000000) := by
  have h := checkLog_sound (w := (251 / 1531)) (n := 12)
    (lo := (330876251 / 1000000000)) (hi := (82719063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 640) = 1/(640 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (330876251 / 1000000000) (82719063 / 250000000) (Real.log (891 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (891 / 640) = -Real.log (640 / 891) := by
    rw [show ((891 / 640) : ℝ) = ((640 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7779513 / 15625000) ≤ -Real.log (389 / 640) ∧
    -Real.log (389 / 640) ≤ (497888833 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1029)) (n := 12)
    (lo := (7779513 / 15625000)) (hi := (497888833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 389) = 1/(389 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-497888833 / 1000000000) (-7779513 / 15625000) (Real.log (389 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66006829 / 200000000) ≤ -Real.log (2560 / 3561) ∧
    -Real.log (2560 / 3561) ≤ (165017073 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 6121)) (n := 12)
    (lo := (66006829 / 200000000)) (hi := (165017073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 2560) = 1/(2560 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66006829 / 200000000) (165017073 / 500000000) (Real.log (3561 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3561 / 2560) = -Real.log (2560 / 3561) := by
    rw [show ((3561 / 2560) : ℝ) = ((2560 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (123990667 / 250000000) ≤ -Real.log (1559 / 2560) ∧
    -Real.log (1559 / 2560) ≤ (495962669 / 1000000000) := by
  have h := checkLog_sound (w := (1001 / 4119)) (n := 12)
    (lo := (123990667 / 250000000)) (hi := (495962669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1559) = 1/(1559 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-495962669 / 1000000000) (-123990667 / 250000000) (Real.log (1559 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (579068213 / 1000000000) ≤ -Real.log (320 / 571) ∧
    -Real.log (320 / 571) ≤ (289534107 / 500000000) := by
  have h := checkLog_sound (w := (251 / 891)) (n := 12)
    (lo := (579068213 / 1000000000)) (hi := (289534107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571 / 320) = 1/(320 / 571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (579068213 / 1000000000) (289534107 / 500000000) (Real.log (571 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (571 / 320) = -Real.log (320 / 571) := by
    rw [show ((571 / 320) : ℝ) = ((320 / 571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153421449 / 100000000) ≤ -Real.log (69 / 320) ∧
    -Real.log (69 / 320) ≤ (1534214493 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 69) = 1/(69 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1534214493 / 1000000000) (-153421449 / 100000000) (Real.log (69 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (115550773 / 200000000) ≤ -Real.log (1280 / 2281) ∧
    -Real.log (1280 / 2281) ≤ (288876933 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 3561)) (n := 12)
    (lo := (115550773 / 200000000)) (hi := (288876933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1280) = 1/(1280 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (115550773 / 200000000) (288876933 / 500000000) (Real.log (2281 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2281 / 1280) = -Real.log (1280 / 2281) := by
    rw [show ((2281 / 1280) : ℝ) = ((1280 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1523403573 / 1000000000) ≤ -Real.log (279 / 1280) ∧
    -Real.log (279 / 1280) ≤ (190425447 / 125000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 279) = 1/(279 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190425447 / 125000000) (-1523403573 / 1000000000) (Real.log (279 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (226389949 / 500000000) ≤ -Real.log (500000 / 786339) ∧
    -Real.log (500000 / 786339) ≤ (452779899 / 1000000000) := by
  have h := checkLog_sound (w := (286339 / 1286339)) (n := 12)
    (lo := (226389949 / 500000000)) (hi := (452779899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786339 / 500000) = 1/(500000 / 786339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (226389949 / 500000000) (452779899 / 1000000000) (Real.log (786339 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (786339 / 500000) = -Real.log (500000 / 786339) := by
    rw [show ((786339 / 500000) : ℝ) = ((500000 / 786339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (850217451 / 1000000000) ≤ -Real.log (213661 / 500000) ∧
    -Real.log (213661 / 500000) ≤ (850217453 / 1000000000) := by
  have h := checkLog_sound (w := (36339 / 463661)) (n := 12)
    (lo := (157070271 / 1000000000)) (hi := (2454223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 213661) = 1/(213661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-850217453 / 1000000000) (-850217451 / 1000000000) (Real.log (213661 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (453982219 / 1000000000) ≤ -Real.log (100000 / 157457) ∧
    -Real.log (100000 / 157457) ≤ (22699111 / 50000000) := by
  have h := checkLog_sound (w := (57457 / 257457)) (n := 12)
    (lo := (453982219 / 1000000000)) (hi := (22699111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157457 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157457 / 100000) = 1/(100000 / 157457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (453982219 / 1000000000) (22699111 / 50000000) (Real.log (157457 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (157457 / 100000) = -Real.log (100000 / 157457) := by
    rw [show ((157457 / 100000) : ℝ) = ((100000 / 157457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106831857 / 125000000) ≤ -Real.log (42543 / 100000) ∧
    -Real.log (42543 / 100000) ≤ (427327429 / 500000000) := by
  have h := checkLog_sound (w := (7457 / 92543)) (n := 12)
    (lo := (40376919 / 250000000)) (hi := (161507677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42543) = 1/(42543 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-427327429 / 500000000) (-106831857 / 125000000) (Real.log (42543 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (368181291 / 1000000000) ≤ -Real.log (62500 / 90319) ∧
    -Real.log (62500 / 90319) ≤ (92045323 / 250000000) := by
  have h := checkLog_sound (w := (27819 / 152819)) (n := 12)
    (lo := (368181291 / 1000000000)) (hi := (92045323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90319 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90319 / 62500) = 1/(62500 / 90319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (368181291 / 1000000000) (92045323 / 250000000) (Real.log (90319 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90319 / 62500) = -Real.log (62500 / 90319) := by
    rw [show ((90319 / 62500) : ℝ) = ((62500 / 90319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58897457 / 100000000) ≤ -Real.log (34681 / 62500) ∧
    -Real.log (34681 / 62500) ≤ (588974571 / 1000000000) := by
  have h := checkLog_sound (w := (27819 / 97181)) (n := 12)
    (lo := (58897457 / 100000000)) (hi := (588974571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34681) = 1/(34681 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-588974571 / 1000000000) (-58897457 / 100000000) (Real.log (34681 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73879691 / 200000000) ≤ -Real.log (62500 / 90429) ∧
    -Real.log (62500 / 90429) ≤ (46174807 / 125000000) := by
  have h := checkLog_sound (w := (27929 / 152929)) (n := 12)
    (lo := (73879691 / 200000000)) (hi := (46174807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90429 / 62500) = 1/(62500 / 90429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73879691 / 200000000) (46174807 / 125000000) (Real.log (90429 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90429 / 62500) = -Real.log (62500 / 90429) := by
    rw [show ((90429 / 62500) : ℝ) = ((62500 / 90429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37009461 / 62500000) ≤ -Real.log (34571 / 62500) ∧
    -Real.log (34571 / 62500) ≤ (592151377 / 1000000000) := by
  have h := checkLog_sound (w := (27929 / 97071)) (n := 12)
    (lo := (37009461 / 62500000)) (hi := (592151377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34571) = 1/(34571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-592151377 / 1000000000) (-37009461 / 62500000) (Real.log (34571 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1302997349 / 1000000000) ≤ -Real.log (250000000000 / 920077833577) ∧
    -Real.log (250000000000 / 920077833577) ≤ (1302997351 / 1000000000) := by
  have h := checkLog_sound (w := (420077833577 / 1420077833577)) (n := 12)
    (lo := (609850169 / 1000000000)) (hi := (60985017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920077833577 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(920077833577 / 500000000000) = 1/(250000000000 / 920077833577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1302997349 / 1000000000) (1302997351 / 1000000000) (Real.log (920077833577 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (920077833577 / 250000000000) = -Real.log (250000000000 / 920077833577) := by
    rw [show ((920077833577 / 250000000000) : ℝ) = ((250000000000 / 920077833577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52345483 / 40000000) ≤ -Real.log (500000000000 / 1850562959829) ∧
    -Real.log (500000000000 / 1850562959829) ≤ (1308637077 / 1000000000) := by
  have h := checkLog_sound (w := (850562959829 / 2850562959829)) (n := 12)
    (lo := (123097979 / 200000000)) (hi := (76936237 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1850562959829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1850562959829 / 1000000000000) = 1/(500000000000 / 1850562959829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52345483 / 40000000) (1308637077 / 1000000000) (Real.log (1850562959829 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1850562959829 / 500000000000) = -Real.log (500000000000 / 1850562959829) := by
    rw [show ((1850562959829 / 500000000000) : ℝ) = ((500000000000 / 1850562959829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (47857793 / 50000000) ≤ -Real.log (250000000000 / 651069750007) ∧
    -Real.log (250000000000 / 651069750007) ≤ (478577931 / 500000000) := by
  have h := checkLog_sound (w := (151069750007 / 1151069750007)) (n := 12)
    (lo := (6600217 / 25000000)) (hi := (264008681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651069750007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(651069750007 / 500000000000) = 1/(250000000000 / 651069750007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (47857793 / 50000000) (478577931 / 500000000) (Real.log (651069750007 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (651069750007 / 250000000000) = -Real.log (250000000000 / 651069750007) := by
    rw [show ((651069750007 / 250000000000) : ℝ) = ((250000000000 / 651069750007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (961549831 / 1000000000) ≤ -Real.log (500000000000 / 1307873651327) ∧
    -Real.log (500000000000 / 1307873651327) ≤ (961549833 / 1000000000) := by
  have h := checkLog_sound (w := (307873651327 / 2307873651327)) (n := 12)
    (lo := (268402651 / 1000000000)) (hi := (67100663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307873651327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1307873651327 / 1000000000000) = 1/(500000000000 / 1307873651327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (961549831 / 1000000000) (961549833 / 1000000000) (Real.log (1307873651327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1307873651327 / 500000000000) = -Real.log (500000000000 / 1307873651327) := by
    rw [show ((1307873651327 / 500000000000) : ℝ) = ((500000000000 / 1307873651327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0103
