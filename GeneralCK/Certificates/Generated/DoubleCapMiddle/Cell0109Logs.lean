import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0109
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

theorem reflection_log_1_neg : (325812949 / 1000000000) ≤ -Real.log (1280 / 1773) ∧
    -Real.log (1280 / 1773) ≤ (6516259 / 20000000) := by
  have h := checkLog_sound (w := (493 / 3053)) (n := 12)
    (lo := (325812949 / 1000000000)) (hi := (6516259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1280) = 1/(1280 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325812949 / 1000000000) (6516259 / 20000000) (Real.log (1773 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1773 / 1280) = -Real.log (1280 / 1773) := by
    rw [show ((1773 / 1280) : ℝ) = ((1280 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121596777 / 250000000) ≤ -Real.log (787 / 1280) ∧
    -Real.log (787 / 1280) ≤ (486387109 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2067)) (n := 12)
    (lo := (121596777 / 250000000)) (hi := (486387109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 787) = 1/(787 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-486387109 / 1000000000) (-121596777 / 250000000) (Real.log (787 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324966567 / 1000000000) ≤ -Real.log (2560 / 3543) ∧
    -Real.log (2560 / 3543) ≤ (40620821 / 125000000) := by
  have h := checkLog_sound (w := (983 / 6103)) (n := 12)
    (lo := (324966567 / 1000000000)) (hi := (40620821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3543 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3543 / 2560) = 1/(2560 / 3543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324966567 / 1000000000) (40620821 / 125000000) (Real.log (3543 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3543 / 2560) = -Real.log (2560 / 3543) := by
    rw [show ((3543 / 2560) : ℝ) = ((2560 / 3543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (9689659 / 20000000) ≤ -Real.log (1577 / 2560) ∧
    -Real.log (1577 / 2560) ≤ (484482951 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 4137)) (n := 12)
    (lo := (9689659 / 20000000)) (hi := (484482951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1577) = 1/(1577 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-484482951 / 1000000000) (-9689659 / 20000000) (Real.log (1577 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (142789021 / 250000000) ≤ -Real.log (640 / 1133) ∧
    -Real.log (640 / 1133) ≤ (114231217 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1773)) (n := 12)
    (lo := (142789021 / 250000000)) (hi := (114231217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133 / 640) = 1/(640 / 1133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (142789021 / 250000000) (114231217 / 200000000) (Real.log (1133 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1133 / 640) = -Real.log (640 / 1133) := by
    rw [show ((1133 / 640) : ℝ) = ((640 / 1133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (367758897 / 250000000) ≤ -Real.log (147 / 640) ∧
    -Real.log (147 / 640) ≤ (1471035591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 147) = 1/(147 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1471035591 / 1000000000) (-367758897 / 250000000) (Real.log (147 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71228911 / 125000000) ≤ -Real.log (1280 / 2263) ∧
    -Real.log (1280 / 2263) ≤ (569831289 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 3543)) (n := 12)
    (lo := (71228911 / 125000000)) (hi := (569831289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2263 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2263 / 1280) = 1/(1280 / 2263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71228911 / 125000000) (569831289 / 1000000000) (Real.log (2263 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2263 / 1280) = -Real.log (1280 / 2263) := by
    rw [show ((2263 / 1280) : ℝ) = ((1280 / 2263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (91305201 / 62500000) ≤ -Real.log (297 / 1280) ∧
    -Real.log (297 / 1280) ≤ (1460883219 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 297) = 1/(297 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1460883219 / 1000000000) (-91305201 / 62500000) (Real.log (297 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1740523 / 3906250) ≤ -Real.log (500000 / 780693) ∧
    -Real.log (500000 / 780693) ≤ (445573889 / 1000000000) := by
  have h := checkLog_sound (w := (280693 / 1280693)) (n := 12)
    (lo := (1740523 / 3906250)) (hi := (445573889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780693 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780693 / 500000) = 1/(500000 / 780693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1740523 / 3906250) (445573889 / 1000000000) (Real.log (780693 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (780693 / 500000) = -Real.log (500000 / 780693) := by
    rw [show ((780693 / 500000) : ℝ) = ((500000 / 780693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (824135523 / 1000000000) ≤ -Real.log (219307 / 500000) ∧
    -Real.log (219307 / 500000) ≤ (32965421 / 40000000) := by
  have h := checkLog_sound (w := (30693 / 469307)) (n := 12)
    (lo := (130988343 / 1000000000)) (hi := (16373543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 219307) = 1/(219307 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32965421 / 40000000) (-824135523 / 1000000000) (Real.log (219307 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (446775303 / 1000000000) ≤ -Real.log (1000000 / 1563263) ∧
    -Real.log (1000000 / 1563263) ≤ (55846913 / 125000000) := by
  have h := checkLog_sound (w := (563263 / 2563263)) (n := 12)
    (lo := (446775303 / 1000000000)) (hi := (55846913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563263 / 1000000) = 1/(1000000 / 1563263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (446775303 / 1000000000) (55846913 / 125000000) (Real.log (1563263 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1563263 / 1000000) = -Real.log (1000000 / 1563263) := by
    rw [show ((1563263 / 1000000) : ℝ) = ((1000000 / 1563263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (165684819 / 200000000) ≤ -Real.log (436737 / 1000000) ∧
    -Real.log (436737 / 1000000) ≤ (828424097 / 1000000000) := by
  have h := checkLog_sound (w := (63263 / 936737)) (n := 12)
    (lo := (27055383 / 200000000)) (hi := (33819229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436737) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 436737) = 1/(436737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-828424097 / 1000000000) (-165684819 / 200000000) (Real.log (436737 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (180464989 / 500000000) ≤ -Real.log (1000000 / 1434663) ∧
    -Real.log (1000000 / 1434663) ≤ (360929979 / 1000000000) := by
  have h := checkLog_sound (w := (434663 / 2434663)) (n := 12)
    (lo := (180464989 / 500000000)) (hi := (360929979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1434663 / 1000000) = 1/(1000000 / 1434663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (180464989 / 500000000) (360929979 / 1000000000) (Real.log (1434663 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1434663 / 1000000) = -Real.log (1000000 / 1434663) := by
    rw [show ((1434663 / 1000000) : ℝ) = ((1000000 / 1434663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114066653 / 200000000) ≤ -Real.log (565337 / 1000000) ∧
    -Real.log (565337 / 1000000) ≤ (285166633 / 500000000) := by
  have h := checkLog_sound (w := (434663 / 1565337)) (n := 12)
    (lo := (114066653 / 200000000)) (hi := (285166633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 565337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 565337) = 1/(565337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285166633 / 500000000) (-114066653 / 200000000) (Real.log (565337 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (362133717 / 1000000000) ≤ -Real.log (1000000 / 1436391) ∧
    -Real.log (1000000 / 1436391) ≤ (181066859 / 500000000) := by
  have h := checkLog_sound (w := (436391 / 2436391)) (n := 12)
    (lo := (362133717 / 1000000000)) (hi := (181066859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1436391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1436391 / 1000000) = 1/(1000000 / 1436391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (362133717 / 1000000000) (181066859 / 500000000) (Real.log (1436391 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1436391 / 1000000) = -Real.log (1000000 / 1436391) := by
    rw [show ((1436391 / 1000000) : ℝ) = ((1000000 / 1436391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57339453 / 100000000) ≤ -Real.log (563609 / 1000000) ∧
    -Real.log (563609 / 1000000) ≤ (573394531 / 1000000000) := by
  have h := checkLog_sound (w := (436391 / 1563609)) (n := 12)
    (lo := (57339453 / 100000000)) (hi := (573394531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 563609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 563609) = 1/(563609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-573394531 / 1000000000) (-57339453 / 100000000) (Real.log (563609 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1269709411 / 1000000000) ≤ -Real.log (500000000000 / 1779908986033) ∧
    -Real.log (500000000000 / 1779908986033) ≤ (1269709413 / 1000000000) := by
  have h := checkLog_sound (w := (779908986033 / 2779908986033)) (n := 12)
    (lo := (576562231 / 1000000000)) (hi := (72070279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779908986033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1779908986033 / 1000000000000) = 1/(500000000000 / 1779908986033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1269709411 / 1000000000) (1269709413 / 1000000000) (Real.log (1779908986033 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1779908986033 / 500000000000) = -Real.log (500000000000 / 1779908986033) := by
    rw [show ((1779908986033 / 500000000000) : ℝ) = ((500000000000 / 1779908986033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (637599699 / 500000000) ≤ -Real.log (500000000000 / 1789707535657) ∧
    -Real.log (500000000000 / 1789707535657) ≤ (6375997 / 5000000) := by
  have h := checkLog_sound (w := (789707535657 / 2789707535657)) (n := 12)
    (lo := (291026109 / 500000000)) (hi := (582052219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789707535657 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1789707535657 / 1000000000000) = 1/(500000000000 / 1789707535657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (637599699 / 500000000) (6375997 / 5000000) (Real.log (1789707535657 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1789707535657 / 500000000000) = -Real.log (500000000000 / 1789707535657) := by
    rw [show ((1789707535657 / 500000000000) : ℝ) = ((500000000000 / 1789707535657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (931263243 / 1000000000) ≤ -Real.log (62500000000 / 158607056499) ∧
    -Real.log (62500000000 / 158607056499) ≤ (186252649 / 200000000) := by
  have h := checkLog_sound (w := (33607056499 / 283607056499)) (n := 12)
    (lo := (238116063 / 1000000000)) (hi := (7441127 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158607056499 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158607056499 / 125000000000) = 1/(62500000000 / 158607056499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (931263243 / 1000000000) (186252649 / 200000000) (Real.log (158607056499 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (158607056499 / 62500000000) = -Real.log (62500000000 / 158607056499) := by
    rw [show ((158607056499 / 62500000000) : ℝ) = ((62500000000 / 158607056499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (935528247 / 1000000000) ≤ -Real.log (100000000000 / 254855937361) ∧
    -Real.log (100000000000 / 254855937361) ≤ (935528249 / 1000000000) := by
  have h := checkLog_sound (w := (54855937361 / 454855937361)) (n := 12)
    (lo := (242381067 / 1000000000)) (hi := (60595267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254855937361 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(254855937361 / 200000000000) = 1/(100000000000 / 254855937361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (935528247 / 1000000000) (935528249 / 1000000000) (Real.log (254855937361 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (254855937361 / 100000000000) = -Real.log (100000000000 / 254855937361) := by
    rw [show ((254855937361 / 100000000000) : ℝ) = ((100000000000 / 254855937361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0109
