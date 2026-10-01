import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0110
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

theorem reflection_log_1_neg : (324966567 / 1000000000) ≤ -Real.log (2560 / 3543) ∧
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


theorem reflection_log_1 : Bounds (324966567 / 1000000000) (40620821 / 125000000) (Real.log (3543 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3543 / 2560) = -Real.log (2560 / 3543) := by
    rw [show ((3543 / 2560) : ℝ) = ((2560 / 3543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9689659 / 20000000) ≤ -Real.log (1577 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-484482951 / 1000000000) (-9689659 / 20000000) (Real.log (1577 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (81029867 / 250000000) ≤ -Real.log (128 / 177) ∧
    -Real.log (128 / 177) ≤ (324119469 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 305)) (n := 12)
    (lo := (81029867 / 250000000)) (hi := (324119469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 128) = 1/(128 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (81029867 / 250000000) (324119469 / 1000000000) (Real.log (177 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (177 / 128) = -Real.log (128 / 177) := by
    rw [show ((177 / 128) : ℝ) = ((128 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (482582411 / 1000000000) ≤ -Real.log (79 / 128) ∧
    -Real.log (79 / 128) ≤ (120645603 / 250000000) := by
  have h := checkLog_sound (w := (49 / 207)) (n := 12)
    (lo := (482582411 / 1000000000)) (hi := (120645603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 79) = 1/(79 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-120645603 / 250000000) (-482582411 / 1000000000) (Real.log (79 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71228911 / 125000000) ≤ -Real.log (1280 / 2263) ∧
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


theorem reflection_log_5 : Bounds (71228911 / 125000000) (569831289 / 1000000000) (Real.log (2263 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2263 / 1280) = -Real.log (1280 / 2263) := by
    rw [show ((2263 / 1280) : ℝ) = ((1280 / 2263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (91305201 / 62500000) ≤ -Real.log (297 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-1460883219 / 1000000000) (-91305201 / 62500000) (Real.log (297 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113700947 / 200000000) ≤ -Real.log (64 / 113) ∧
    -Real.log (64 / 113) ≤ (17765773 / 31250000) := by
  have h := checkLog_sound (w := (49 / 177)) (n := 12)
    (lo := (113700947 / 200000000)) (hi := (17765773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113 / 64) = 1/(64 / 113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113700947 / 200000000) (17765773 / 31250000) (Real.log (113 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (113 / 64) = -Real.log (64 / 113) := by
    rw [show ((113 / 64) : ℝ) = ((64 / 113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-362708221 / 250000000) (-1450832881 / 1000000000) (Real.log (15 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (444373593 / 1000000000) ≤ -Real.log (1000000 / 1559513) ∧
    -Real.log (1000000 / 1559513) ≤ (222186797 / 500000000) := by
  have h := checkLog_sound (w := (559513 / 2559513)) (n := 12)
    (lo := (444373593 / 1000000000)) (hi := (222186797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1559513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1559513 / 1000000) = 1/(1000000 / 1559513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (444373593 / 1000000000) (222186797 / 500000000) (Real.log (1559513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1559513 / 1000000) = -Real.log (1000000 / 1559513) := by
    rw [show ((1559513 / 1000000) : ℝ) = ((1000000 / 1559513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (163974869 / 200000000) ≤ -Real.log (440487 / 1000000) ∧
    -Real.log (440487 / 1000000) ≤ (819874347 / 1000000000) := by
  have h := checkLog_sound (w := (59513 / 940487)) (n := 12)
    (lo := (25345433 / 200000000)) (hi := (63363583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440487) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 440487) = 1/(440487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-819874347 / 1000000000) (-163974869 / 200000000) (Real.log (440487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3481051 / 7812500) ≤ -Real.log (1000000 / 1561387) ∧
    -Real.log (1000000 / 1561387) ≤ (445574529 / 1000000000) := by
  have h := checkLog_sound (w := (561387 / 2561387)) (n := 12)
    (lo := (3481051 / 7812500)) (hi := (445574529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1561387 / 1000000) = 1/(1000000 / 1561387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3481051 / 7812500) (445574529 / 1000000000) (Real.log (1561387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1561387 / 1000000) = -Real.log (1000000 / 1561387) := by
    rw [show ((1561387 / 1000000) : ℝ) = ((1000000 / 1561387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (824137803 / 1000000000) ≤ -Real.log (438613 / 1000000) ∧
    -Real.log (438613 / 1000000) ≤ (164827561 / 200000000) := by
  have h := checkLog_sound (w := (61387 / 938613)) (n := 12)
    (lo := (130990623 / 1000000000)) (hi := (4093457 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438613) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 438613) = 1/(438613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-164827561 / 200000000) (-824137803 / 1000000000) (Real.log (438613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (359729673 / 1000000000) ≤ -Real.log (500000 / 716471) ∧
    -Real.log (500000 / 716471) ≤ (179864837 / 500000000) := by
  have h := checkLog_sound (w := (216471 / 1216471)) (n := 12)
    (lo := (359729673 / 1000000000)) (hi := (179864837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716471 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716471 / 500000) = 1/(500000 / 716471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (359729673 / 1000000000) (179864837 / 500000000) (Real.log (716471 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (716471 / 500000) = -Real.log (500000 / 716471) := by
    rw [show ((716471 / 500000) : ℝ) = ((500000 / 716471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (567293687 / 1000000000) ≤ -Real.log (283529 / 500000) ∧
    -Real.log (283529 / 500000) ≤ (70911711 / 125000000) := by
  have h := checkLog_sound (w := (216471 / 783529)) (n := 12)
    (lo := (567293687 / 1000000000)) (hi := (70911711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 283529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 283529) = 1/(283529 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-70911711 / 125000000) (-567293687 / 1000000000) (Real.log (283529 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14437227 / 40000000) ≤ -Real.log (125000 / 179333) ∧
    -Real.log (125000 / 179333) ≤ (90232669 / 250000000) := by
  have h := checkLog_sound (w := (54333 / 304333)) (n := 12)
    (lo := (14437227 / 40000000)) (hi := (90232669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179333 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179333 / 125000) = 1/(125000 / 179333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14437227 / 40000000) (90232669 / 250000000) (Real.log (179333 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (179333 / 125000) = -Real.log (125000 / 179333) := by
    rw [show ((179333 / 125000) : ℝ) = ((125000 / 179333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (285167517 / 500000000) ≤ -Real.log (70667 / 125000) ∧
    -Real.log (70667 / 125000) ≤ (114067007 / 200000000) := by
  have h := checkLog_sound (w := (54333 / 195667)) (n := 12)
    (lo := (285167517 / 500000000)) (hi := (114067007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 70667) = 1/(70667 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-114067007 / 200000000) (-285167517 / 500000000) (Real.log (70667 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (632123969 / 500000000) ≤ -Real.log (500000000000 / 1770214557977) ∧
    -Real.log (500000000000 / 1770214557977) ≤ (63212397 / 50000000) := by
  have h := checkLog_sound (w := (770214557977 / 2770214557977)) (n := 12)
    (lo := (285550379 / 500000000)) (hi := (571100759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1770214557977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1770214557977 / 1000000000000) = 1/(500000000000 / 1770214557977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (632123969 / 500000000) (63212397 / 50000000) (Real.log (1770214557977 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1770214557977 / 500000000000) = -Real.log (500000000000 / 1770214557977) := by
    rw [show ((1770214557977 / 500000000000) : ℝ) = ((500000000000 / 1770214557977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1269712331 / 1000000000) ≤ -Real.log (500000000000 / 1779914184031) ∧
    -Real.log (500000000000 / 1779914184031) ≤ (1269712333 / 1000000000) := by
  have h := checkLog_sound (w := (779914184031 / 2779914184031)) (n := 12)
    (lo := (576565151 / 1000000000)) (hi := (18017661 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779914184031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1779914184031 / 1000000000000) = 1/(500000000000 / 1779914184031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1269712331 / 1000000000) (1269712333 / 1000000000) (Real.log (1779914184031 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1779914184031 / 500000000000) = -Real.log (500000000000 / 1779914184031) := by
    rw [show ((1779914184031 / 500000000000) : ℝ) = ((500000000000 / 1779914184031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (724237 / 781250) ≤ -Real.log (25000000000 / 63174401913) ∧
    -Real.log (25000000000 / 63174401913) ≤ (463511681 / 500000000) := by
  have h := checkLog_sound (w := (13174401913 / 113174401913)) (n := 12)
    (lo := (11693809 / 50000000)) (hi := (233876181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63174401913 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63174401913 / 50000000000) = 1/(25000000000 / 63174401913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (724237 / 781250) (463511681 / 500000000) (Real.log (63174401913 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (63174401913 / 25000000000) = -Real.log (25000000000 / 63174401913) := by
    rw [show ((63174401913 / 25000000000) : ℝ) = ((25000000000 / 63174401913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (931265709 / 1000000000) ≤ -Real.log (125000000000 / 317214895213) ∧
    -Real.log (125000000000 / 317214895213) ≤ (931265711 / 1000000000) := by
  have h := checkLog_sound (w := (67214895213 / 567214895213)) (n := 12)
    (lo := (238118529 / 1000000000)) (hi := (23811853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317214895213 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(317214895213 / 250000000000) = 1/(125000000000 / 317214895213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (931265709 / 1000000000) (931265711 / 1000000000) (Real.log (317214895213 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (317214895213 / 125000000000) = -Real.log (125000000000 / 317214895213) := by
    rw [show ((317214895213 / 125000000000) : ℝ) = ((125000000000 / 317214895213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0110
