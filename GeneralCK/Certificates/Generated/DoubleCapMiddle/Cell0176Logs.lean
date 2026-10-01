import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0176
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

theorem reflection_log_1_neg : (55277613 / 200000000) ≤ -Real.log (512 / 675) ∧
    -Real.log (512 / 675) ≤ (138194033 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1187)) (n := 12)
    (lo := (55277613 / 200000000)) (hi := (138194033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675 / 512) = 1/(512 / 675) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55277613 / 200000000) (138194033 / 500000000) (Real.log (675 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (675 / 512) = -Real.log (512 / 675) := by
    rw [show ((675 / 512) : ℝ) = ((512 / 675) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (191626351 / 500000000) ≤ -Real.log (349 / 512) ∧
    -Real.log (349 / 512) ≤ (383252703 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 861)) (n := 12)
    (lo := (191626351 / 500000000)) (hi := (383252703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 349) = 1/(349 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-383252703 / 1000000000) (-191626351 / 500000000) (Real.log (349 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137971761 / 500000000) ≤ -Real.log (5120 / 6747) ∧
    -Real.log (5120 / 6747) ≤ (275943523 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 11867)) (n := 12)
    (lo := (137971761 / 500000000)) (hi := (275943523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6747 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6747 / 5120) = 1/(5120 / 6747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137971761 / 500000000) (275943523 / 1000000000) (Real.log (6747 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6747 / 5120) = -Real.log (5120 / 6747) := by
    rw [show ((6747 / 5120) : ℝ) = ((5120 / 6747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (382393473 / 1000000000) ≤ -Real.log (3493 / 5120) ∧
    -Real.log (3493 / 5120) ≤ (191196737 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 8613)) (n := 12)
    (lo := (382393473 / 1000000000)) (hi := (191196737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3493) = 1/(3493 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-191196737 / 500000000) (-382393473 / 1000000000) (Real.log (3493 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19707739 / 40000000) ≤ -Real.log (256 / 419) ∧
    -Real.log (256 / 419) ≤ (123173369 / 250000000) := by
  have h := checkLog_sound (w := (163 / 675)) (n := 12)
    (lo := (19707739 / 40000000)) (hi := (123173369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419 / 256) = 1/(256 / 419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19707739 / 40000000) (123173369 / 250000000) (Real.log (419 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (419 / 256) = -Real.log (256 / 419) := by
    rw [show ((419 / 256) : ℝ) = ((256 / 419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (20251559 / 20000000) ≤ -Real.log (93 / 256) ∧
    -Real.log (93 / 256) ≤ (31643061 / 31250000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 93) = 1/(93 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31643061 / 31250000) (-20251559 / 20000000) (Real.log (93 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122994307 / 250000000) ≤ -Real.log (2560 / 4187) ∧
    -Real.log (2560 / 4187) ≤ (491977229 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 6747)) (n := 12)
    (lo := (122994307 / 250000000)) (hi := (491977229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4187 / 2560) = 1/(2560 / 4187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122994307 / 250000000) (491977229 / 1000000000) (Real.log (4187 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4187 / 2560) = -Real.log (2560 / 4187) := by
    rw [show ((4187 / 2560) : ℝ) = ((2560 / 4187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126169667 / 125000000) ≤ -Real.log (933 / 2560) ∧
    -Real.log (933 / 2560) ≤ (504678669 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 933) = 1/(933 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-504678669 / 500000000) (-126169667 / 125000000) (Real.log (933 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37748187 / 100000000) ≤ -Real.log (1000000 / 1458607) ∧
    -Real.log (1000000 / 1458607) ≤ (377481871 / 1000000000) := by
  have h := checkLog_sound (w := (458607 / 2458607)) (n := 12)
    (lo := (37748187 / 100000000)) (hi := (377481871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1458607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1458607 / 1000000) = 1/(1000000 / 1458607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37748187 / 100000000) (377481871 / 1000000000) (Real.log (1458607 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1458607 / 1000000) = -Real.log (1000000 / 1458607) := by
    rw [show ((1458607 / 1000000) : ℝ) = ((1000000 / 1458607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (613609831 / 1000000000) ≤ -Real.log (541393 / 1000000) ∧
    -Real.log (541393 / 1000000) ≤ (76701229 / 125000000) := by
  have h := checkLog_sound (w := (458607 / 1541393)) (n := 12)
    (lo := (613609831 / 1000000000)) (hi := (76701229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 541393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 541393) = 1/(541393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76701229 / 125000000) (-613609831 / 1000000000) (Real.log (541393 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37809117 / 100000000) ≤ -Real.log (125000 / 182437) ∧
    -Real.log (125000 / 182437) ≤ (378091171 / 1000000000) := by
  have h := checkLog_sound (w := (57437 / 307437)) (n := 12)
    (lo := (37809117 / 100000000)) (hi := (378091171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182437 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182437 / 125000) = 1/(125000 / 182437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37809117 / 100000000) (378091171 / 1000000000) (Real.log (182437 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182437 / 125000) = -Real.log (125000 / 182437) := by
    rw [show ((182437 / 125000) : ℝ) = ((125000 / 182437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (615253241 / 1000000000) ≤ -Real.log (67563 / 125000) ∧
    -Real.log (67563 / 125000) ≤ (307626621 / 500000000) := by
  have h := checkLog_sound (w := (57437 / 192563)) (n := 12)
    (lo := (615253241 / 1000000000)) (hi := (307626621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 67563) = 1/(67563 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-307626621 / 500000000) (-615253241 / 1000000000) (Real.log (67563 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (147927789 / 500000000) ≤ -Real.log (250000 / 336069) ∧
    -Real.log (250000 / 336069) ≤ (295855579 / 1000000000) := by
  have h := checkLog_sound (w := (86069 / 586069)) (n := 12)
    (lo := (147927789 / 500000000)) (hi := (295855579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336069 / 250000) = 1/(250000 / 336069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (147927789 / 500000000) (295855579 / 1000000000) (Real.log (336069 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (336069 / 250000) = -Real.log (250000 / 336069) := by
    rw [show ((336069 / 250000) : ℝ) = ((250000 / 336069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (42201531 / 100000000) ≤ -Real.log (163931 / 250000) ∧
    -Real.log (163931 / 250000) ≤ (422015311 / 1000000000) := by
  have h := checkLog_sound (w := (86069 / 413931)) (n := 12)
    (lo := (42201531 / 100000000)) (hi := (422015311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163931) = 1/(163931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-422015311 / 1000000000) (-42201531 / 100000000) (Real.log (163931 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (296413343 / 1000000000) ≤ -Real.log (500000 / 672513) ∧
    -Real.log (500000 / 672513) ≤ (9262917 / 31250000) := by
  have h := checkLog_sound (w := (172513 / 1172513)) (n := 12)
    (lo := (296413343 / 1000000000)) (hi := (9262917 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672513 / 500000) = 1/(500000 / 672513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (296413343 / 1000000000) (9262917 / 31250000) (Real.log (672513 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (672513 / 500000) = -Real.log (500000 / 672513) := by
    rw [show ((672513 / 500000) : ℝ) = ((500000 / 672513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211579869 / 500000000) ≤ -Real.log (327487 / 500000) ∧
    -Real.log (327487 / 500000) ≤ (423159739 / 1000000000) := by
  have h := checkLog_sound (w := (172513 / 827487)) (n := 12)
    (lo := (211579869 / 500000000)) (hi := (423159739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 327487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 327487) = 1/(327487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-423159739 / 1000000000) (-211579869 / 500000000) (Real.log (327487 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (991091701 / 1000000000) ≤ -Real.log (100000000000 / 269417410273) ∧
    -Real.log (100000000000 / 269417410273) ≤ (991091703 / 1000000000) := by
  have h := checkLog_sound (w := (69417410273 / 469417410273)) (n := 12)
    (lo := (297944521 / 1000000000)) (hi := (148972261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269417410273 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269417410273 / 200000000000) = 1/(100000000000 / 269417410273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (991091701 / 1000000000) (991091703 / 1000000000) (Real.log (269417410273 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269417410273 / 100000000000) = -Real.log (100000000000 / 269417410273) := by
    rw [show ((269417410273 / 100000000000) : ℝ) = ((100000000000 / 269417410273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (993344411 / 1000000000) ≤ -Real.log (100000000000 / 270025013691) ∧
    -Real.log (100000000000 / 270025013691) ≤ (993344413 / 1000000000) := by
  have h := checkLog_sound (w := (70025013691 / 470025013691)) (n := 12)
    (lo := (300197231 / 1000000000)) (hi := (18762327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270025013691 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270025013691 / 200000000000) = 1/(100000000000 / 270025013691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (993344411 / 1000000000) (993344413 / 1000000000) (Real.log (270025013691 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270025013691 / 100000000000) = -Real.log (100000000000 / 270025013691) := by
    rw [show ((270025013691 / 100000000000) : ℝ) = ((100000000000 / 270025013691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (717870887 / 1000000000) ≤ -Real.log (250000000000 / 512515936583) ∧
    -Real.log (250000000000 / 512515936583) ≤ (717870889 / 1000000000) := by
  have h := checkLog_sound (w := (12515936583 / 1012515936583)) (n := 12)
    (lo := (24723707 / 1000000000)) (hi := (6180927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512515936583 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512515936583 / 500000000000) = 1/(250000000000 / 512515936583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (717870887 / 1000000000) (717870889 / 1000000000) (Real.log (512515936583 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (512515936583 / 250000000000) = -Real.log (250000000000 / 512515936583) := by
    rw [show ((512515936583 / 250000000000) : ℝ) = ((250000000000 / 512515936583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (719573081 / 1000000000) ≤ -Real.log (500000000000 / 1026778162187) ∧
    -Real.log (500000000000 / 1026778162187) ≤ (719573083 / 1000000000) := by
  have h := checkLog_sound (w := (26778162187 / 2026778162187)) (n := 12)
    (lo := (26425901 / 1000000000)) (hi := (13212951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026778162187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026778162187 / 1000000000000) = 1/(500000000000 / 1026778162187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (719573081 / 1000000000) (719573083 / 1000000000) (Real.log (1026778162187 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1026778162187 / 500000000000) = -Real.log (500000000000 / 1026778162187) := by
    rw [show ((1026778162187 / 500000000000) : ℝ) = ((500000000000 / 1026778162187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0176
