import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0074
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

theorem reflection_log_1_neg : (33816341 / 50000000) ≤ -Real.log (12800 / 25173) ∧
    -Real.log (12800 / 25173) ≤ (676326821 / 1000000000) := by
  have h := checkLog_sound (w := (12373 / 37973)) (n := 12)
    (lo := (33816341 / 50000000)) (hi := (676326821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25173 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25173 / 12800) = 1/(12800 / 25173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33816341 / 50000000) (676326821 / 1000000000) (Real.log (25173 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25173 / 12800) = -Real.log (12800 / 25173) := by
    rw [show ((25173 / 12800) : ℝ) = ((12800 / 25173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1700208217 / 500000000) ≤ -Real.log (427 / 12800) ∧
    -Real.log (427 / 12800) ≤ (3400416439 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 427) = 1/(427 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3400416439 / 1000000000) (-1700208217 / 500000000) (Real.log (427 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169034527 / 250000000) ≤ -Real.log (51200 / 100673) ∧
    -Real.log (51200 / 100673) ≤ (676138109 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 151873)) (n := 12)
    (lo := (169034527 / 250000000)) (hi := (676138109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100673 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100673 / 51200) = 1/(51200 / 100673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169034527 / 250000000) (676138109 / 1000000000) (Real.log (100673 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100673 / 51200) = -Real.log (51200 / 100673) := by
    rw [show ((100673 / 51200) : ℝ) = ((51200 / 100673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338935373 / 100000000) ≤ -Real.log (1727 / 51200) ∧
    -Real.log (1727 / 51200) ≤ (677870747 / 200000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1727) = 1/(1727 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-677870747 / 200000000) (-338935373 / 100000000) (Real.log (1727 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2575073 / 3906250) ≤ -Real.log (6400 / 12373) ∧
    -Real.log (6400 / 12373) ≤ (659218689 / 1000000000) := by
  have h := checkLog_sound (w := (5973 / 18773)) (n := 12)
    (lo := (2575073 / 3906250)) (hi := (659218689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12373 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12373 / 6400) = 1/(6400 / 12373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2575073 / 3906250) (659218689 / 1000000000) (Real.log (12373 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12373 / 6400) = -Real.log (6400 / 12373) := by
    rw [show ((12373 / 6400) : ℝ) = ((6400 / 12373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1353634627 / 500000000) ≤ -Real.log (427 / 6400) ∧
    -Real.log (427 / 6400) ≤ (1353634629 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 427) = 1/(427 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1353634629 / 500000000) (-1353634627 / 500000000) (Real.log (427 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (329417357 / 500000000) ≤ -Real.log (25600 / 49473) ∧
    -Real.log (25600 / 49473) ≤ (131766943 / 200000000) := by
  have h := checkLog_sound (w := (23873 / 75073)) (n := 12)
    (lo := (329417357 / 500000000)) (hi := (131766943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49473 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49473 / 25600) = 1/(25600 / 49473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (329417357 / 500000000) (131766943 / 200000000) (Real.log (49473 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49473 / 25600) = -Real.log (25600 / 49473) := by
    rw [show ((49473 / 25600) : ℝ) = ((25600 / 49473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (53924131 / 20000000) ≤ -Real.log (1727 / 25600) ∧
    -Real.log (1727 / 25600) ≤ (1348103277 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1727) = 1/(1727 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1348103277 / 500000000) (-53924131 / 20000000) (Real.log (1727 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67903 / 100000) ≤ -Real.log (250000 / 492991) ∧
    -Real.log (250000 / 492991) ≤ (679030001 / 1000000000) := by
  have h := checkLog_sound (w := (242991 / 742991)) (n := 12)
    (lo := (67903 / 100000)) (hi := (679030001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492991 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492991 / 250000) = 1/(250000 / 492991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67903 / 100000) (679030001 / 1000000000) (Real.log (492991 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (492991 / 250000) = -Real.log (250000 / 492991) := by
    rw [show ((492991 / 250000) : ℝ) = ((250000 / 492991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3574265877 / 1000000000) ≤ -Real.log (7009 / 250000) ∧
    -Real.log (7009 / 250000) ≤ (3574265883 / 1000000000) := by
  have h := checkLog_sound (w := (1607 / 29643)) (n := 12)
    (lo := (108529977 / 1000000000)) (hi := (54264989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14018) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14018) = 1/(7009 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3574265883 / 1000000000) (-3574265877 / 1000000000) (Real.log (7009 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169794643 / 250000000) ≤ -Real.log (1000000 / 1972257) ∧
    -Real.log (1000000 / 1972257) ≤ (679178573 / 1000000000) := by
  have h := checkLog_sound (w := (972257 / 2972257)) (n := 12)
    (lo := (169794643 / 250000000)) (hi := (679178573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972257 / 1000000) = 1/(1000000 / 1972257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169794643 / 250000000) (679178573 / 1000000000) (Real.log (1972257 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1972257 / 1000000) = -Real.log (1000000 / 1972257) := by
    rw [show ((1972257 / 1000000) : ℝ) = ((1000000 / 1972257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89619293 / 25000000) ≤ -Real.log (27743 / 1000000) ∧
    -Real.log (27743 / 1000000) ≤ (1792385863 / 500000000) := by
  have h := checkLog_sound (w := (3507 / 58993)) (n := 12)
    (lo := (5951791 / 50000000)) (hi := (119035821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27743) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27743) = 1/(27743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1792385863 / 500000000) (-89619293 / 25000000) (Real.log (27743 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678929587 / 1000000000) ≤ -Real.log (500000 / 985883) ∧
    -Real.log (500000 / 985883) ≤ (169732397 / 250000000) := by
  have h := checkLog_sound (w := (485883 / 1485883)) (n := 12)
    (lo := (678929587 / 1000000000)) (hi := (169732397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985883 / 500000) = 1/(500000 / 985883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678929587 / 1000000000) (169732397 / 250000000) (Real.log (985883 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (985883 / 500000) = -Real.log (500000 / 985883) := by
    rw [show ((985883 / 500000) : ℝ) = ((500000 / 985883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71344567 / 20000000) ≤ -Real.log (14117 / 500000) ∧
    -Real.log (14117 / 500000) ≤ (891807089 / 250000000) := by
  have h := checkLog_sound (w := (754 / 14871)) (n := 12)
    (lo := (2029849 / 20000000)) (hi := (101492451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14117) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14117) = 1/(14117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-891807089 / 250000000) (-71344567 / 20000000) (Real.log (14117 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679081217 / 1000000000) ≤ -Real.log (200000 / 394413) ∧
    -Real.log (200000 / 394413) ≤ (339540609 / 500000000) := by
  have h := checkLog_sound (w := (194413 / 594413)) (n := 12)
    (lo := (679081217 / 1000000000)) (hi := (339540609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394413 / 200000) = 1/(200000 / 394413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679081217 / 1000000000) (339540609 / 500000000) (Real.log (394413 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394413 / 200000) = -Real.log (200000 / 394413) := by
    rw [show ((394413 / 200000) : ℝ) = ((200000 / 394413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3577874893 / 1000000000) ≤ -Real.log (5587 / 200000) ∧
    -Real.log (5587 / 200000) ≤ (3577874899 / 1000000000) := by
  have h := checkLog_sound (w := (663 / 11837)) (n := 12)
    (lo := (112138993 / 1000000000)) (hi := (56069497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5587) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5587) = 1/(5587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3577874899 / 1000000000) (-3577874893 / 1000000000) (Real.log (5587 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4253295877 / 1000000000) ≤ -Real.log (500000000000 / 35168426309031) ∧
    -Real.log (500000000000 / 35168426309031) ≤ (1063323971 / 250000000) := by
  have h := checkLog_sound (w := (3168426309031 / 67168426309031)) (n := 12)
    (lo := (94412797 / 1000000000)) (hi := (47206399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35168426309031 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35168426309031 / 32000000000000) = 1/(500000000000 / 35168426309031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4253295877 / 1000000000) (1063323971 / 250000000) (Real.log (35168426309031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (35168426309031 / 500000000000) = -Real.log (500000000000 / 35168426309031) := by
    rw [show ((35168426309031 / 500000000000) : ℝ) = ((500000000000 / 35168426309031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4263950291 / 1000000000) ≤ -Real.log (125000000000 / 8886282125221) ∧
    -Real.log (125000000000 / 8886282125221) ≤ (2131975149 / 500000000) := by
  have h := checkLog_sound (w := (886282125221 / 16886282125221)) (n := 12)
    (lo := (105067211 / 1000000000)) (hi := (26266803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8886282125221 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8886282125221 / 8000000000000) = 1/(125000000000 / 8886282125221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4263950291 / 1000000000) (2131975149 / 500000000) (Real.log (8886282125221 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8886282125221 / 125000000000) = -Real.log (125000000000 / 8886282125221) := by
    rw [show ((8886282125221 / 125000000000) : ℝ) = ((125000000000 / 8886282125221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2123078969 / 500000000) ≤ -Real.log (250000000000 / 17459145002479) ∧
    -Real.log (250000000000 / 17459145002479) ≤ (849231589 / 200000000) := by
  have h := checkLog_sound (w := (1459145002479 / 33459145002479)) (n := 12)
    (lo := (43637429 / 500000000)) (hi := (87274859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17459145002479 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17459145002479 / 16000000000000) = 1/(250000000000 / 17459145002479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2123078969 / 500000000) (849231589 / 200000000) (Real.log (17459145002479 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17459145002479 / 250000000000) = -Real.log (250000000000 / 17459145002479) := by
    rw [show ((17459145002479 / 250000000000) : ℝ) = ((250000000000 / 17459145002479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4256956109 / 1000000000) ≤ -Real.log (100000000000 / 7059477358153) ∧
    -Real.log (100000000000 / 7059477358153) ≤ (1064239029 / 250000000) := by
  have h := checkLog_sound (w := (659477358153 / 13459477358153)) (n := 12)
    (lo := (98073029 / 1000000000)) (hi := (9807303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7059477358153 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7059477358153 / 6400000000000) = 1/(100000000000 / 7059477358153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4256956109 / 1000000000) (1064239029 / 250000000) (Real.log (7059477358153 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7059477358153 / 100000000000) = -Real.log (100000000000 / 7059477358153) := by
    rw [show ((7059477358153 / 100000000000) : ℝ) = ((100000000000 / 7059477358153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0074
