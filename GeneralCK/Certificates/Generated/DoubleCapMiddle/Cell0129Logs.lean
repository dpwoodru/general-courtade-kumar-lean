import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0129
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

theorem reflection_log_1_neg : (38593461 / 125000000) ≤ -Real.log (1280 / 1743) ∧
    -Real.log (1280 / 1743) ≤ (308747689 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3023)) (n := 12)
    (lo := (38593461 / 125000000)) (hi := (308747689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1280) = 1/(1280 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38593461 / 125000000) (308747689 / 1000000000) (Real.log (1743 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1743 / 1280) = -Real.log (1280 / 1743) := by
    rw [show ((1743 / 1280) : ℝ) = ((1280 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224488131 / 500000000) ≤ -Real.log (817 / 1280) ∧
    -Real.log (817 / 1280) ≤ (448976263 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2097)) (n := 12)
    (lo := (224488131 / 500000000)) (hi := (448976263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 817) = 1/(817 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-448976263 / 1000000000) (-224488131 / 500000000) (Real.log (817 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (76971683 / 250000000) ≤ -Real.log (2560 / 3483) ∧
    -Real.log (2560 / 3483) ≤ (307886733 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 6043)) (n := 12)
    (lo := (76971683 / 250000000)) (hi := (307886733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3483 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3483 / 2560) = 1/(2560 / 3483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (76971683 / 250000000) (307886733 / 1000000000) (Real.log (3483 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3483 / 2560) = -Real.log (2560 / 3483) := by
    rw [show ((3483 / 2560) : ℝ) = ((2560 / 3483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11178549 / 25000000) ≤ -Real.log (1637 / 2560) ∧
    -Real.log (1637 / 2560) ≤ (447141961 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 4197)) (n := 12)
    (lo := (11178549 / 25000000)) (hi := (447141961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1637) = 1/(1637 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-447141961 / 1000000000) (-11178549 / 25000000) (Real.log (1637 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (272160421 / 500000000) ≤ -Real.log (640 / 1103) ∧
    -Real.log (640 / 1103) ≤ (544320843 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1743)) (n := 12)
    (lo := (272160421 / 500000000)) (hi := (544320843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103 / 640) = 1/(640 / 1103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (272160421 / 500000000) (544320843 / 1000000000) (Real.log (1103 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1103 / 640) = -Real.log (640 / 1103) := by
    rw [show ((1103 / 640) : ℝ) = ((640 / 1103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1285318443 / 1000000000) ≤ -Real.log (177 / 640) ∧
    -Real.log (177 / 640) ≤ (257063689 / 200000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 177) = 1/(177 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-257063689 / 200000000) (-1285318443 / 1000000000) (Real.log (177 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (542959989 / 1000000000) ≤ -Real.log (1280 / 2203) ∧
    -Real.log (1280 / 2203) ≤ (54295999 / 100000000) := by
  have h := checkLog_sound (w := (923 / 3483)) (n := 12)
    (lo := (542959989 / 1000000000)) (hi := (54295999 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2203 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2203 / 1280) = 1/(1280 / 2203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (542959989 / 1000000000) (54295999 / 100000000) (Real.log (2203 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2203 / 1280) = -Real.log (1280 / 2203) := by
    rw [show ((2203 / 1280) : ℝ) = ((1280 / 2203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638439787 / 500000000) ≤ -Real.log (357 / 1280) ∧
    -Real.log (357 / 1280) ≤ (159609947 / 125000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 357) = 1/(357 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159609947 / 125000000) (-638439787 / 500000000) (Real.log (357 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (421569401 / 1000000000) ≤ -Real.log (15625 / 23818) ∧
    -Real.log (15625 / 23818) ≤ (210784701 / 500000000) := by
  have h := checkLog_sound (w := (8193 / 39443)) (n := 12)
    (lo := (421569401 / 1000000000)) (hi := (210784701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23818 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23818 / 15625) = 1/(15625 / 23818) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (421569401 / 1000000000) (210784701 / 500000000) (Real.log (23818 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23818 / 15625) = -Real.log (15625 / 23818) := by
    rw [show ((23818 / 15625) : ℝ) = ((15625 / 23818) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (743077193 / 1000000000) ≤ -Real.log (7432 / 15625) ∧
    -Real.log (7432 / 15625) ≤ (148615439 / 200000000) := by
  have h := checkLog_sound (w := (761 / 30489)) (n := 12)
    (lo := (49930013 / 1000000000)) (hi := (24965007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14864) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14864) = 1/(7432 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-148615439 / 200000000) (-743077193 / 1000000000) (Real.log (7432 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (422771157 / 1000000000) ≤ -Real.log (200000 / 305237) ∧
    -Real.log (200000 / 305237) ≤ (211385579 / 500000000) := by
  have h := checkLog_sound (w := (105237 / 505237)) (n := 12)
    (lo := (422771157 / 1000000000)) (hi := (211385579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305237 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305237 / 200000) = 1/(200000 / 305237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (422771157 / 1000000000) (211385579 / 500000000) (Real.log (305237 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (305237 / 200000) = -Real.log (200000 / 305237) := by
    rw [show ((305237 / 200000) : ℝ) = ((200000 / 305237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93367291 / 125000000) ≤ -Real.log (94763 / 200000) ∧
    -Real.log (94763 / 200000) ≤ (74693833 / 100000000) := by
  have h := checkLog_sound (w := (5237 / 194763)) (n := 12)
    (lo := (13447787 / 250000000)) (hi := (53791149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94763) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94763) = 1/(94763 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-74693833 / 100000000) (-93367291 / 125000000) (Real.log (94763 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67461663 / 200000000) ≤ -Real.log (1000000 / 1401171) ∧
    -Real.log (1000000 / 1401171) ≤ (84327079 / 250000000) := by
  have h := checkLog_sound (w := (401171 / 2401171)) (n := 12)
    (lo := (67461663 / 200000000)) (hi := (84327079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401171 / 1000000) = 1/(1000000 / 1401171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67461663 / 200000000) (84327079 / 250000000) (Real.log (1401171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1401171 / 1000000) = -Real.log (1000000 / 1401171) := by
    rw [show ((1401171 / 1000000) : ℝ) = ((1000000 / 1401171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (512779197 / 1000000000) ≤ -Real.log (598829 / 1000000) ∧
    -Real.log (598829 / 1000000) ≤ (256389599 / 500000000) := by
  have h := checkLog_sound (w := (401171 / 1598829)) (n := 12)
    (lo := (512779197 / 1000000000)) (hi := (256389599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 598829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 598829) = 1/(598829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256389599 / 500000000) (-512779197 / 1000000000) (Real.log (598829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338472377 / 1000000000) ≤ -Real.log (1000000 / 1402803) ∧
    -Real.log (1000000 / 1402803) ≤ (169236189 / 500000000) := by
  have h := checkLog_sound (w := (402803 / 2402803)) (n := 12)
    (lo := (338472377 / 1000000000)) (hi := (169236189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1402803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1402803 / 1000000) = 1/(1000000 / 1402803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338472377 / 1000000000) (169236189 / 500000000) (Real.log (1402803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1402803 / 1000000) = -Real.log (1000000 / 1402803) := by
    rw [show ((1402803 / 1000000) : ℝ) = ((1000000 / 1402803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128877059 / 250000000) ≤ -Real.log (597197 / 1000000) ∧
    -Real.log (597197 / 1000000) ≤ (515508237 / 1000000000) := by
  have h := checkLog_sound (w := (402803 / 1597197)) (n := 12)
    (lo := (128877059 / 250000000)) (hi := (515508237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 597197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 597197) = 1/(597197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-515508237 / 1000000000) (-128877059 / 250000000) (Real.log (597197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (232929319 / 200000000) ≤ -Real.log (500000000000 / 1602395048439) ∧
    -Real.log (500000000000 / 1602395048439) ≤ (1164646597 / 1000000000) := by
  have h := checkLog_sound (w := (602395048439 / 2602395048439)) (n := 12)
    (lo := (94299883 / 200000000)) (hi := (58937427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1602395048439 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1602395048439 / 1000000000000) = 1/(500000000000 / 1602395048439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (232929319 / 200000000) (1164646597 / 1000000000) (Real.log (1602395048439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1602395048439 / 500000000000) = -Real.log (500000000000 / 1602395048439) := by
    rw [show ((1602395048439 / 500000000000) : ℝ) = ((500000000000 / 1602395048439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (233941897 / 200000000) ≤ -Real.log (250000000000 / 805264185389) ∧
    -Real.log (250000000000 / 805264185389) ≤ (1169709487 / 1000000000) := by
  have h := checkLog_sound (w := (305264185389 / 1305264185389)) (n := 12)
    (lo := (95312461 / 200000000)) (hi := (238281153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805264185389 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(805264185389 / 500000000000) = 1/(250000000000 / 805264185389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (233941897 / 200000000) (1169709487 / 1000000000) (Real.log (805264185389 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (805264185389 / 250000000000) = -Real.log (250000000000 / 805264185389) := by
    rw [show ((805264185389 / 250000000000) : ℝ) = ((250000000000 / 805264185389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (106260939 / 125000000) ≤ -Real.log (125000000000 / 292481451299) ∧
    -Real.log (125000000000 / 292481451299) ≤ (425043757 / 500000000) := by
  have h := checkLog_sound (w := (42481451299 / 542481451299)) (n := 12)
    (lo := (39235083 / 250000000)) (hi := (156940333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292481451299 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292481451299 / 250000000000) = 1/(125000000000 / 292481451299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (106260939 / 125000000) (425043757 / 500000000) (Real.log (292481451299 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (292481451299 / 125000000000) = -Real.log (125000000000 / 292481451299) := by
    rw [show ((292481451299 / 125000000000) : ℝ) = ((125000000000 / 292481451299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426990307 / 500000000) ≤ -Real.log (500000000000 / 1174489322619) ∧
    -Real.log (500000000000 / 1174489322619) ≤ (106747577 / 125000000) := by
  have h := checkLog_sound (w := (174489322619 / 2174489322619)) (n := 12)
    (lo := (80416717 / 500000000)) (hi := (32166687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174489322619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1174489322619 / 1000000000000) = 1/(500000000000 / 1174489322619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426990307 / 500000000) (106747577 / 125000000) (Real.log (1174489322619 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1174489322619 / 500000000000) = -Real.log (500000000000 / 1174489322619) := by
    rw [show ((1174489322619 / 500000000000) : ℝ) = ((500000000000 / 1174489322619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0129
