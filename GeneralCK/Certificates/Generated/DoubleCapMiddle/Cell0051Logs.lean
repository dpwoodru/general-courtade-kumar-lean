import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0051
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

theorem reflection_log_1_neg : (373716409 / 1000000000) ≤ -Real.log (64 / 93) ∧
    -Real.log (64 / 93) ≤ (37371641 / 100000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 64) = 1/(64 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (373716409 / 1000000000) (37371641 / 100000000) (Real.log (93 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (93 / 64) = -Real.log (64 / 93) := by
    rw [show ((93 / 64) : ℝ) = ((64 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (603535021 / 1000000000) ≤ -Real.log (35 / 64) ∧
    -Real.log (35 / 64) ≤ (301767511 / 500000000) := by
  have h := checkLog_sound (w := (29 / 99)) (n := 12)
    (lo := (603535021 / 1000000000)) (hi := (301767511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 35) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 35) = 1/(35 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301767511 / 500000000) (-603535021 / 1000000000) (Real.log (35 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5826713 / 15625000) ≤ -Real.log (2560 / 3717) ∧
    -Real.log (2560 / 3717) ≤ (372909633 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 6277)) (n := 12)
    (lo := (5826713 / 15625000)) (hi := (372909633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3717 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3717 / 2560) = 1/(2560 / 3717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5826713 / 15625000) (372909633 / 1000000000) (Real.log (3717 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3717 / 2560) = -Real.log (2560 / 3717) := by
    rw [show ((3717 / 2560) : ℝ) = ((2560 / 3717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (601394457 / 1000000000) ≤ -Real.log (1403 / 2560) ∧
    -Real.log (1403 / 2560) ≤ (300697229 / 500000000) := by
  have h := checkLog_sound (w := (1157 / 3963)) (n := 12)
    (lo := (601394457 / 1000000000)) (hi := (300697229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1403) = 1/(1403 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-300697229 / 500000000) (-601394457 / 1000000000) (Real.log (1403 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (645137961 / 1000000000) ≤ -Real.log (32 / 61) ∧
    -Real.log (32 / 61) ≤ (322568981 / 500000000) := by
  have h := checkLog_sound (w := (29 / 93)) (n := 12)
    (lo := (645137961 / 1000000000)) (hi := (322568981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 32) = 1/(32 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (645137961 / 1000000000) (322568981 / 500000000) (Real.log (61 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (61 / 32) = -Real.log (32 / 61) := by
    rw [show ((61 / 32) : ℝ) = ((32 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (591780903 / 250000000) ≤ -Real.log (3 / 32) ∧
    -Real.log (3 / 32) ≤ (73972613 / 31250000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4 / 3) = 1/(3 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-73972613 / 31250000) (-591780903 / 250000000) (Real.log (3 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40244231 / 62500000) ≤ -Real.log (1280 / 2437) ∧
    -Real.log (1280 / 2437) ≤ (643907697 / 1000000000) := by
  have h := checkLog_sound (w := (1157 / 3717)) (n := 12)
    (lo := (40244231 / 62500000)) (hi := (643907697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2437 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2437 / 1280) = 1/(1280 / 2437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40244231 / 62500000) (643907697 / 1000000000) (Real.log (2437 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2437 / 1280) = -Real.log (1280 / 2437) := by
    rw [show ((2437 / 1280) : ℝ) = ((1280 / 2437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2342430999 / 1000000000) ≤ -Real.log (123 / 1280) ∧
    -Real.log (123 / 1280) ≤ (2342431003 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 123) = 1/(123 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2342431003 / 1000000000) (-2342430999 / 1000000000) (Real.log (123 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (258217829 / 500000000) ≤ -Real.log (1000000 / 1676043) ∧
    -Real.log (1000000 / 1676043) ≤ (516435659 / 1000000000) := by
  have h := checkLog_sound (w := (676043 / 2676043)) (n := 12)
    (lo := (258217829 / 500000000)) (hi := (516435659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1676043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1676043 / 1000000) = 1/(1000000 / 1676043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (258217829 / 500000000) (516435659 / 1000000000) (Real.log (1676043 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1676043 / 1000000) = -Real.log (1000000 / 1676043) := by
    rw [show ((1676043 / 1000000) : ℝ) = ((1000000 / 1676043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1127144487 / 1000000000) ≤ -Real.log (323957 / 1000000) ∧
    -Real.log (323957 / 1000000) ≤ (1127144489 / 1000000000) := by
  have h := checkLog_sound (w := (176043 / 823957)) (n := 12)
    (lo := (433997307 / 1000000000)) (hi := (108499327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 323957) = 1/(323957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1127144489 / 1000000000) (-1127144487 / 1000000000) (Real.log (323957 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (517708681 / 1000000000) ≤ -Real.log (500000 / 839089) ∧
    -Real.log (500000 / 839089) ≤ (258854341 / 500000000) := by
  have h := checkLog_sound (w := (339089 / 1339089)) (n := 12)
    (lo := (517708681 / 1000000000)) (hi := (258854341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839089 / 500000) = 1/(500000 / 839089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (517708681 / 1000000000) (258854341 / 500000000) (Real.log (839089 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (839089 / 500000) = -Real.log (500000 / 839089) := by
    rw [show ((839089 / 500000) : ℝ) = ((500000 / 839089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28343917 / 25000000) ≤ -Real.log (160911 / 500000) ∧
    -Real.log (160911 / 500000) ≤ (566878341 / 500000000) := by
  have h := checkLog_sound (w := (89089 / 410911)) (n := 12)
    (lo := (881219 / 2000000)) (hi := (440609501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 160911) = 1/(160911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-566878341 / 500000000) (-28343917 / 25000000) (Real.log (160911 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (217940897 / 500000000) ≤ -Real.log (500000 / 773163) ∧
    -Real.log (500000 / 773163) ≤ (87176359 / 200000000) := by
  have h := checkLog_sound (w := (273163 / 1273163)) (n := 12)
    (lo := (217940897 / 500000000)) (hi := (87176359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773163 / 500000) = 1/(500000 / 773163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (217940897 / 500000000) (87176359 / 200000000) (Real.log (773163 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (773163 / 500000) = -Real.log (500000 / 773163) := by
    rw [show ((773163 / 500000) : ℝ) = ((500000 / 773163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (790376399 / 1000000000) ≤ -Real.log (226837 / 500000) ∧
    -Real.log (226837 / 500000) ≤ (790376401 / 1000000000) := by
  have h := checkLog_sound (w := (23163 / 476837)) (n := 12)
    (lo := (97229219 / 1000000000)) (hi := (4861461 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 226837) = 1/(226837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-790376401 / 1000000000) (-790376399 / 1000000000) (Real.log (226837 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (437308031 / 1000000000) ≤ -Real.log (1000000 / 1548533) ∧
    -Real.log (1000000 / 1548533) ≤ (3416469 / 7812500) := by
  have h := checkLog_sound (w := (548533 / 2548533)) (n := 12)
    (lo := (437308031 / 1000000000)) (hi := (3416469 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1548533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1548533 / 1000000) = 1/(1000000 / 1548533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (437308031 / 1000000000) (3416469 / 7812500) (Real.log (1548533 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1548533 / 1000000) = -Real.log (1000000 / 1548533) := by
    rw [show ((1548533 / 1000000) : ℝ) = ((1000000 / 1548533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (795252997 / 1000000000) ≤ -Real.log (451467 / 1000000) ∧
    -Real.log (451467 / 1000000) ≤ (795252999 / 1000000000) := by
  have h := checkLog_sound (w := (48533 / 951467)) (n := 12)
    (lo := (102105817 / 1000000000)) (hi := (51052909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 451467) = 1/(451467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-795252999 / 1000000000) (-795252997 / 1000000000) (Real.log (451467 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (102723759 / 62500000) ≤ -Real.log (125000000000 / 646707356223) ∧
    -Real.log (125000000000 / 646707356223) ≤ (1643580147 / 1000000000) := by
  have h := checkLog_sound (w := (146707356223 / 1146707356223)) (n := 12)
    (lo := (32160723 / 125000000)) (hi := (51457157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646707356223 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(646707356223 / 500000000000) = 1/(125000000000 / 646707356223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (102723759 / 62500000) (1643580147 / 1000000000) (Real.log (646707356223 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (646707356223 / 125000000000) = -Real.log (125000000000 / 646707356223) := by
    rw [show ((646707356223 / 125000000000) : ℝ) = ((125000000000 / 646707356223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1651465361 / 1000000000) ≤ -Real.log (250000000000 / 1303653883203) ∧
    -Real.log (250000000000 / 1303653883203) ≤ (412866341 / 250000000) := by
  have h := checkLog_sound (w := (303653883203 / 2303653883203)) (n := 12)
    (lo := (265171001 / 1000000000)) (hi := (132585501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303653883203 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1303653883203 / 1000000000000) = 1/(250000000000 / 1303653883203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1651465361 / 1000000000) (412866341 / 250000000) (Real.log (1303653883203 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1303653883203 / 250000000000) = -Real.log (250000000000 / 1303653883203) := by
    rw [show ((1303653883203 / 250000000000) : ℝ) = ((250000000000 / 1303653883203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (613129097 / 500000000) ≤ -Real.log (20000000000 / 68169037679) ∧
    -Real.log (20000000000 / 68169037679) ≤ (306564549 / 250000000) := by
  have h := checkLog_sound (w := (28169037679 / 108169037679)) (n := 12)
    (lo := (266555507 / 500000000)) (hi := (106622203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68169037679 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68169037679 / 40000000000) = 1/(20000000000 / 68169037679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (613129097 / 500000000) (306564549 / 250000000) (Real.log (68169037679 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (68169037679 / 20000000000) = -Real.log (20000000000 / 68169037679) := by
    rw [show ((68169037679 / 20000000000) : ℝ) = ((20000000000 / 68169037679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1232561029 / 1000000000) ≤ -Real.log (250000000000 / 857500658963) ∧
    -Real.log (250000000000 / 857500658963) ≤ (1232561031 / 1000000000) := by
  have h := checkLog_sound (w := (357500658963 / 1357500658963)) (n := 12)
    (lo := (539413849 / 1000000000)) (hi := (10788277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857500658963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(857500658963 / 500000000000) = 1/(250000000000 / 857500658963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1232561029 / 1000000000) (1232561031 / 1000000000) (Real.log (857500658963 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (857500658963 / 250000000000) = -Real.log (250000000000 / 857500658963) := by
    rw [show ((857500658963 / 250000000000) : ℝ) = ((250000000000 / 857500658963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0051
