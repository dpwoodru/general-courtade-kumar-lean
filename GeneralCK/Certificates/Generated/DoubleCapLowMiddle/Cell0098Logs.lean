import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0098
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

theorem reflection_log_1_neg : (671787873 / 1000000000) ≤ -Real.log (12800 / 25059) ∧
    -Real.log (12800 / 25059) ≤ (335893937 / 500000000) := by
  have h := checkLog_sound (w := (12259 / 37859)) (n := 12)
    (lo := (671787873 / 1000000000)) (hi := (335893937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25059 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25059 / 12800) = 1/(12800 / 25059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (671787873 / 1000000000) (335893937 / 500000000) (Real.log (25059 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25059 / 12800) = -Real.log (12800 / 25059) := by
    rw [show ((25059 / 12800) : ℝ) = ((12800 / 25059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197736323 / 62500000) ≤ -Real.log (541 / 12800) ∧
    -Real.log (541 / 12800) ≤ (3163781173 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 541) = 1/(541 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3163781173 / 1000000000) (-197736323 / 62500000) (Real.log (541 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335799151 / 500000000) ≤ -Real.log (51200 / 100217) ∧
    -Real.log (51200 / 100217) ≤ (671598303 / 1000000000) := by
  have h := checkLog_sound (w := (49017 / 151417)) (n := 12)
    (lo := (335799151 / 500000000)) (hi := (671598303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100217 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100217 / 51200) = 1/(51200 / 100217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335799151 / 500000000) (671598303 / 1000000000) (Real.log (100217 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100217 / 51200) = -Real.log (51200 / 100217) := by
    rw [show ((100217 / 51200) : ℝ) = ((51200 / 100217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (788759863 / 250000000) ≤ -Real.log (2183 / 51200) ∧
    -Real.log (2183 / 51200) ≤ (3155039457 / 1000000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2183) = 1/(2183 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3155039457 / 1000000000) (-788759863 / 250000000) (Real.log (2183 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (64996237 / 100000000) ≤ -Real.log (6400 / 12259) ∧
    -Real.log (6400 / 12259) ≤ (649962371 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 18659)) (n := 12)
    (lo := (64996237 / 100000000)) (hi := (649962371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12259 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12259 / 6400) = 1/(6400 / 12259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (64996237 / 100000000) (649962371 / 1000000000) (Real.log (12259 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12259 / 6400) = -Real.log (6400 / 12259) := by
    rw [show ((12259 / 6400) : ℝ) = ((6400 / 12259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617658497 / 250000000) ≤ -Real.log (541 / 6400) ∧
    -Real.log (541 / 6400) ≤ (308829249 / 125000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 541) = 1/(541 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-308829249 / 125000000) (-617658497 / 250000000) (Real.log (541 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25982993 / 40000000) ≤ -Real.log (25600 / 49017) ∧
    -Real.log (25600 / 49017) ≤ (324787413 / 500000000) := by
  have h := checkLog_sound (w := (23417 / 74617)) (n := 12)
    (lo := (25982993 / 40000000)) (hi := (324787413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49017 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49017 / 25600) = 1/(25600 / 49017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25982993 / 40000000) (324787413 / 500000000) (Real.log (49017 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49017 / 25600) = -Real.log (25600 / 49017) := by
    rw [show ((49017 / 25600) : ℝ) = ((25600 / 49017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153868267 / 62500000) ≤ -Real.log (2183 / 25600) ∧
    -Real.log (2183 / 25600) ≤ (615473069 / 250000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2183) = 1/(2183 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-615473069 / 250000000) (-153868267 / 62500000) (Real.log (2183 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42218647 / 62500000) ≤ -Real.log (250000 / 491253) ∧
    -Real.log (250000 / 491253) ≤ (675498353 / 1000000000) := by
  have h := checkLog_sound (w := (241253 / 741253)) (n := 12)
    (lo := (42218647 / 62500000)) (hi := (675498353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491253 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491253 / 250000) = 1/(250000 / 491253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42218647 / 62500000) (675498353 / 1000000000) (Real.log (491253 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (491253 / 250000) = -Real.log (250000 / 491253) := by
    rw [show ((491253 / 250000) : ℝ) = ((250000 / 491253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3352750131 / 1000000000) ≤ -Real.log (8747 / 250000) ∧
    -Real.log (8747 / 250000) ≤ (419093767 / 125000000) := by
  have h := checkLog_sound (w := (3439 / 12186)) (n := 12)
    (lo := (580161411 / 1000000000)) (hi := (145040353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8747) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8747) = 1/(8747 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-419093767 / 125000000) (-3352750131 / 1000000000) (Real.log (8747 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135128981 / 200000000) ≤ -Real.log (10000 / 19653) ∧
    -Real.log (10000 / 19653) ≤ (337822453 / 500000000) := by
  have h := checkLog_sound (w := (9653 / 29653)) (n := 12)
    (lo := (135128981 / 200000000)) (hi := (337822453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19653 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19653 / 10000) = 1/(10000 / 19653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135128981 / 200000000) (337822453 / 500000000) (Real.log (19653 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19653 / 10000) = -Real.log (10000 / 19653) := by
    rw [show ((19653 / 10000) : ℝ) = ((10000 / 19653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3361015589 / 1000000000) ≤ -Real.log (347 / 10000) ∧
    -Real.log (347 / 10000) ≤ (1680507797 / 500000000) := by
  have h := checkLog_sound (w := (139 / 486)) (n := 12)
    (lo := (588426869 / 1000000000)) (hi := (58842687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 347) = 1/(347 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1680507797 / 500000000) (-3361015589 / 1000000000) (Real.log (347 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135065571 / 200000000) ≤ -Real.log (1000000 / 1964677) ∧
    -Real.log (1000000 / 1964677) ≤ (42207991 / 62500000) := by
  have h := checkLog_sound (w := (964677 / 2964677)) (n := 12)
    (lo := (135065571 / 200000000)) (hi := (42207991 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964677 / 1000000) = 1/(1000000 / 1964677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135065571 / 200000000) (42207991 / 62500000) (Real.log (1964677 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964677 / 1000000) = -Real.log (1000000 / 1964677) := by
    rw [show ((1964677 / 1000000) : ℝ) = ((1000000 / 1964677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1671610483 / 500000000) ≤ -Real.log (35323 / 1000000) ∧
    -Real.log (35323 / 1000000) ≤ (3343220971 / 1000000000) := by
  have h := checkLog_sound (w := (27177 / 97823)) (n := 12)
    (lo := (285316123 / 500000000)) (hi := (570632247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35323) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35323) = 1/(35323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3343220971 / 1000000000) (-1671610483 / 500000000) (Real.log (35323 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135095599 / 200000000) ≤ -Real.log (250000 / 491243) ∧
    -Real.log (250000 / 491243) ≤ (168869499 / 250000000) := by
  have h := checkLog_sound (w := (241243 / 741243)) (n := 12)
    (lo := (135095599 / 200000000)) (hi := (168869499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491243 / 250000) = 1/(250000 / 491243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135095599 / 200000000) (168869499 / 250000000) (Real.log (491243 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (491243 / 250000) = -Real.log (250000 / 491243) := by
    rw [show ((491243 / 250000) : ℝ) = ((250000 / 491243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (670321507 / 200000000) ≤ -Real.log (8757 / 250000) ∧
    -Real.log (8757 / 250000) ≤ (167580377 / 50000000) := by
  have h := checkLog_sound (w := (3434 / 12191)) (n := 12)
    (lo := (115803763 / 200000000)) (hi := (9047169 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8757) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8757) = 1/(8757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-167580377 / 50000000) (-670321507 / 200000000) (Real.log (8757 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2014124241 / 500000000) ≤ -Real.log (125000000000 / 7020306962387) ∧
    -Real.log (125000000000 / 7020306962387) ≤ (503531061 / 125000000) := by
  have h := checkLog_sound (w := (3020306962387 / 11020306962387)) (n := 12)
    (lo := (281256291 / 500000000)) (hi := (562512583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7020306962387 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7020306962387 / 4000000000000) = 1/(125000000000 / 7020306962387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2014124241 / 500000000) (503531061 / 125000000) (Real.log (7020306962387 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7020306962387 / 125000000000) = -Real.log (125000000000 / 7020306962387) := by
    rw [show ((7020306962387 / 125000000000) : ℝ) = ((125000000000 / 7020306962387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2018330247 / 500000000) ≤ -Real.log (100000000000 / 5663688760807) ∧
    -Real.log (100000000000 / 5663688760807) ≤ (8073321 / 2000000) := by
  have h := checkLog_sound (w := (2463688760807 / 8863688760807)) (n := 12)
    (lo := (285462297 / 500000000)) (hi := (114184919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5663688760807 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5663688760807 / 3200000000000) = 1/(100000000000 / 5663688760807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2018330247 / 500000000) (8073321 / 2000000) (Real.log (5663688760807 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5663688760807 / 100000000000) = -Real.log (100000000000 / 5663688760807) := by
    rw [show ((5663688760807 / 100000000000) : ℝ) = ((100000000000 / 5663688760807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4018548821 / 1000000000) ≤ -Real.log (20000000000 / 1112406647227) ∧
    -Real.log (20000000000 / 1112406647227) ≤ (4018548827 / 1000000000) := by
  have h := checkLog_sound (w := (472406647227 / 1752406647227)) (n := 12)
    (lo := (552812921 / 1000000000)) (hi := (276406461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112406647227 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1112406647227 / 640000000000) = 1/(20000000000 / 1112406647227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4018548821 / 1000000000) (4018548827 / 1000000000) (Real.log (1112406647227 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1112406647227 / 20000000000) = -Real.log (20000000000 / 1112406647227) := by
    rw [show ((1112406647227 / 20000000000) : ℝ) = ((20000000000 / 1112406647227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (402708553 / 100000000) ≤ -Real.log (500000000000 / 28048589699669) ∧
    -Real.log (500000000000 / 28048589699669) ≤ (125846423 / 31250000) := by
  have h := checkLog_sound (w := (12048589699669 / 44048589699669)) (n := 12)
    (lo := (56134963 / 100000000)) (hi := (561349631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28048589699669 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28048589699669 / 16000000000000) = 1/(500000000000 / 28048589699669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (402708553 / 100000000) (125846423 / 31250000) (Real.log (28048589699669 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28048589699669 / 500000000000) = -Real.log (500000000000 / 28048589699669) := by
    rw [show ((28048589699669 / 500000000000) : ℝ) = ((500000000000 / 28048589699669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0098
