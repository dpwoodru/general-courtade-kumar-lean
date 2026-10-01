import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0215
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

theorem reflection_log_1_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134534189 / 250000000) ≤ -Real.log (3200 / 5481) ∧
    -Real.log (3200 / 5481) ≤ (538136757 / 1000000000) := by
  have h := checkLog_sound (w := (2281 / 8681)) (n := 12)
    (lo := (134534189 / 250000000)) (hi := (538136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5481 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5481 / 3200) = 1/(3200 / 5481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134534189 / 250000000) (538136757 / 1000000000) (Real.log (5481 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5481 / 3200) = -Real.log (3200 / 5481) := by
    rw [show ((5481 / 3200) : ℝ) = ((3200 / 5481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249523993 / 200000000) ≤ -Real.log (919 / 3200) ∧
    -Real.log (919 / 3200) ≤ (1247619967 / 1000000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 919) = 1/(919 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1247619967 / 1000000000) (-249523993 / 200000000) (Real.log (919 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177305157 / 500000000) ≤ -Real.log (1600 / 2281) ∧
    -Real.log (1600 / 2281) ≤ (70922063 / 200000000) := by
  have h := checkLog_sound (w := (681 / 3881)) (n := 12)
    (lo := (177305157 / 500000000)) (hi := (70922063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1600) = 1/(1600 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177305157 / 500000000) (70922063 / 200000000) (Real.log (2281 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2281 / 1600) = -Real.log (1600 / 2281) := by
    rw [show ((2281 / 1600) : ℝ) = ((1600 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (110894557 / 200000000) ≤ -Real.log (919 / 1600) ∧
    -Real.log (919 / 1600) ≤ (277236393 / 500000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 919) = 1/(919 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277236393 / 500000000) (-110894557 / 200000000) (Real.log (919 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (600128523 / 1000000000) ≤ -Real.log (1000000 / 1822353) ∧
    -Real.log (1000000 / 1822353) ≤ (150032131 / 250000000) := by
  have h := checkLog_sound (w := (822353 / 2822353)) (n := 12)
    (lo := (600128523 / 1000000000)) (hi := (150032131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1822353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1822353 / 1000000) = 1/(1000000 / 1822353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (600128523 / 1000000000) (150032131 / 250000000) (Real.log (1822353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1822353 / 1000000) = -Real.log (1000000 / 1822353) := by
    rw [show ((1822353 / 1000000) : ℝ) = ((1000000 / 1822353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (863978421 / 500000000) ≤ -Real.log (177647 / 1000000) ∧
    -Real.log (177647 / 1000000) ≤ (345591369 / 200000000) := by
  have h := checkLog_sound (w := (72353 / 427647)) (n := 12)
    (lo := (170831241 / 500000000)) (hi := (341662483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177647) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 177647) = 1/(177647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-345591369 / 200000000) (-863978421 / 500000000) (Real.log (177647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (300708343 / 500000000) ≤ -Real.log (500000 / 912351) ∧
    -Real.log (500000 / 912351) ≤ (601416687 / 1000000000) := by
  have h := checkLog_sound (w := (412351 / 1412351)) (n := 12)
    (lo := (300708343 / 500000000)) (hi := (601416687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912351 / 500000) = 1/(500000 / 912351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (300708343 / 500000000) (601416687 / 1000000000) (Real.log (912351 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (912351 / 500000) = -Real.log (500000 / 912351) := by
    rw [show ((912351 / 500000) : ℝ) = ((500000 / 912351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (348253579 / 200000000) ≤ -Real.log (87649 / 500000) ∧
    -Real.log (87649 / 500000) ≤ (870633949 / 500000000) := by
  have h := checkLog_sound (w := (37351 / 212649)) (n := 12)
    (lo := (70994707 / 200000000)) (hi := (11092923 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87649) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 87649) = 1/(87649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-870633949 / 500000000) (-348253579 / 200000000) (Real.log (87649 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23343269 / 40000000) ≤ -Real.log (1000000 / 1792447) ∧
    -Real.log (1000000 / 1792447) ≤ (291790863 / 500000000) := by
  have h := checkLog_sound (w := (792447 / 2792447)) (n := 12)
    (lo := (23343269 / 40000000)) (hi := (291790863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1792447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1792447 / 1000000) = 1/(1000000 / 1792447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23343269 / 40000000) (291790863 / 500000000) (Real.log (1792447 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1792447 / 1000000) = -Real.log (1000000 / 1792447) := by
    rw [show ((1792447 / 1000000) : ℝ) = ((1000000 / 1792447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1572368549 / 1000000000) ≤ -Real.log (207553 / 1000000) ∧
    -Real.log (207553 / 1000000) ≤ (196546069 / 125000000) := by
  have h := checkLog_sound (w := (42447 / 457553)) (n := 12)
    (lo := (186074189 / 1000000000)) (hi := (18607419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207553) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 207553) = 1/(207553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-196546069 / 125000000) (-1572368549 / 1000000000) (Real.log (207553 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (585733447 / 1000000000) ≤ -Real.log (250000 / 449077) ∧
    -Real.log (250000 / 449077) ≤ (73216681 / 125000000) := by
  have h := checkLog_sound (w := (199077 / 699077)) (n := 12)
    (lo := (585733447 / 1000000000)) (hi := (73216681 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449077 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449077 / 250000) = 1/(250000 / 449077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (585733447 / 1000000000) (73216681 / 125000000) (Real.log (449077 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (449077 / 250000) = -Real.log (250000 / 449077) := by
    rw [show ((449077 / 250000) : ℝ) = ((250000 / 449077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (397786557 / 250000000) ≤ -Real.log (50923 / 250000) ∧
    -Real.log (50923 / 250000) ≤ (1591146231 / 1000000000) := by
  have h := checkLog_sound (w := (11577 / 113423)) (n := 12)
    (lo := (51212967 / 250000000)) (hi := (204851869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50923) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 50923) = 1/(50923 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1591146231 / 1000000000) (-397786557 / 250000000) (Real.log (50923 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (465617073 / 200000000) ≤ -Real.log (500000000000 / 5129140936801) ∧
    -Real.log (500000000000 / 5129140936801) ≤ (2328085369 / 1000000000) := by
  have h := checkLog_sound (w := (1129140936801 / 9129140936801)) (n := 12)
    (lo := (9945753 / 40000000)) (hi := (124321913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5129140936801 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5129140936801 / 4000000000000) = 1/(500000000000 / 5129140936801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (465617073 / 200000000) (2328085369 / 1000000000) (Real.log (5129140936801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5129140936801 / 500000000000) = -Real.log (500000000000 / 5129140936801) := by
    rw [show ((5129140936801 / 500000000000) : ℝ) = ((500000000000 / 5129140936801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (117134229 / 50000000) ≤ -Real.log (125000000000 / 1301142910929) ∧
    -Real.log (125000000000 / 1301142910929) ≤ (292835573 / 125000000) := by
  have h := checkLog_sound (w := (301142910929 / 2301142910929)) (n := 12)
    (lo := (1645269 / 6250000)) (hi := (263243041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301142910929 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1301142910929 / 1000000000000) = 1/(125000000000 / 1301142910929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (117134229 / 50000000) (292835573 / 125000000) (Real.log (1301142910929 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1301142910929 / 125000000000) = -Real.log (125000000000 / 1301142910929) := by
    rw [show ((1301142910929 / 125000000000) : ℝ) = ((125000000000 / 1301142910929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2155950273 / 1000000000) ≤ -Real.log (125000000000 / 1079511618719) ∧
    -Real.log (125000000000 / 1079511618719) ≤ (2155950277 / 1000000000) := by
  have h := checkLog_sound (w := (79511618719 / 2079511618719)) (n := 12)
    (lo := (76508733 / 1000000000)) (hi := (38254367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079511618719 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1079511618719 / 1000000000000) = 1/(125000000000 / 1079511618719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2155950273 / 1000000000) (2155950277 / 1000000000) (Real.log (1079511618719 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1079511618719 / 125000000000) = -Real.log (125000000000 / 1079511618719) := by
    rw [show ((1079511618719 / 125000000000) : ℝ) = ((125000000000 / 1079511618719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (87075187 / 40000000) ≤ -Real.log (125000000000 / 1102343243721) ∧
    -Real.log (125000000000 / 1102343243721) ≤ (2176879679 / 1000000000) := by
  have h := checkLog_sound (w := (102343243721 / 2102343243721)) (n := 12)
    (lo := (19487627 / 200000000)) (hi := (12179767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102343243721 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1102343243721 / 1000000000000) = 1/(125000000000 / 1102343243721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (87075187 / 40000000) (2176879679 / 1000000000) (Real.log (1102343243721 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1102343243721 / 125000000000) = -Real.log (125000000000 / 1102343243721) := by
    rw [show ((1102343243721 / 125000000000) : ℝ) = ((125000000000 / 1102343243721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0215
