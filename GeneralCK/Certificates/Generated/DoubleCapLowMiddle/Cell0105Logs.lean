import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0105
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

theorem reflection_log_1_neg : (670460123 / 1000000000) ≤ -Real.log (51200 / 100103) ∧
    -Real.log (51200 / 100103) ≤ (167615031 / 250000000) := by
  have h := checkLog_sound (w := (48903 / 151303)) (n := 12)
    (lo := (670460123 / 1000000000)) (hi := (167615031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100103 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100103 / 51200) = 1/(51200 / 100103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (670460123 / 1000000000) (167615031 / 250000000) (Real.log (100103 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100103 / 51200) = -Real.log (51200 / 100103) := by
    rw [show ((100103 / 51200) : ℝ) = ((51200 / 100103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1552067803 / 500000000) ≤ -Real.log (2297 / 51200) ∧
    -Real.log (2297 / 51200) ≤ (3104135611 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2297) = 1/(2297 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3104135611 / 1000000000) (-1552067803 / 500000000) (Real.log (2297 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (670270301 / 1000000000) ≤ -Real.log (12800 / 25021) ∧
    -Real.log (12800 / 25021) ≤ (335135151 / 500000000) := by
  have h := checkLog_sound (w := (12221 / 37821)) (n := 12)
    (lo := (670270301 / 1000000000)) (hi := (335135151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25021 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25021 / 12800) = 1/(12800 / 25021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (670270301 / 1000000000) (335135151 / 500000000) (Real.log (25021 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25021 / 12800) = -Real.log (12800 / 25021) := by
    rw [show ((25021 / 12800) : ℝ) = ((12800 / 25021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (309589797 / 100000000) ≤ -Real.log (579 / 12800) ∧
    -Real.log (579 / 12800) ≤ (123835919 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 579) = 1/(579 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123835919 / 40000000) (-309589797 / 100000000) (Real.log (579 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (80905799 / 125000000) ≤ -Real.log (25600 / 48903) ∧
    -Real.log (25600 / 48903) ≤ (647246393 / 1000000000) := by
  have h := checkLog_sound (w := (23303 / 74503)) (n := 12)
    (lo := (80905799 / 125000000)) (hi := (647246393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48903 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48903 / 25600) = 1/(25600 / 48903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (80905799 / 125000000) (647246393 / 1000000000) (Real.log (48903 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48903 / 25600) = -Real.log (25600 / 48903) := by
    rw [show ((48903 / 25600) : ℝ) = ((25600 / 48903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1205494213 / 500000000) ≤ -Real.log (2297 / 25600) ∧
    -Real.log (2297 / 25600) ≤ (241098843 / 100000000) := by
  have h := checkLog_sound (w := (903 / 5497)) (n := 12)
    (lo := (165773443 / 500000000)) (hi := (331546887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2297) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2297) = 1/(2297 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241098843 / 100000000) (-1205494213 / 500000000) (Real.log (2297 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (646857793 / 1000000000) ≤ -Real.log (6400 / 12221) ∧
    -Real.log (6400 / 12221) ≤ (323428897 / 500000000) := by
  have h := checkLog_sound (w := (5821 / 18621)) (n := 12)
    (lo := (646857793 / 1000000000)) (hi := (323428897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12221 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12221 / 6400) = 1/(6400 / 12221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (646857793 / 1000000000) (323428897 / 500000000) (Real.log (12221 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12221 / 6400) = -Real.log (6400 / 12221) := by
    rw [show ((12221 / 6400) : ℝ) = ((6400 / 12221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (240275079 / 100000000) ≤ -Real.log (579 / 6400) ∧
    -Real.log (579 / 6400) ≤ (1201375397 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 579) = 1/(579 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1201375397 / 500000000) (-240275079 / 100000000) (Real.log (579 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168620007 / 250000000) ≤ -Real.log (250000 / 490753) ∧
    -Real.log (250000 / 490753) ≤ (674480029 / 1000000000) := by
  have h := checkLog_sound (w := (240753 / 740753)) (n := 12)
    (lo := (168620007 / 250000000)) (hi := (674480029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490753 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490753 / 250000) = 1/(250000 / 490753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168620007 / 250000000) (674480029 / 1000000000) (Real.log (490753 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (490753 / 250000) = -Real.log (250000 / 490753) := by
    rw [show ((490753 / 250000) : ℝ) = ((250000 / 490753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3297161741 / 1000000000) ≤ -Real.log (9247 / 250000) ∧
    -Real.log (9247 / 250000) ≤ (1648580873 / 500000000) := by
  have h := checkLog_sound (w := (3189 / 12436)) (n := 12)
    (lo := (524573021 / 1000000000)) (hi := (262286511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9247) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9247) = 1/(9247 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1648580873 / 500000000) (-3297161741 / 1000000000) (Real.log (9247 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42164107 / 62500000) ≤ -Real.log (500000 / 981649) ∧
    -Real.log (500000 / 981649) ≤ (674625713 / 1000000000) := by
  have h := checkLog_sound (w := (481649 / 1481649)) (n := 12)
    (lo := (42164107 / 62500000)) (hi := (674625713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981649 / 500000) = 1/(500000 / 981649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42164107 / 62500000) (674625713 / 1000000000) (Real.log (981649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (981649 / 500000) = -Real.log (500000 / 981649) := by
    rw [show ((981649 / 500000) : ℝ) = ((500000 / 981649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3304924027 / 1000000000) ≤ -Real.log (18351 / 500000) ∧
    -Real.log (18351 / 500000) ≤ (25819719 / 7812500) := by
  have h := checkLog_sound (w := (12899 / 49601)) (n := 12)
    (lo := (532335307 / 1000000000)) (hi := (133083827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18351) = 1/(18351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25819719 / 7812500) (-3304924027 / 1000000000) (Real.log (18351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6742849 / 10000000) ≤ -Real.log (1000000 / 1962629) ∧
    -Real.log (1000000 / 1962629) ≤ (674284901 / 1000000000) := by
  have h := checkLog_sound (w := (962629 / 2962629)) (n := 12)
    (lo := (6742849 / 10000000)) (hi := (674284901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962629 / 1000000) = 1/(1000000 / 1962629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6742849 / 10000000) (674284901 / 1000000000) (Real.log (1962629 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962629 / 1000000) = -Real.log (1000000 / 1962629) := by
    rw [show ((1962629 / 1000000) : ℝ) = ((1000000 / 1962629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1643430137 / 500000000) ≤ -Real.log (37371 / 1000000) ∧
    -Real.log (37371 / 1000000) ≤ (3286860279 / 1000000000) := by
  have h := checkLog_sound (w := (25129 / 99871)) (n := 12)
    (lo := (257135777 / 500000000)) (hi := (102854311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37371) = 1/(37371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3286860279 / 1000000000) (-1643430137 / 500000000) (Real.log (37371 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674434179 / 1000000000) ≤ -Real.log (500000 / 981461) ∧
    -Real.log (500000 / 981461) ≤ (33721709 / 50000000) := by
  have h := checkLog_sound (w := (481461 / 1481461)) (n := 12)
    (lo := (674434179 / 1000000000)) (hi := (33721709 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981461 / 500000) = 1/(500000 / 981461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674434179 / 1000000000) (33721709 / 50000000) (Real.log (981461 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981461 / 500000) = -Real.log (500000 / 981461) := by
    rw [show ((981461 / 500000) : ℝ) = ((500000 / 981461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1647365737 / 500000000) ≤ -Real.log (18539 / 500000) ∧
    -Real.log (18539 / 500000) ≤ (3294731479 / 1000000000) := by
  have h := checkLog_sound (w := (12711 / 49789)) (n := 12)
    (lo := (261071377 / 500000000)) (hi := (104428551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18539) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18539) = 1/(18539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3294731479 / 1000000000) (-1647365737 / 500000000) (Real.log (18539 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (496455221 / 125000000) ≤ -Real.log (5000000000 / 265357953931) ∧
    -Real.log (5000000000 / 265357953931) ≤ (1985820887 / 500000000) := by
  have h := checkLog_sound (w := (105357953931 / 425357953931)) (n := 12)
    (lo := (126476467 / 250000000)) (hi := (505905869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265357953931 / 160000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(265357953931 / 160000000000) = 1/(5000000000 / 265357953931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (496455221 / 125000000) (1985820887 / 500000000) (Real.log (265357953931 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (265357953931 / 5000000000) = -Real.log (5000000000 / 265357953931) := by
    rw [show ((265357953931 / 5000000000) : ℝ) = ((5000000000 / 265357953931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1989774869 / 500000000) ≤ -Real.log (500000000000 / 26746471581931) ∧
    -Real.log (500000000000 / 26746471581931) ≤ (248721859 / 62500000) := by
  have h := checkLog_sound (w := (10746471581931 / 42746471581931)) (n := 12)
    (lo := (256906919 / 500000000)) (hi := (513813839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26746471581931 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26746471581931 / 16000000000000) = 1/(500000000000 / 26746471581931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1989774869 / 500000000) (248721859 / 62500000) (Real.log (26746471581931 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26746471581931 / 500000000000) = -Real.log (500000000000 / 26746471581931) := by
    rw [show ((26746471581931 / 500000000000) : ℝ) = ((500000000000 / 26746471581931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1980572587 / 500000000) ≤ -Real.log (500000000000 / 26258716651949) ∧
    -Real.log (500000000000 / 26258716651949) ≤ (198057259 / 50000000) := by
  have h := checkLog_sound (w := (10258716651949 / 42258716651949)) (n := 12)
    (lo := (247704637 / 500000000)) (hi := (19816371 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26258716651949 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26258716651949 / 16000000000000) = 1/(500000000000 / 26258716651949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1980572587 / 500000000) (198057259 / 50000000) (Real.log (26258716651949 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26258716651949 / 500000000000) = -Real.log (500000000000 / 26258716651949) := by
    rw [show ((26258716651949 / 500000000000) : ℝ) = ((500000000000 / 26258716651949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3969165653 / 1000000000) ≤ -Real.log (100000000000 / 5294034198177) ∧
    -Real.log (100000000000 / 5294034198177) ≤ (3969165659 / 1000000000) := by
  have h := checkLog_sound (w := (2094034198177 / 8494034198177)) (n := 12)
    (lo := (503429753 / 1000000000)) (hi := (251714877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5294034198177 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5294034198177 / 3200000000000) = 1/(100000000000 / 5294034198177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3969165653 / 1000000000) (3969165659 / 1000000000) (Real.log (5294034198177 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5294034198177 / 100000000000) = -Real.log (100000000000 / 5294034198177) := by
    rw [show ((5294034198177 / 100000000000) : ℝ) = ((100000000000 / 5294034198177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0105
