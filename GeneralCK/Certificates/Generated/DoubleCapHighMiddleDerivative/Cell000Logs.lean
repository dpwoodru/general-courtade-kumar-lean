import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell000
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (223612191 / 1000000000) ≤ -Real.log (5120 / 6403) ∧
    -Real.log (5120 / 6403) ≤ (6987881 / 31250000) := by
  have h := checkLog_sound (w := (1283 / 11523)) (n := 12)
    (lo := (223612191 / 1000000000)) (hi := (6987881 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6403 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6403 / 5120) = 1/(5120 / 6403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223612191 / 1000000000) (6987881 / 31250000) (Real.log (6403 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6403 / 5120) = -Real.log (5120 / 6403) := by
    rw [show ((6403 / 5120) : ℝ) = ((5120 / 6403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (288463627 / 1000000000) ≤ -Real.log (3837 / 5120) ∧
    -Real.log (3837 / 5120) ≤ (72115907 / 250000000) := by
  have h := checkLog_sound (w := (1283 / 8957)) (n := 12)
    (lo := (288463627 / 1000000000)) (hi := (72115907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3837) = 1/(3837 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72115907 / 250000000) (-288463627 / 1000000000) (Real.log (3837 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223143551 / 1000000000) (1743309 / 7812500) (Real.log (5 / 4)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5 / 4) = -Real.log (4 / 5) := by
    rw [show ((5 / 4) : ℝ) = ((4 / 5) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35960259 / 125000000) ≤ -Real.log (3 / 4) ∧
    -Real.log (3 / 4) ≤ (287682073 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4 / 3) = 1/(3 / 4) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-287682073 / 1000000000) (-35960259 / 125000000) (Real.log (3 / 4)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4079509 / 25000000) ≤ -Real.log (1000000 / 1177249) ∧
    -Real.log (1000000 / 1177249) ≤ (163180361 / 1000000000) := by
  have h := checkLog_sound (w := (177249 / 2177249)) (n := 12)
    (lo := (4079509 / 25000000)) (hi := (163180361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177249 / 1000000) = 1/(1000000 / 1177249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4079509 / 25000000) (163180361 / 1000000000) (Real.log (1177249 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1177249 / 1000000) = -Real.log (1000000 / 1177249) := by
    rw [show ((1177249 / 1000000) : ℝ) = ((1000000 / 1177249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7804067 / 40000000) ≤ -Real.log (822751 / 1000000) ∧
    -Real.log (822751 / 1000000) ≤ (48775419 / 250000000) := by
  have h := checkLog_sound (w := (177249 / 1822751)) (n := 12)
    (lo := (7804067 / 40000000)) (hi := (48775419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822751) = 1/(822751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-48775419 / 250000000) (-7804067 / 40000000) (Real.log (822751 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (163536211 / 1000000000) ≤ -Real.log (250000 / 294417) ∧
    -Real.log (250000 / 294417) ≤ (40884053 / 250000000) := by
  have h := checkLog_sound (w := (44417 / 544417)) (n := 12)
    (lo := (163536211 / 1000000000)) (hi := (40884053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294417 / 250000) = 1/(250000 / 294417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (163536211 / 1000000000) (40884053 / 250000000) (Real.log (294417 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (294417 / 250000) = -Real.log (250000 / 294417) := by
    rw [show ((294417 / 250000) : ℝ) = ((250000 / 294417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3056423 / 15625000) ≤ -Real.log (205583 / 250000) ∧
    -Real.log (205583 / 250000) ≤ (195611073 / 1000000000) := by
  have h := checkLog_sound (w := (44417 / 455583)) (n := 12)
    (lo := (3056423 / 15625000)) (hi := (195611073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205583) = 1/(205583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-195611073 / 1000000000) (-3056423 / 15625000) (Real.log (205583 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59528889 / 500000000) ≤ -Real.log (200000 / 225287) ∧
    -Real.log (200000 / 225287) ≤ (119057779 / 1000000000) := by
  have h := checkLog_sound (w := (25287 / 425287)) (n := 12)
    (lo := (59528889 / 500000000)) (hi := (119057779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225287 / 200000) = 1/(200000 / 225287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59528889 / 500000000) (119057779 / 1000000000) (Real.log (225287 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225287 / 200000) = -Real.log (200000 / 225287) := by
    rw [show ((225287 / 200000) : ℝ) = ((200000 / 225287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67586369 / 500000000) ≤ -Real.log (174713 / 200000) ∧
    -Real.log (174713 / 200000) ≤ (135172739 / 1000000000) := by
  have h := checkLog_sound (w := (25287 / 374713)) (n := 12)
    (lo := (67586369 / 500000000)) (hi := (135172739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174713) = 1/(174713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135172739 / 1000000000) (-67586369 / 500000000) (Real.log (174713 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119327619 / 1000000000) ≤ -Real.log (1000000 / 1126739) ∧
    -Real.log (1000000 / 1126739) ≤ (5966381 / 50000000) := by
  have h := checkLog_sound (w := (126739 / 2126739)) (n := 12)
    (lo := (119327619 / 1000000000)) (hi := (5966381 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126739 / 1000000) = 1/(1000000 / 1126739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119327619 / 1000000000) (5966381 / 50000000) (Real.log (1126739 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1126739 / 1000000) = -Real.log (1000000 / 1126739) := by
    rw [show ((1126739 / 1000000) : ℝ) = ((1000000 / 1126739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (67760399 / 500000000) ≤ -Real.log (873261 / 1000000) ∧
    -Real.log (873261 / 1000000) ≤ (135520799 / 1000000000) := by
  have h := checkLog_sound (w := (126739 / 1873261)) (n := 12)
    (lo := (67760399 / 500000000)) (hi := (135520799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873261) = 1/(873261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-135520799 / 1000000000) (-67760399 / 500000000) (Real.log (873261 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (510825623 / 1000000000) ≤ -Real.log (500000000000 / 833333333333) ∧
    -Real.log (500000000000 / 833333333333) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (333333333333 / 1333333333333)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833333333333 / 500000000000) = 1/(500000000000 / 833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (833333333333 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (833333333333 / 500000000000) = -Real.log (500000000000 / 833333333333) := by
    rw [show ((833333333333 / 500000000000) : ℝ) = ((500000000000 / 833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (512075819 / 1000000000) ≤ -Real.log (500000000000 / 834375814439) ∧
    -Real.log (500000000000 / 834375814439) ≤ (25603791 / 50000000) := by
  have h := checkLog_sound (w := (334375814439 / 1334375814439)) (n := 12)
    (lo := (512075819 / 1000000000)) (hi := (25603791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834375814439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834375814439 / 500000000000) = 1/(500000000000 / 834375814439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (512075819 / 1000000000) (25603791 / 50000000) (Real.log (834375814439 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (834375814439 / 500000000000) = -Real.log (500000000000 / 834375814439) := by
    rw [show ((834375814439 / 500000000000) : ℝ) = ((500000000000 / 834375814439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (89570509 / 250000000) ≤ -Real.log (100000000000 / 143086912079) ∧
    -Real.log (100000000000 / 143086912079) ≤ (358282037 / 1000000000) := by
  have h := checkLog_sound (w := (43086912079 / 243086912079)) (n := 12)
    (lo := (89570509 / 250000000)) (hi := (358282037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143086912079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143086912079 / 100000000000) = 1/(100000000000 / 143086912079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (89570509 / 250000000) (358282037 / 1000000000) (Real.log (143086912079 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (143086912079 / 100000000000) = -Real.log (100000000000 / 143086912079) := by
    rw [show ((143086912079 / 100000000000) : ℝ) = ((100000000000 / 143086912079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (89786821 / 250000000) ≤ -Real.log (250000000000 / 358026928297) ∧
    -Real.log (250000000000 / 358026928297) ≤ (71829457 / 200000000) := by
  have h := checkLog_sound (w := (108026928297 / 608026928297)) (n := 12)
    (lo := (89786821 / 250000000)) (hi := (71829457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358026928297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358026928297 / 250000000000) = 1/(250000000000 / 358026928297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (89786821 / 250000000) (71829457 / 200000000) (Real.log (358026928297 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358026928297 / 250000000000) = -Real.log (250000000000 / 358026928297) := by
    rw [show ((358026928297 / 250000000000) : ℝ) = ((250000000000 / 358026928297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (254230517 / 1000000000) ≤ -Real.log (500000000000 / 644734507449) ∧
    -Real.log (500000000000 / 644734507449) ≤ (127115259 / 500000000) := by
  have h := checkLog_sound (w := (144734507449 / 1144734507449)) (n := 12)
    (lo := (254230517 / 1000000000)) (hi := (127115259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644734507449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644734507449 / 500000000000) = 1/(500000000000 / 644734507449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (254230517 / 1000000000) (127115259 / 500000000) (Real.log (644734507449 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (644734507449 / 500000000000) = -Real.log (500000000000 / 644734507449) := by
    rw [show ((644734507449 / 500000000000) : ℝ) = ((500000000000 / 644734507449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (127424209 / 500000000) ≤ -Real.log (250000000000 / 322566506463) ∧
    -Real.log (250000000000 / 322566506463) ≤ (254848419 / 1000000000) := by
  have h := checkLog_sound (w := (72566506463 / 572566506463)) (n := 12)
    (lo := (127424209 / 500000000)) (hi := (254848419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322566506463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322566506463 / 250000000000) = 1/(250000000000 / 322566506463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (127424209 / 500000000) (254848419 / 1000000000) (Real.log (322566506463 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (322566506463 / 250000000000) = -Real.log (250000000000 / 322566506463) := by
    rw [show ((322566506463 / 250000000000) : ℝ) = ((250000000000 / 322566506463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8096589 / 500000000) ≤ -Real.log (983937225879 / 1000000000000) ∧
    -Real.log (983937225879 / 1000000000000) ≤ (16193179 / 1000000000) := by
  have h := checkLog_sound (w := (16062774121 / 1983937225879)) (n := 12)
    (lo := (8096589 / 500000000)) (hi := (16193179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983937225879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983937225879) = 1/(983937225879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16193179 / 1000000000) (-8096589 / 500000000) (Real.log (983937225879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (201437 / 12500000) ≤ -Real.log (39360567631 / 40000000000) ∧
    -Real.log (39360567631 / 40000000000) ≤ (16114961 / 1000000000) := by
  have h := checkLog_sound (w := (639432369 / 79360567631)) (n := 12)
    (lo := (201437 / 12500000)) (hi := (16114961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39360567631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39360567631) = 1/(39360567631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16114961 / 1000000000) (-201437 / 12500000) (Real.log (39360567631 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell000
