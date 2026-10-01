import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell212
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

theorem reflection_log_1_neg : (12732467 / 40000000) ≤ -Real.log (5120 / 7039) ∧
    -Real.log (5120 / 7039) ≤ (79577919 / 250000000) := by
  have h := checkLog_sound (w := (1919 / 12159)) (n := 12)
    (lo := (12732467 / 40000000)) (hi := (79577919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7039 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7039 / 5120) = 1/(5120 / 7039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12732467 / 40000000) (79577919 / 250000000) (Real.log (7039 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7039 / 5120) = -Real.log (5120 / 7039) := by
    rw [show ((7039 / 5120) : ℝ) = ((5120 / 7039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (234845589 / 500000000) ≤ -Real.log (3201 / 5120) ∧
    -Real.log (3201 / 5120) ≤ (469691179 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 8321)) (n := 12)
    (lo := (234845589 / 500000000)) (hi := (469691179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3201) = 1/(3201 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-469691179 / 1000000000) (-234845589 / 500000000) (Real.log (3201 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (317885387 / 1000000000) ≤ -Real.log (1280 / 1759) ∧
    -Real.log (1280 / 1759) ≤ (79471347 / 250000000) := by
  have h := checkLog_sound (w := (479 / 3039)) (n := 12)
    (lo := (317885387 / 1000000000)) (hi := (79471347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759 / 1280) = 1/(1280 / 1759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (317885387 / 1000000000) (79471347 / 250000000) (Real.log (1759 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1759 / 1280) = -Real.log (1280 / 1759) := by
    rw [show ((1759 / 1280) : ℝ) = ((1280 / 1759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (468754409 / 1000000000) ≤ -Real.log (801 / 1280) ∧
    -Real.log (801 / 1280) ≤ (46875441 / 100000000) := by
  have h := checkLog_sound (w := (479 / 2081)) (n := 12)
    (lo := (468754409 / 1000000000)) (hi := (46875441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 801) = 1/(801 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46875441 / 100000000) (-468754409 / 1000000000) (Real.log (801 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47212429 / 200000000) ≤ -Real.log (1000000 / 1266253) ∧
    -Real.log (1000000 / 1266253) ≤ (118031073 / 500000000) := by
  have h := checkLog_sound (w := (266253 / 2266253)) (n := 12)
    (lo := (47212429 / 200000000)) (hi := (118031073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266253 / 1000000) = 1/(1000000 / 1266253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47212429 / 200000000) (118031073 / 500000000) (Real.log (1266253 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1266253 / 1000000) = -Real.log (1000000 / 1266253) := by
    rw [show ((1266253 / 1000000) : ℝ) = ((1000000 / 1266253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77397749 / 250000000) ≤ -Real.log (733747 / 1000000) ∧
    -Real.log (733747 / 1000000) ≤ (309590997 / 1000000000) := by
  have h := checkLog_sound (w := (266253 / 1733747)) (n := 12)
    (lo := (77397749 / 250000000)) (hi := (309590997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733747) = 1/(733747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-309590997 / 1000000000) (-77397749 / 250000000) (Real.log (733747 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (118198073 / 500000000) ≤ -Real.log (250000 / 316669) ∧
    -Real.log (250000 / 316669) ≤ (236396147 / 1000000000) := by
  have h := checkLog_sound (w := (66669 / 566669)) (n := 12)
    (lo := (118198073 / 500000000)) (hi := (236396147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316669 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316669 / 250000) = 1/(250000 / 316669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (118198073 / 500000000) (236396147 / 1000000000) (Real.log (316669 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (316669 / 250000) = -Real.log (250000 / 316669) := by
    rw [show ((316669 / 250000) : ℝ) = ((250000 / 316669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62033531 / 200000000) ≤ -Real.log (183331 / 250000) ∧
    -Real.log (183331 / 250000) ≤ (38770957 / 125000000) := by
  have h := checkLog_sound (w := (66669 / 433331)) (n := 12)
    (lo := (62033531 / 200000000)) (hi := (38770957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183331) = 1/(183331 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38770957 / 125000000) (-62033531 / 200000000) (Real.log (183331 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1405329 / 8000000) ≤ -Real.log (25000 / 29801) ∧
    -Real.log (25000 / 29801) ≤ (87833063 / 500000000) := by
  have h := checkLog_sound (w := (4801 / 54801)) (n := 12)
    (lo := (1405329 / 8000000)) (hi := (87833063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29801 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29801 / 25000) = 1/(25000 / 29801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1405329 / 8000000) (87833063 / 500000000) (Real.log (29801 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29801 / 25000) = -Real.log (25000 / 29801) := by
    rw [show ((29801 / 25000) : ℝ) = ((25000 / 29801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (106621363 / 500000000) ≤ -Real.log (20199 / 25000) ∧
    -Real.log (20199 / 25000) ≤ (213242727 / 1000000000) := by
  have h := checkLog_sound (w := (4801 / 45199)) (n := 12)
    (lo := (106621363 / 500000000)) (hi := (213242727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20199) = 1/(20199 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-213242727 / 1000000000) (-106621363 / 500000000) (Real.log (20199 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175932859 / 1000000000) ≤ -Real.log (500000 / 596179) ∧
    -Real.log (500000 / 596179) ≤ (8796643 / 50000000) := by
  have h := checkLog_sound (w := (96179 / 1096179)) (n := 12)
    (lo := (175932859 / 1000000000)) (hi := (8796643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596179 / 500000) = 1/(500000 / 596179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175932859 / 1000000000) (8796643 / 50000000) (Real.log (596179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (596179 / 500000) = -Real.log (500000 / 596179) := by
    rw [show ((596179 / 500000) : ℝ) = ((500000 / 596179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (213636387 / 1000000000) ≤ -Real.log (403821 / 500000) ∧
    -Real.log (403821 / 500000) ≤ (53409097 / 250000000) := by
  have h := checkLog_sound (w := (96179 / 903821)) (n := 12)
    (lo := (213636387 / 1000000000)) (hi := (53409097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403821) = 1/(403821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53409097 / 250000000) (-213636387 / 1000000000) (Real.log (403821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (786639797 / 1000000000) ≤ -Real.log (250000000000 / 549001248439) ∧
    -Real.log (250000000000 / 549001248439) ≤ (786639799 / 1000000000) := by
  have h := checkLog_sound (w := (49001248439 / 1049001248439)) (n := 12)
    (lo := (93492617 / 1000000000)) (hi := (46746309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549001248439 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(549001248439 / 500000000000) = 1/(250000000000 / 549001248439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (786639797 / 1000000000) (786639799 / 1000000000) (Real.log (549001248439 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (549001248439 / 250000000000) = -Real.log (250000000000 / 549001248439) := by
    rw [show ((549001248439 / 250000000000) : ℝ) = ((250000000000 / 549001248439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (788002853 / 1000000000) ≤ -Real.log (250000000000 / 549750078101) ∧
    -Real.log (250000000000 / 549750078101) ≤ (157600571 / 200000000) := by
  have h := checkLog_sound (w := (49750078101 / 1049750078101)) (n := 12)
    (lo := (94855673 / 1000000000)) (hi := (47427837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549750078101 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(549750078101 / 500000000000) = 1/(250000000000 / 549750078101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (788002853 / 1000000000) (157600571 / 200000000) (Real.log (549750078101 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (549750078101 / 250000000000) = -Real.log (250000000000 / 549750078101) := by
    rw [show ((549750078101 / 250000000000) : ℝ) = ((250000000000 / 549750078101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (272826571 / 500000000) ≤ -Real.log (250000000000 / 431433791211) ∧
    -Real.log (250000000000 / 431433791211) ≤ (545653143 / 1000000000) := by
  have h := checkLog_sound (w := (181433791211 / 681433791211)) (n := 12)
    (lo := (272826571 / 500000000)) (hi := (545653143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431433791211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431433791211 / 250000000000) = 1/(250000000000 / 431433791211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (272826571 / 500000000) (545653143 / 1000000000) (Real.log (431433791211 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (431433791211 / 250000000000) = -Real.log (250000000000 / 431433791211) := by
    rw [show ((431433791211 / 250000000000) : ℝ) = ((250000000000 / 431433791211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (273281901 / 500000000) ≤ -Real.log (50000000000 / 86365371923) ∧
    -Real.log (50000000000 / 86365371923) ≤ (546563803 / 1000000000) := by
  have h := checkLog_sound (w := (36365371923 / 136365371923)) (n := 12)
    (lo := (273281901 / 500000000)) (hi := (546563803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86365371923 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86365371923 / 50000000000) = 1/(50000000000 / 86365371923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (273281901 / 500000000) (546563803 / 1000000000) (Real.log (86365371923 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (86365371923 / 50000000000) = -Real.log (50000000000 / 86365371923) := by
    rw [show ((86365371923 / 50000000000) : ℝ) = ((50000000000 / 86365371923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (388908851 / 1000000000) ≤ -Real.log (62500000000 / 92210629239) ∧
    -Real.log (62500000000 / 92210629239) ≤ (97227213 / 250000000) := by
  have h := checkLog_sound (w := (29710629239 / 154710629239)) (n := 12)
    (lo := (388908851 / 1000000000)) (hi := (97227213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92210629239 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92210629239 / 62500000000) = 1/(62500000000 / 92210629239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (388908851 / 1000000000) (97227213 / 250000000) (Real.log (92210629239 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (92210629239 / 62500000000) = -Real.log (62500000000 / 92210629239) := by
    rw [show ((92210629239 / 62500000000) : ℝ) = ((62500000000 / 92210629239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (389569247 / 1000000000) ≤ -Real.log (100000000000 / 147634471709) ∧
    -Real.log (100000000000 / 147634471709) ≤ (12174039 / 31250000) := by
  have h := checkLog_sound (w := (47634471709 / 247634471709)) (n := 12)
    (lo := (389569247 / 1000000000)) (hi := (12174039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147634471709 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147634471709 / 100000000000) = 1/(100000000000 / 147634471709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (389569247 / 1000000000) (12174039 / 31250000) (Real.log (147634471709 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (147634471709 / 100000000000) = -Real.log (100000000000 / 147634471709) := by
    rw [show ((147634471709 / 100000000000) : ℝ) = ((100000000000 / 147634471709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4712941 / 125000000) ≤ -Real.log (240749599959 / 250000000000) ∧
    -Real.log (240749599959 / 250000000000) ≤ (37703529 / 1000000000) := by
  have h := checkLog_sound (w := (9250400041 / 490749599959)) (n := 12)
    (lo := (4712941 / 125000000)) (hi := (37703529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240749599959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240749599959) = 1/(240749599959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37703529 / 1000000000) (-4712941 / 125000000) (Real.log (240749599959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37576601 / 1000000000) ≤ -Real.log (601950399 / 625000000) ∧
    -Real.log (601950399 / 625000000) ≤ (18788301 / 500000000) := by
  have h := checkLog_sound (w := (23049601 / 1226950399)) (n := 12)
    (lo := (37576601 / 1000000000)) (hi := (18788301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 601950399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 601950399) = 1/(601950399 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18788301 / 500000000) (-37576601 / 1000000000) (Real.log (601950399 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell212
