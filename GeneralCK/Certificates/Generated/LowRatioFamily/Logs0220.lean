import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14080_neg : (97943621 / 250000000) ≤ -Real.log (250000 / 369901) ∧
    -Real.log (250000 / 369901) ≤ (78354897 / 200000000) := by
  have h := checkLog_sound (w := (119901 / 619901)) (n := 12)
    (lo := (97943621 / 250000000)) (hi := (78354897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369901 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369901 / 250000) = 1/(250000 / 369901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14080 : Bounds (97943621 / 250000000) (78354897 / 200000000) (Real.log (369901 / 250000)) := by
  have h := reflection_log_14080_neg
  have he : Real.log (369901 / 250000) = -Real.log (250000 / 369901) := by
    rw [show ((369901 / 250000) : ℝ) = ((250000 / 369901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14081_neg : (326582609 / 500000000) ≤ -Real.log (130099 / 250000) ∧
    -Real.log (130099 / 250000) ≤ (653165219 / 1000000000) := by
  have h := checkLog_sound (w := (119901 / 380099)) (n := 12)
    (lo := (326582609 / 500000000)) (hi := (653165219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130099) = 1/(130099 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14081 : Bounds (-653165219 / 1000000000) (-326582609 / 500000000) (Real.log (130099 / 250000)) := by
  have h := reflection_log_14081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14082_neg : (393854633 / 1000000000) ≤ -Real.log (200000 / 296537) ∧
    -Real.log (200000 / 296537) ≤ (196927317 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 496537)) (n := 12)
    (lo := (393854633 / 1000000000)) (hi := (196927317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296537 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296537 / 200000) = 1/(200000 / 296537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14082 : Bounds (393854633 / 1000000000) (196927317 / 500000000) (Real.log (296537 / 200000)) := by
  have h := reflection_log_14082_neg
  have he : Real.log (296537 / 200000) = -Real.log (200000 / 296537) := by
    rw [show ((296537 / 200000) : ℝ) = ((200000 / 296537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14083_neg : (131820661 / 200000000) ≤ -Real.log (103463 / 200000) ∧
    -Real.log (103463 / 200000) ≤ (329551653 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 303463)) (n := 12)
    (lo := (131820661 / 200000000)) (hi := (329551653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103463) = 1/(103463 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14083 : Bounds (-329551653 / 500000000) (-131820661 / 200000000) (Real.log (103463 / 200000)) := by
  have h := reflection_log_14083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14084_neg : (8289021 / 31250000) ≤ -Real.log (30680607631 / 40000000000) ∧
    -Real.log (30680607631 / 40000000000) ≤ (265248673 / 1000000000) := by
  have h := checkLog_sound (w := (9319392369 / 70680607631)) (n := 12)
    (lo := (8289021 / 31250000)) (hi := (265248673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30680607631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30680607631) = 1/(30680607631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14084 : Bounds (-265248673 / 1000000000) (-8289021 / 31250000) (Real.log (30680607631 / 40000000000)) := by
  have h := reflection_log_14084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14085_neg : (130695367 / 500000000) ≤ -Real.log (48123750199 / 62500000000) ∧
    -Real.log (48123750199 / 62500000000) ≤ (52278147 / 200000000) := by
  have h := checkLog_sound (w := (14376249801 / 110623750199)) (n := 12)
    (lo := (130695367 / 500000000)) (hi := (52278147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 48123750199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 48123750199) = 1/(48123750199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14085 : Bounds (-52278147 / 200000000) (-130695367 / 500000000) (Real.log (48123750199 / 62500000000)) := by
  have h := reflection_log_14085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14086_neg : (522469851 / 500000000) ≤ -Real.log (500000000000 / 1421613540457) ∧
    -Real.log (500000000000 / 1421613540457) ≤ (130617463 / 125000000) := by
  have h := checkLog_sound (w := (421613540457 / 2421613540457)) (n := 12)
    (lo := (175896261 / 500000000)) (hi := (351792523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421613540457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1421613540457 / 1000000000000) = 1/(500000000000 / 1421613540457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14086 : Bounds (522469851 / 500000000) (130617463 / 125000000) (Real.log (1421613540457 / 500000000000)) := by
  have h := reflection_log_14086_neg
  have he : Real.log (1421613540457 / 500000000000) = -Real.log (500000000000 / 1421613540457) := by
    rw [show ((1421613540457 / 500000000000) : ℝ) = ((500000000000 / 1421613540457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14087_neg : (526478969 / 500000000) ≤ -Real.log (500000000000 / 1433058194717) ∧
    -Real.log (500000000000 / 1433058194717) ≤ (52647897 / 50000000) := by
  have h := checkLog_sound (w := (433058194717 / 2433058194717)) (n := 12)
    (lo := (179905379 / 500000000)) (hi := (359810759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433058194717 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1433058194717 / 1000000000000) = 1/(500000000000 / 1433058194717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14087 : Bounds (526478969 / 500000000) (52647897 / 50000000) (Real.log (1433058194717 / 500000000000)) := by
  have h := reflection_log_14087_neg
  have he : Real.log (1433058194717 / 500000000000) = -Real.log (500000000000 / 1433058194717) := by
    rw [show ((1433058194717 / 500000000000) : ℝ) = ((500000000000 / 1433058194717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14088_neg : (29464237 / 12500000) ≤ -Real.log (500000000000 / 5280346820809) ∧
    -Real.log (500000000000 / 5280346820809) ≤ (589284741 / 250000000) := by
  have h := checkLog_sound (w := (1280346820809 / 9280346820809)) (n := 12)
    (lo := (13884871 / 50000000)) (hi := (277697421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5280346820809 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5280346820809 / 4000000000000) = 1/(500000000000 / 5280346820809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14088 : Bounds (29464237 / 12500000) (589284741 / 250000000) (Real.log (5280346820809 / 500000000000)) := by
  have h := reflection_log_14088_neg
  have he : Real.log (5280346820809 / 500000000000) = -Real.log (500000000000 / 5280346820809) := by
    rw [show ((5280346820809 / 500000000000) : ℝ) = ((500000000000 / 5280346820809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14089_neg : (2376272807 / 1000000000) ≤ -Real.log (500000000000 / 5382352941177) ∧
    -Real.log (500000000000 / 5382352941177) ≤ (2376272811 / 1000000000) := by
  have h := checkLog_sound (w := (1382352941177 / 9382352941177)) (n := 12)
    (lo := (296831267 / 1000000000)) (hi := (74207817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5382352941177 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5382352941177 / 4000000000000) = 1/(500000000000 / 5382352941177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14089 : Bounds (2376272807 / 1000000000) (2376272811 / 1000000000) (Real.log (5382352941177 / 500000000000)) := by
  have h := reflection_log_14089_neg
  have he : Real.log (5382352941177 / 500000000000) = -Real.log (500000000000 / 5382352941177) := by
    rw [show ((5382352941177 / 500000000000) : ℝ) = ((500000000000 / 5382352941177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14090_neg : (37872123 / 62500000) ≤ -Real.log (1000 / 1833) ∧
    -Real.log (1000 / 1833) ≤ (605953969 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 2833)) (n := 12)
    (lo := (37872123 / 62500000)) (hi := (605953969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1000) = 1/(1000 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14090 : Bounds (37872123 / 62500000) (605953969 / 1000000000) (Real.log (1833 / 1000)) := by
  have h := reflection_log_14090_neg
  have he : Real.log (1833 / 1000) = -Real.log (1000 / 1833) := by
    rw [show ((1833 / 1000) : ℝ) = ((1000 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14091_neg : (357952293 / 200000000) ≤ -Real.log (167 / 1000) ∧
    -Real.log (167 / 1000) ≤ (447440367 / 250000000) := by
  have h := checkLog_sound (w := (83 / 417)) (n := 12)
    (lo := (80693421 / 200000000)) (hi := (201733553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 167) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 167) = 1/(167 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14091 : Bounds (-447440367 / 250000000) (-357952293 / 200000000) (Real.log (167 / 1000)) := by
  have h := reflection_log_14091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14092_neg : (832653 / 1000000000) ≤ -Real.log (1000000 / 1000833) ∧
    -Real.log (1000000 / 1000833) ≤ (416327 / 500000000) := by
  have h := checkLog_sound (w := (833 / 2000833)) (n := 12)
    (lo := (832653 / 1000000000)) (hi := (416327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000833 / 1000000) = 1/(1000000 / 1000833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14092 : Bounds (832653 / 1000000000) (416327 / 500000000) (Real.log (1000833 / 1000000)) := by
  have h := reflection_log_14092_neg
  have he : Real.log (1000833 / 1000000) = -Real.log (1000000 / 1000833) := by
    rw [show ((1000833 / 1000000) : ℝ) = ((1000000 / 1000833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14093_neg : (833347 / 1000000000) ≤ -Real.log (999167 / 1000000) ∧
    -Real.log (999167 / 1000000) ≤ (208337 / 250000000) := by
  have h := checkLog_sound (w := (833 / 1999167)) (n := 12)
    (lo := (833347 / 1000000000)) (hi := (208337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999167) = 1/(999167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14093 : Bounds (-208337 / 250000000) (-833347 / 1000000000) (Real.log (999167 / 1000000)) := by
  have h := reflection_log_14093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14094_neg : (49175331 / 125000000) ≤ -Real.log (200000 / 296403) ∧
    -Real.log (200000 / 296403) ≤ (393402649 / 1000000000) := by
  have h := checkLog_sound (w := (96403 / 496403)) (n := 12)
    (lo := (49175331 / 125000000)) (hi := (393402649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296403 / 200000) = 1/(200000 / 296403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14094 : Bounds (49175331 / 125000000) (393402649 / 1000000000) (Real.log (296403 / 200000)) := by
  have h := reflection_log_14094_neg
  have he : Real.log (296403 / 200000) = -Real.log (200000 / 296403) := by
    rw [show ((296403 / 200000) : ℝ) = ((200000 / 296403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14095_neg : (328904497 / 500000000) ≤ -Real.log (103597 / 200000) ∧
    -Real.log (103597 / 200000) ≤ (131561799 / 200000000) := by
  have h := checkLog_sound (w := (96403 / 303597)) (n := 12)
    (lo := (328904497 / 500000000)) (hi := (131561799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103597) = 1/(103597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14095 : Bounds (-131561799 / 200000000) (-328904497 / 500000000) (Real.log (103597 / 200000)) := by
  have h := reflection_log_14095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14096_neg : (39548817 / 100000000) ≤ -Real.log (1000000 / 1485109) ∧
    -Real.log (1000000 / 1485109) ≤ (395488171 / 1000000000) := by
  have h := checkLog_sound (w := (485109 / 2485109)) (n := 12)
    (lo := (39548817 / 100000000)) (hi := (395488171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1485109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1485109 / 1000000) = 1/(1000000 / 1485109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14096 : Bounds (39548817 / 100000000) (395488171 / 1000000000) (Real.log (1485109 / 1000000)) := by
  have h := reflection_log_14096_neg
  have he : Real.log (1485109 / 1000000) = -Real.log (1000000 / 1485109) := by
    rw [show ((1485109 / 1000000) : ℝ) = ((1000000 / 1485109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14097_neg : (663800051 / 1000000000) ≤ -Real.log (514891 / 1000000) ∧
    -Real.log (514891 / 1000000) ≤ (165950013 / 250000000) := by
  have h := checkLog_sound (w := (485109 / 1514891)) (n := 12)
    (lo := (663800051 / 1000000000)) (hi := (165950013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 514891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 514891) = 1/(514891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14097 : Bounds (-165950013 / 250000000) (-663800051 / 1000000000) (Real.log (514891 / 1000000)) := by
  have h := reflection_log_14097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14098_neg : (6707797 / 25000000) ≤ -Real.log (764669258119 / 1000000000000) ∧
    -Real.log (764669258119 / 1000000000000) ≤ (268311881 / 1000000000) := by
  have h := checkLog_sound (w := (235330741881 / 1764669258119)) (n := 12)
    (lo := (6707797 / 25000000)) (hi := (268311881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 764669258119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 764669258119) = 1/(764669258119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14098 : Bounds (-268311881 / 1000000000) (-6707797 / 25000000) (Real.log (764669258119 / 1000000000000)) := by
  have h := reflection_log_14098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14099_neg : (132203173 / 500000000) ≤ -Real.log (30706461591 / 40000000000) ∧
    -Real.log (30706461591 / 40000000000) ≤ (264406347 / 1000000000) := by
  have h := checkLog_sound (w := (9293538409 / 70706461591)) (n := 12)
    (lo := (132203173 / 500000000)) (hi := (264406347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30706461591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30706461591) = 1/(30706461591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14099 : Bounds (-264406347 / 1000000000) (-132203173 / 500000000) (Real.log (30706461591 / 40000000000)) := by
  have h := reflection_log_14099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14100_neg : (525605821 / 500000000) ≤ -Real.log (250000000000 / 715278917343) ∧
    -Real.log (250000000000 / 715278917343) ≤ (262802911 / 250000000) := by
  have h := checkLog_sound (w := (215278917343 / 1215278917343)) (n := 12)
    (lo := (179032231 / 500000000)) (hi := (358064463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715278917343 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(715278917343 / 500000000000) = 1/(250000000000 / 715278917343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14100 : Bounds (525605821 / 500000000) (262802911 / 250000000) (Real.log (715278917343 / 250000000000)) := by
  have h := reflection_log_14100_neg
  have he : Real.log (715278917343 / 250000000000) = -Real.log (250000000000 / 715278917343) := by
    rw [show ((715278917343 / 250000000000) : ℝ) = ((250000000000 / 715278917343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14101_neg : (52964411 / 50000000) ≤ -Real.log (500000000000 / 1442158631633) ∧
    -Real.log (500000000000 / 1442158631633) ≤ (529644111 / 500000000) := by
  have h := checkLog_sound (w := (442158631633 / 2442158631633)) (n := 12)
    (lo := (4576763 / 12500000)) (hi := (366141041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442158631633 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1442158631633 / 1000000000000) = 1/(500000000000 / 1442158631633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14101 : Bounds (52964411 / 50000000) (529644111 / 500000000) (Real.log (1442158631633 / 500000000000)) := by
  have h := reflection_log_14101_neg
  have he : Real.log (1442158631633 / 500000000000) = -Real.log (500000000000 / 1442158631633) := by
    rw [show ((1442158631633 / 500000000000) : ℝ) = ((500000000000 / 1442158631633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14102_neg : (2376272807 / 1000000000) ≤ -Real.log (62500000000 / 672794117647) ∧
    -Real.log (62500000000 / 672794117647) ≤ (2376272811 / 1000000000) := by
  have h := checkLog_sound (w := (172794117647 / 1172794117647)) (n := 12)
    (lo := (296831267 / 1000000000)) (hi := (74207817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672794117647 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(672794117647 / 500000000000) = 1/(62500000000 / 672794117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14102 : Bounds (2376272807 / 1000000000) (2376272811 / 1000000000) (Real.log (672794117647 / 62500000000)) := by
  have h := reflection_log_14102_neg
  have he : Real.log (672794117647 / 62500000000) = -Real.log (62500000000 / 672794117647) := by
    rw [show ((672794117647 / 62500000000) : ℝ) = ((62500000000 / 672794117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14103_neg : (2395715433 / 1000000000) ≤ -Real.log (15625000000 / 171500748503) ∧
    -Real.log (15625000000 / 171500748503) ≤ (2395715437 / 1000000000) := by
  have h := checkLog_sound (w := (46500748503 / 296500748503)) (n := 12)
    (lo := (316273893 / 1000000000)) (hi := (158136947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171500748503 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(171500748503 / 125000000000) = 1/(15625000000 / 171500748503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14103 : Bounds (2395715433 / 1000000000) (2395715437 / 1000000000) (Real.log (171500748503 / 15625000000)) := by
  have h := reflection_log_14103_neg
  have he : Real.log (171500748503 / 15625000000) = -Real.log (15625000000 / 171500748503) := by
    rw [show ((171500748503 / 15625000000) : ℝ) = ((15625000000 / 171500748503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14104_neg : (151897323 / 250000000) ≤ -Real.log (250 / 459) ∧
    -Real.log (250 / 459) ≤ (607589293 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 709)) (n := 12)
    (lo := (151897323 / 250000000)) (hi := (607589293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459 / 250) = 1/(250 / 459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14104 : Bounds (151897323 / 250000000) (607589293 / 1000000000) (Real.log (459 / 250)) := by
  have h := reflection_log_14104_neg
  have he : Real.log (459 / 250) = -Real.log (250 / 459) := by
    rw [show ((459 / 250) : ℝ) = ((250 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14105_neg : (36157777 / 20000000) ≤ -Real.log (41 / 250) ∧
    -Real.log (41 / 250) ≤ (1807888853 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 207)) (n := 12)
    (lo := (42159449 / 100000000)) (hi := (421594491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 82) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 82) = 1/(41 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14105 : Bounds (-1807888853 / 1000000000) (-36157777 / 20000000) (Real.log (41 / 250)) := by
  have h := reflection_log_14105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14106_neg : (16713 / 20000000) ≤ -Real.log (250000 / 250209) ∧
    -Real.log (250000 / 250209) ≤ (835651 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 500209)) (n := 12)
    (lo := (16713 / 20000000)) (hi := (835651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250209 / 250000) = 1/(250000 / 250209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14106 : Bounds (16713 / 20000000) (835651 / 1000000000) (Real.log (250209 / 250000)) := by
  have h := reflection_log_14106_neg
  have he : Real.log (250209 / 250000) = -Real.log (250000 / 250209) := by
    rw [show ((250209 / 250000) : ℝ) = ((250000 / 250209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14107_neg : (836349 / 1000000000) ≤ -Real.log (249791 / 250000) ∧
    -Real.log (249791 / 250000) ≤ (16727 / 20000000) := by
  have h := checkLog_sound (w := (209 / 499791)) (n := 12)
    (lo := (836349 / 1000000000)) (hi := (16727 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249791) = 1/(249791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14107 : Bounds (-16727 / 20000000) (-836349 / 1000000000) (Real.log (249791 / 250000)) := by
  have h := reflection_log_14107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14108_neg : (395036923 / 1000000000) ≤ -Real.log (1000000 / 1484439) ∧
    -Real.log (1000000 / 1484439) ≤ (98759231 / 250000000) := by
  have h := checkLog_sound (w := (484439 / 2484439)) (n := 12)
    (lo := (395036923 / 1000000000)) (hi := (98759231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1484439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1484439 / 1000000) = 1/(1000000 / 1484439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14108 : Bounds (395036923 / 1000000000) (98759231 / 250000000) (Real.log (1484439 / 1000000)) := by
  have h := reflection_log_14108_neg
  have he : Real.log (1484439 / 1000000) = -Real.log (1000000 / 1484439) := by
    rw [show ((1484439 / 1000000) : ℝ) = ((1000000 / 1484439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14109_neg : (13249993 / 20000000) ≤ -Real.log (515561 / 1000000) ∧
    -Real.log (515561 / 1000000) ≤ (662499651 / 1000000000) := by
  have h := checkLog_sound (w := (484439 / 1515561)) (n := 12)
    (lo := (13249993 / 20000000)) (hi := (662499651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 515561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 515561) = 1/(515561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14109 : Bounds (-662499651 / 1000000000) (-13249993 / 20000000) (Real.log (515561 / 1000000)) := by
  have h := reflection_log_14109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14110_neg : (198563891 / 500000000) ≤ -Real.log (500000 / 743773) ∧
    -Real.log (500000 / 743773) ≤ (397127783 / 1000000000) := by
  have h := checkLog_sound (w := (243773 / 1243773)) (n := 12)
    (lo := (198563891 / 500000000)) (hi := (397127783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743773 / 500000) = 1/(500000 / 743773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14110 : Bounds (198563891 / 500000000) (397127783 / 1000000000) (Real.log (743773 / 500000)) := by
  have h := reflection_log_14110_neg
  have he : Real.log (743773 / 500000) = -Real.log (500000 / 743773) := by
    rw [show ((743773 / 500000) : ℝ) = ((500000 / 743773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14111_neg : (83568041 / 125000000) ≤ -Real.log (256227 / 500000) ∧
    -Real.log (256227 / 500000) ≤ (668544329 / 1000000000) := by
  have h := checkLog_sound (w := (243773 / 756227)) (n := 12)
    (lo := (83568041 / 125000000)) (hi := (668544329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 256227) = 1/(256227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14111 : Bounds (-668544329 / 1000000000) (-83568041 / 125000000) (Real.log (256227 / 500000)) := by
  have h := reflection_log_14111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14112_neg : (54283309 / 200000000) ≤ -Real.log (190574724471 / 250000000000) ∧
    -Real.log (190574724471 / 250000000000) ≤ (135708273 / 500000000) := by
  have h := checkLog_sound (w := (59425275529 / 440574724471)) (n := 12)
    (lo := (54283309 / 200000000)) (hi := (135708273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 190574724471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 190574724471) = 1/(190574724471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14112 : Bounds (-135708273 / 500000000) (-54283309 / 200000000) (Real.log (190574724471 / 250000000000)) := by
  have h := reflection_log_14112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14113_neg : (267462727 / 1000000000) ≤ -Real.log (765318855279 / 1000000000000) ∧
    -Real.log (765318855279 / 1000000000000) ≤ (33432841 / 125000000) := by
  have h := checkLog_sound (w := (234681144721 / 1765318855279)) (n := 12)
    (lo := (267462727 / 1000000000)) (hi := (33432841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 765318855279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 765318855279) = 1/(765318855279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14113 : Bounds (-33432841 / 125000000) (-267462727 / 1000000000) (Real.log (765318855279 / 1000000000000)) := by
  have h := reflection_log_14113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14114_neg : (1057536573 / 1000000000) ≤ -Real.log (250000000000 / 719817344601) ∧
    -Real.log (250000000000 / 719817344601) ≤ (42301463 / 40000000) := by
  have h := checkLog_sound (w := (219817344601 / 1219817344601)) (n := 12)
    (lo := (364389393 / 1000000000)) (hi := (182194697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719817344601 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(719817344601 / 500000000000) = 1/(250000000000 / 719817344601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14114 : Bounds (1057536573 / 1000000000) (42301463 / 40000000) (Real.log (719817344601 / 250000000000)) := by
  have h := reflection_log_14114_neg
  have he : Real.log (719817344601 / 250000000000) = -Real.log (250000000000 / 719817344601) := by
    rw [show ((719817344601 / 250000000000) : ℝ) = ((250000000000 / 719817344601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14115_neg : (1065672109 / 1000000000) ≤ -Real.log (100000000000 / 290278932353) ∧
    -Real.log (100000000000 / 290278932353) ≤ (1065672111 / 1000000000) := by
  have h := checkLog_sound (w := (90278932353 / 490278932353)) (n := 12)
    (lo := (372524929 / 1000000000)) (hi := (37252493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290278932353 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(290278932353 / 200000000000) = 1/(100000000000 / 290278932353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14115 : Bounds (1065672109 / 1000000000) (1065672111 / 1000000000) (Real.log (290278932353 / 100000000000)) := by
  have h := reflection_log_14115_neg
  have he : Real.log (290278932353 / 100000000000) = -Real.log (100000000000 / 290278932353) := by
    rw [show ((290278932353 / 100000000000) : ℝ) = ((100000000000 / 290278932353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14116_neg : (2395715433 / 1000000000) ≤ -Real.log (100000000000 / 1097604790419) ∧
    -Real.log (100000000000 / 1097604790419) ≤ (2395715437 / 1000000000) := by
  have h := checkLog_sound (w := (297604790419 / 1897604790419)) (n := 12)
    (lo := (316273893 / 1000000000)) (hi := (158136947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097604790419 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1097604790419 / 800000000000) = 1/(100000000000 / 1097604790419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14116 : Bounds (2395715433 / 1000000000) (2395715437 / 1000000000) (Real.log (1097604790419 / 100000000000)) := by
  have h := reflection_log_14116_neg
  have he : Real.log (1097604790419 / 100000000000) = -Real.log (100000000000 / 1097604790419) := by
    rw [show ((1097604790419 / 100000000000) : ℝ) = ((100000000000 / 1097604790419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14117_neg : (2415478141 / 1000000000) ≤ -Real.log (50000000000 / 559756097561) ∧
    -Real.log (50000000000 / 559756097561) ≤ (483095629 / 200000000) := by
  have h := checkLog_sound (w := (159756097561 / 959756097561)) (n := 12)
    (lo := (336036601 / 1000000000)) (hi := (168018301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559756097561 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(559756097561 / 400000000000) = 1/(50000000000 / 559756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14117 : Bounds (2415478141 / 1000000000) (483095629 / 200000000) (Real.log (559756097561 / 50000000000)) := by
  have h := reflection_log_14117_neg
  have he : Real.log (559756097561 / 50000000000) = -Real.log (50000000000 / 559756097561) := by
    rw [show ((559756097561 / 50000000000) : ℝ) = ((50000000000 / 559756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14118_neg : (121844389 / 200000000) ≤ -Real.log (1000 / 1839) ∧
    -Real.log (1000 / 1839) ≤ (304610973 / 500000000) := by
  have h := checkLog_sound (w := (839 / 2839)) (n := 12)
    (lo := (121844389 / 200000000)) (hi := (304610973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1000) = 1/(1000 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14118 : Bounds (121844389 / 200000000) (304610973 / 500000000) (Real.log (1839 / 1000)) := by
  have h := reflection_log_14118_neg
  have he : Real.log (1839 / 1000) = -Real.log (1000 / 1839) := by
    rw [show ((1839 / 1000) : ℝ) = ((1000 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14119_neg : (28536733 / 15625000) ≤ -Real.log (161 / 1000) ∧
    -Real.log (161 / 1000) ≤ (365270183 / 200000000) := by
  have h := checkLog_sound (w := (89 / 411)) (n := 12)
    (lo := (55007069 / 125000000)) (hi := (440056553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 161) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 161) = 1/(161 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14119 : Bounds (-365270183 / 200000000) (-28536733 / 15625000) (Real.log (161 / 1000)) := by
  have h := reflection_log_14119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14120_neg : (104831 / 125000000) ≤ -Real.log (1000000 / 1000839) ∧
    -Real.log (1000000 / 1000839) ≤ (838649 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 2000839)) (n := 12)
    (lo := (104831 / 125000000)) (hi := (838649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000839 / 1000000) = 1/(1000000 / 1000839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14120 : Bounds (104831 / 125000000) (838649 / 1000000000) (Real.log (1000839 / 1000000)) := by
  have h := reflection_log_14120_neg
  have he : Real.log (1000839 / 1000000) = -Real.log (1000000 / 1000839) := by
    rw [show ((1000839 / 1000000) : ℝ) = ((1000000 / 1000839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14121_neg : (104919 / 125000000) ≤ -Real.log (999161 / 1000000) ∧
    -Real.log (999161 / 1000000) ≤ (839353 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 1999161)) (n := 12)
    (lo := (104919 / 125000000)) (hi := (839353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999161) = 1/(999161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14121 : Bounds (-839353 / 1000000000) (-104919 / 125000000) (Real.log (999161 / 1000000)) := by
  have h := reflection_log_14121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14122_neg : (198338301 / 500000000) ≤ -Real.log (1600 / 2379) ∧
    -Real.log (1600 / 2379) ≤ (396676603 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3979)) (n := 12)
    (lo := (198338301 / 500000000)) (hi := (396676603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2379 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2379 / 1600) = 1/(1600 / 2379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14122 : Bounds (198338301 / 500000000) (396676603 / 1000000000) (Real.log (2379 / 1600)) := by
  have h := reflection_log_14122_neg
  have he : Real.log (2379 / 1600) = -Real.log (1600 / 2379) := by
    rw [show ((2379 / 1600) : ℝ) = ((1600 / 2379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14123_neg : (333617899 / 500000000) ≤ -Real.log (821 / 1600) ∧
    -Real.log (821 / 1600) ≤ (667235799 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2421)) (n := 12)
    (lo := (333617899 / 500000000)) (hi := (667235799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 821) = 1/(821 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14123 : Bounds (-667235799 / 1000000000) (-333617899 / 500000000) (Real.log (821 / 1600)) := by
  have h := reflection_log_14123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14124_neg : (99693191 / 250000000) ≤ -Real.log (200000 / 297999) ∧
    -Real.log (200000 / 297999) ≤ (79754553 / 200000000) := by
  have h := checkLog_sound (w := (97999 / 497999)) (n := 12)
    (lo := (99693191 / 250000000)) (hi := (79754553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297999 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297999 / 200000) = 1/(200000 / 297999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14124 : Bounds (99693191 / 250000000) (79754553 / 200000000) (Real.log (297999 / 200000)) := by
  have h := reflection_log_14124_neg
  have he : Real.log (297999 / 200000) = -Real.log (200000 / 297999) := by
    rw [show ((297999 / 200000) : ℝ) = ((200000 / 297999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14125_neg : (673334749 / 1000000000) ≤ -Real.log (102001 / 200000) ∧
    -Real.log (102001 / 200000) ≤ (2693339 / 4000000) := by
  have h := checkLog_sound (w := (97999 / 302001)) (n := 12)
    (lo := (673334749 / 1000000000)) (hi := (2693339 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 102001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 102001) = 1/(102001 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14125 : Bounds (-2693339 / 4000000) (-673334749 / 1000000000) (Real.log (102001 / 200000)) := by
  have h := reflection_log_14125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14126_neg : (54912397 / 200000000) ≤ -Real.log (30396195999 / 40000000000) ∧
    -Real.log (30396195999 / 40000000000) ≤ (137280993 / 500000000) := by
  have h := checkLog_sound (w := (9603804001 / 70396195999)) (n := 12)
    (lo := (54912397 / 200000000)) (hi := (137280993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30396195999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30396195999) = 1/(30396195999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14126 : Bounds (-137280993 / 500000000) (-54912397 / 200000000) (Real.log (30396195999 / 40000000000)) := by
  have h := reflection_log_14126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14127_neg : (67639799 / 250000000) ≤ -Real.log (1953159 / 2560000) ∧
    -Real.log (1953159 / 2560000) ≤ (270559197 / 1000000000) := by
  have h := checkLog_sound (w := (606841 / 4513159)) (n := 12)
    (lo := (67639799 / 250000000)) (hi := (270559197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 1953159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 1953159) = 1/(1953159 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14127 : Bounds (-270559197 / 1000000000) (-67639799 / 250000000) (Real.log (1953159 / 2560000)) := by
  have h := reflection_log_14127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14128_neg : (2659781 / 2500000) ≤ -Real.log (500000000000 / 1448842874543) ∧
    -Real.log (500000000000 / 1448842874543) ≤ (531956201 / 500000000) := by
  have h := checkLog_sound (w := (448842874543 / 2448842874543)) (n := 12)
    (lo := (18538261 / 50000000)) (hi := (370765221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448842874543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1448842874543 / 1000000000000) = 1/(500000000000 / 1448842874543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14128 : Bounds (2659781 / 2500000) (531956201 / 500000000) (Real.log (1448842874543 / 500000000000)) := by
  have h := reflection_log_14128_neg
  have he : Real.log (1448842874543 / 500000000000) = -Real.log (500000000000 / 1448842874543) := by
    rw [show ((1448842874543 / 500000000000) : ℝ) = ((500000000000 / 1448842874543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14129_neg : (1072107513 / 1000000000) ≤ -Real.log (500000000000 / 1460765090539) ∧
    -Real.log (500000000000 / 1460765090539) ≤ (214421503 / 200000000) := by
  have h := checkLog_sound (w := (460765090539 / 2460765090539)) (n := 12)
    (lo := (378960333 / 1000000000)) (hi := (189480167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460765090539 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1460765090539 / 1000000000000) = 1/(500000000000 / 1460765090539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14129 : Bounds (1072107513 / 1000000000) (214421503 / 200000000) (Real.log (1460765090539 / 500000000000)) := by
  have h := reflection_log_14129_neg
  have he : Real.log (1460765090539 / 500000000000) = -Real.log (500000000000 / 1460765090539) := by
    rw [show ((1460765090539 / 500000000000) : ℝ) = ((500000000000 / 1460765090539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14130_neg : (2415478141 / 1000000000) ≤ -Real.log (500000000000 / 5597560975609) ∧
    -Real.log (500000000000 / 5597560975609) ≤ (483095629 / 200000000) := by
  have h := checkLog_sound (w := (1597560975609 / 9597560975609)) (n := 12)
    (lo := (336036601 / 1000000000)) (hi := (168018301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5597560975609 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5597560975609 / 4000000000000) = 1/(500000000000 / 5597560975609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14130 : Bounds (2415478141 / 1000000000) (483095629 / 200000000) (Real.log (5597560975609 / 500000000000)) := by
  have h := reflection_log_14130_neg
  have he : Real.log (5597560975609 / 500000000000) = -Real.log (500000000000 / 5597560975609) := by
    rw [show ((5597560975609 / 500000000000) : ℝ) = ((500000000000 / 5597560975609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14131_neg : (2435572857 / 1000000000) ≤ -Real.log (7812500000 / 89237189441) ∧
    -Real.log (7812500000 / 89237189441) ≤ (2435572861 / 1000000000) := by
  have h := checkLog_sound (w := (26737189441 / 151737189441)) (n := 12)
    (lo := (356131317 / 1000000000)) (hi := (178065659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89237189441 / 62500000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(89237189441 / 62500000000) = 1/(7812500000 / 89237189441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14131 : Bounds (2435572857 / 1000000000) (2435572861 / 1000000000) (Real.log (89237189441 / 7812500000)) := by
  have h := reflection_log_14131_neg
  have he : Real.log (89237189441 / 7812500000) = -Real.log (7812500000 / 89237189441) := by
    rw [show ((89237189441 / 7812500000) : ℝ) = ((7812500000 / 89237189441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14132_neg : (610851937 / 1000000000) ≤ -Real.log (500 / 921) ∧
    -Real.log (500 / 921) ≤ (305425969 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1421)) (n := 12)
    (lo := (610851937 / 1000000000)) (hi := (305425969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 500) = 1/(500 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14132 : Bounds (610851937 / 1000000000) (305425969 / 500000000) (Real.log (921 / 500)) := by
  have h := reflection_log_14132_neg
  have he : Real.log (921 / 500) = -Real.log (500 / 921) := by
    rw [show ((921 / 500) : ℝ) = ((500 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14133_neg : (461290061 / 250000000) ≤ -Real.log (79 / 500) ∧
    -Real.log (79 / 500) ≤ (1845160247 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 102)) (n := 12)
    (lo := (114716471 / 250000000)) (hi := (91773177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 79) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 79) = 1/(79 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14133 : Bounds (-1845160247 / 1000000000) (-461290061 / 250000000) (Real.log (79 / 500)) := by
  have h := reflection_log_14133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14134_neg : (168329 / 200000000) ≤ -Real.log (500000 / 500421) ∧
    -Real.log (500000 / 500421) ≤ (420823 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1000421)) (n := 12)
    (lo := (168329 / 200000000)) (hi := (420823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500421 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500421 / 500000) = 1/(500000 / 500421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14134 : Bounds (168329 / 200000000) (420823 / 500000000) (Real.log (500421 / 500000)) := by
  have h := reflection_log_14134_neg
  have he : Real.log (500421 / 500000) = -Real.log (500000 / 500421) := by
    rw [show ((500421 / 500000) : ℝ) = ((500000 / 500421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14135_neg : (421177 / 500000000) ≤ -Real.log (499579 / 500000) ∧
    -Real.log (499579 / 500000) ≤ (168471 / 200000000) := by
  have h := checkLog_sound (w := (421 / 999579)) (n := 12)
    (lo := (421177 / 500000000)) (hi := (168471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499579) = 1/(499579 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14135 : Bounds (-168471 / 200000000) (-421177 / 500000000) (Real.log (499579 / 500000)) := by
  have h := reflection_log_14135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14136_neg : (15932893 / 40000000) ≤ -Real.log (250000 / 372331) ∧
    -Real.log (250000 / 372331) ≤ (199161163 / 500000000) := by
  have h := checkLog_sound (w := (122331 / 622331)) (n := 12)
    (lo := (15932893 / 40000000)) (hi := (199161163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372331 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372331 / 250000) = 1/(250000 / 372331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14136 : Bounds (15932893 / 40000000) (199161163 / 500000000) (Real.log (372331 / 250000)) := by
  have h := reflection_log_14136_neg
  have he : Real.log (372331 / 250000) = -Real.log (250000 / 372331) := by
    rw [show ((372331 / 250000) : ℝ) = ((250000 / 372331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14137_neg : (33600997 / 50000000) ≤ -Real.log (127669 / 250000) ∧
    -Real.log (127669 / 250000) ≤ (672019941 / 1000000000) := by
  have h := checkLog_sound (w := (122331 / 377669)) (n := 12)
    (lo := (33600997 / 50000000)) (hi := (672019941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127669) = 1/(127669 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14137 : Bounds (-672019941 / 1000000000) (-33600997 / 50000000) (Real.log (127669 / 250000)) := by
  have h := reflection_log_14137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14138_neg : (80084751 / 200000000) ≤ -Real.log (1000000 / 1492457) ∧
    -Real.log (1000000 / 1492457) ≤ (100105939 / 250000000) := by
  have h := checkLog_sound (w := (492457 / 2492457)) (n := 12)
    (lo := (80084751 / 200000000)) (hi := (100105939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1492457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1492457 / 1000000) = 1/(1000000 / 1492457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14138 : Bounds (80084751 / 200000000) (100105939 / 250000000) (Real.log (1492457 / 1000000)) := by
  have h := reflection_log_14138_neg
  have he : Real.log (1492457 / 1000000) = -Real.log (1000000 / 1492457) := by
    rw [show ((1492457 / 1000000) : ℝ) = ((1000000 / 1492457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14139_neg : (339086921 / 500000000) ≤ -Real.log (507543 / 1000000) ∧
    -Real.log (507543 / 1000000) ≤ (678173843 / 1000000000) := by
  have h := checkLog_sound (w := (492457 / 1507543)) (n := 12)
    (lo := (339086921 / 500000000)) (hi := (678173843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 507543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 507543) = 1/(507543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14139 : Bounds (-678173843 / 1000000000) (-339086921 / 500000000) (Real.log (507543 / 1000000)) := by
  have h := reflection_log_14139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14140_neg : (277750087 / 1000000000) ≤ -Real.log (757486103151 / 1000000000000) ∧
    -Real.log (757486103151 / 1000000000000) ≤ (34718761 / 125000000) := by
  have h := checkLog_sound (w := (242513896849 / 1757486103151)) (n := 12)
    (lo := (277750087 / 1000000000)) (hi := (34718761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 757486103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 757486103151) = 1/(757486103151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14140 : Bounds (-34718761 / 125000000) (-277750087 / 1000000000) (Real.log (757486103151 / 1000000000000)) := by
  have h := reflection_log_14140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14141_neg : (54739523 / 200000000) ≤ -Real.log (47535126439 / 62500000000) ∧
    -Real.log (47535126439 / 62500000000) ≤ (17106101 / 62500000) := by
  have h := checkLog_sound (w := (14964873561 / 110035126439)) (n := 12)
    (lo := (54739523 / 200000000)) (hi := (17106101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47535126439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47535126439) = 1/(47535126439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14141 : Bounds (-17106101 / 62500000) (-54739523 / 200000000) (Real.log (47535126439 / 62500000000)) := by
  have h := reflection_log_14141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14142_neg : (214068453 / 200000000) ≤ -Real.log (50000000000 / 145818875373) ∧
    -Real.log (50000000000 / 145818875373) ≤ (1070342267 / 1000000000) := by
  have h := checkLog_sound (w := (45818875373 / 245818875373)) (n := 12)
    (lo := (75439017 / 200000000)) (hi := (188597543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145818875373 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145818875373 / 100000000000) = 1/(50000000000 / 145818875373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14142 : Bounds (214068453 / 200000000) (1070342267 / 1000000000) (Real.log (145818875373 / 50000000000)) := by
  have h := reflection_log_14142_neg
  have he : Real.log (145818875373 / 50000000000) = -Real.log (50000000000 / 145818875373) := by
    rw [show ((145818875373 / 50000000000) : ℝ) = ((50000000000 / 145818875373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14143_neg : (1078597597 / 1000000000) ≤ -Real.log (250000000000 / 735138205039) ∧
    -Real.log (250000000000 / 735138205039) ≤ (1078597599 / 1000000000) := by
  have h := checkLog_sound (w := (235138205039 / 1235138205039)) (n := 12)
    (lo := (385450417 / 1000000000)) (hi := (192725209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735138205039 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(735138205039 / 500000000000) = 1/(250000000000 / 735138205039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14143 : Bounds (1078597597 / 1000000000) (1078597599 / 1000000000) (Real.log (735138205039 / 250000000000)) := by
  have h := reflection_log_14143_neg
  have he : Real.log (735138205039 / 250000000000) = -Real.log (250000000000 / 735138205039) := by
    rw [show ((735138205039 / 250000000000) : ℝ) = ((250000000000 / 735138205039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
