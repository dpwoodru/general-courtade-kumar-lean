import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12352_neg : (293539191 / 1000000000) ≤ -Real.log (37281 / 50000) ∧
    -Real.log (37281 / 50000) ≤ (36692399 / 125000000) := by
  have h := checkLog_sound (w := (12719 / 87281)) (n := 12)
    (lo := (293539191 / 1000000000)) (hi := (36692399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37281) = 1/(37281 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12352 : Bounds (-36692399 / 125000000) (-293539191 / 1000000000) (Real.log (37281 / 50000)) := by
  have h := reflection_log_12352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12353_neg : (13379553 / 200000000) ≤ -Real.log (2338227039 / 2500000000) ∧
    -Real.log (2338227039 / 2500000000) ≤ (33448883 / 500000000) := by
  have h := checkLog_sound (w := (161772961 / 4838227039)) (n := 12)
    (lo := (13379553 / 200000000)) (hi := (33448883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2338227039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2338227039) = 1/(2338227039 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12353 : Bounds (-33448883 / 500000000) (-13379553 / 200000000) (Real.log (2338227039 / 2500000000)) := by
  have h := reflection_log_12353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12354_neg : (6633607 / 100000000) ≤ -Real.log (37432652439 / 40000000000) ∧
    -Real.log (37432652439 / 40000000000) ≤ (66336071 / 1000000000) := by
  have h := checkLog_sound (w := (2567347561 / 77432652439)) (n := 12)
    (lo := (6633607 / 100000000)) (hi := (66336071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37432652439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37432652439) = 1/(37432652439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12354 : Bounds (-66336071 / 1000000000) (-6633607 / 100000000) (Real.log (37432652439 / 40000000000)) := by
  have h := reflection_log_12354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12355_neg : (20718721 / 40000000) ≤ -Real.log (500000000000 / 839306640951) ∧
    -Real.log (500000000000 / 839306640951) ≤ (258984013 / 500000000) := by
  have h := checkLog_sound (w := (339306640951 / 1339306640951)) (n := 12)
    (lo := (20718721 / 40000000)) (hi := (258984013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839306640951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839306640951 / 500000000000) = 1/(500000000000 / 839306640951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12355 : Bounds (20718721 / 40000000) (258984013 / 500000000) (Real.log (839306640951 / 500000000000)) := by
  have h := reflection_log_12355_neg
  have he : Real.log (839306640951 / 500000000000) = -Real.log (500000000000 / 839306640951) := by
    rw [show ((839306640951 / 500000000000) : ℝ) = ((500000000000 / 839306640951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12356_neg : (260090309 / 500000000) ≤ -Real.log (500000000000 / 841165741263) ∧
    -Real.log (500000000000 / 841165741263) ≤ (520180619 / 1000000000) := by
  have h := checkLog_sound (w := (341165741263 / 1341165741263)) (n := 12)
    (lo := (260090309 / 500000000)) (hi := (520180619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841165741263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841165741263 / 500000000000) = 1/(500000000000 / 841165741263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12356 : Bounds (260090309 / 500000000) (520180619 / 1000000000) (Real.log (841165741263 / 500000000000)) := by
  have h := reflection_log_12356_neg
  have he : Real.log (841165741263 / 500000000000) = -Real.log (500000000000 / 841165741263) := by
    rw [show ((841165741263 / 500000000000) : ℝ) = ((500000000000 / 841165741263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12357_neg : (21180063 / 20000000) ≤ -Real.log (100000000000 / 288349514563) ∧
    -Real.log (100000000000 / 288349514563) ≤ (66187697 / 62500000) := by
  have h := checkLog_sound (w := (88349514563 / 488349514563)) (n := 12)
    (lo := (36585597 / 100000000)) (hi := (365855971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288349514563 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288349514563 / 200000000000) = 1/(100000000000 / 288349514563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12357 : Bounds (21180063 / 20000000) (66187697 / 62500000) (Real.log (288349514563 / 100000000000)) := by
  have h := reflection_log_12357_neg
  have he : Real.log (288349514563 / 100000000000) = -Real.log (100000000000 / 288349514563) := by
    rw [show ((288349514563 / 100000000000) : ℝ) = ((100000000000 / 288349514563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12358_neg : (1061619959 / 1000000000) ≤ -Real.log (500000000000 / 1445525291829) ∧
    -Real.log (500000000000 / 1445525291829) ≤ (1061619961 / 1000000000) := by
  have h := checkLog_sound (w := (445525291829 / 2445525291829)) (n := 12)
    (lo := (368472779 / 1000000000)) (hi := (18423639 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445525291829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1445525291829 / 1000000000000) = 1/(500000000000 / 1445525291829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12358 : Bounds (1061619959 / 1000000000) (1061619961 / 1000000000) (Real.log (1445525291829 / 500000000000)) := by
  have h := reflection_log_12358_neg
  have he : Real.log (1445525291829 / 500000000000) = -Real.log (500000000000 / 1445525291829) := by
    rw [show ((1445525291829 / 500000000000) : ℝ) = ((500000000000 / 1445525291829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12359_neg : (396760667 / 1000000000) ≤ -Real.log (1000 / 1487) ∧
    -Real.log (1000 / 1487) ≤ (99190167 / 250000000) := by
  have h := checkLog_sound (w := (487 / 2487)) (n := 12)
    (lo := (396760667 / 1000000000)) (hi := (99190167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1000) = 1/(1000 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12359 : Bounds (396760667 / 1000000000) (99190167 / 250000000) (Real.log (1487 / 1000)) := by
  have h := reflection_log_12359_neg
  have he : Real.log (1487 / 1000) = -Real.log (1000 / 1487) := by
    rw [show ((1487 / 1000) : ℝ) = ((1000 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12360_neg : (667479433 / 1000000000) ≤ -Real.log (513 / 1000) ∧
    -Real.log (513 / 1000) ≤ (333739717 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1513)) (n := 12)
    (lo := (667479433 / 1000000000)) (hi := (333739717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 513) = 1/(513 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12360 : Bounds (-333739717 / 500000000) (-667479433 / 1000000000) (Real.log (513 / 1000)) := by
  have h := reflection_log_12360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12361_neg : (486881 / 1000000000) ≤ -Real.log (1000000 / 1000487) ∧
    -Real.log (1000000 / 1000487) ≤ (243441 / 500000000) := by
  have h := checkLog_sound (w := (487 / 2000487)) (n := 12)
    (lo := (486881 / 1000000000)) (hi := (243441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000487 / 1000000) = 1/(1000000 / 1000487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12361 : Bounds (486881 / 1000000000) (243441 / 500000000) (Real.log (1000487 / 1000000)) := by
  have h := reflection_log_12361_neg
  have he : Real.log (1000487 / 1000000) = -Real.log (1000000 / 1000487) := by
    rw [show ((1000487 / 1000000) : ℝ) = ((1000000 / 1000487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12362_neg : (243559 / 500000000) ≤ -Real.log (999513 / 1000000) ∧
    -Real.log (999513 / 1000000) ≤ (487119 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 1999513)) (n := 12)
    (lo := (243559 / 500000000)) (hi := (487119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999513) = 1/(999513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12362 : Bounds (-487119 / 1000000000) (-243559 / 500000000) (Real.log (999513 / 1000000)) := by
  have h := reflection_log_12362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12363_neg : (226272251 / 1000000000) ≤ -Real.log (1000000 / 1253917) ∧
    -Real.log (1000000 / 1253917) ≤ (56568063 / 250000000) := by
  have h := checkLog_sound (w := (253917 / 2253917)) (n := 12)
    (lo := (226272251 / 1000000000)) (hi := (56568063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253917 / 1000000) = 1/(1000000 / 1253917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12363 : Bounds (226272251 / 1000000000) (56568063 / 250000000) (Real.log (1253917 / 1000000)) := by
  have h := reflection_log_12363_neg
  have he : Real.log (1253917 / 1000000) = -Real.log (1000000 / 1253917) := by
    rw [show ((1253917 / 1000000) : ℝ) = ((1000000 / 1253917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12364_neg : (36614803 / 125000000) ≤ -Real.log (746083 / 1000000) ∧
    -Real.log (746083 / 1000000) ≤ (11716737 / 40000000) := by
  have h := checkLog_sound (w := (253917 / 1746083)) (n := 12)
    (lo := (36614803 / 125000000)) (hi := (11716737 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746083) = 1/(746083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12364 : Bounds (-11716737 / 40000000) (-36614803 / 125000000) (Real.log (746083 / 1000000)) := by
  have h := reflection_log_12364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12365_neg : (227098121 / 1000000000) ≤ -Real.log (1000000 / 1254953) ∧
    -Real.log (1000000 / 1254953) ≤ (113549061 / 500000000) := by
  have h := checkLog_sound (w := (254953 / 2254953)) (n := 12)
    (lo := (227098121 / 1000000000)) (hi := (113549061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254953 / 1000000) = 1/(1000000 / 1254953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12365 : Bounds (227098121 / 1000000000) (113549061 / 500000000) (Real.log (1254953 / 1000000)) := by
  have h := reflection_log_12365_neg
  have he : Real.log (1254953 / 1000000) = -Real.log (1000000 / 1254953) := by
    rw [show ((1254953 / 1000000) : ℝ) = ((1000000 / 1254953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12366_neg : (11772319 / 40000000) ≤ -Real.log (745047 / 1000000) ∧
    -Real.log (745047 / 1000000) ≤ (36788497 / 125000000) := by
  have h := checkLog_sound (w := (254953 / 1745047)) (n := 12)
    (lo := (11772319 / 40000000)) (hi := (36788497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745047) = 1/(745047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12366 : Bounds (-36788497 / 125000000) (-11772319 / 40000000) (Real.log (745047 / 1000000)) := by
  have h := reflection_log_12366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12367_neg : (67209853 / 1000000000) ≤ -Real.log (934998967791 / 1000000000000) ∧
    -Real.log (934998967791 / 1000000000000) ≤ (33604927 / 500000000) := by
  have h := checkLog_sound (w := (65001032209 / 1934998967791)) (n := 12)
    (lo := (67209853 / 1000000000)) (hi := (33604927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 934998967791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 934998967791) = 1/(934998967791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12367 : Bounds (-33604927 / 500000000) (-67209853 / 1000000000) (Real.log (934998967791 / 1000000000000)) := by
  have h := reflection_log_12367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12368_neg : (66646173 / 1000000000) ≤ -Real.log (935526157111 / 1000000000000) ∧
    -Real.log (935526157111 / 1000000000000) ≤ (33323087 / 500000000) := by
  have h := checkLog_sound (w := (64473842889 / 1935526157111)) (n := 12)
    (lo := (66646173 / 1000000000)) (hi := (33323087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935526157111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935526157111) = 1/(935526157111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12368 : Bounds (-33323087 / 500000000) (-66646173 / 1000000000) (Real.log (935526157111 / 1000000000000)) := by
  have h := reflection_log_12368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12369_neg : (129797669 / 250000000) ≤ -Real.log (100000000000 / 168066689631) ∧
    -Real.log (100000000000 / 168066689631) ≤ (519190677 / 1000000000) := by
  have h := checkLog_sound (w := (68066689631 / 268066689631)) (n := 12)
    (lo := (129797669 / 250000000)) (hi := (519190677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168066689631 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168066689631 / 100000000000) = 1/(100000000000 / 168066689631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12369 : Bounds (129797669 / 250000000) (519190677 / 1000000000) (Real.log (168066689631 / 100000000000)) := by
  have h := reflection_log_12369_neg
  have he : Real.log (168066689631 / 100000000000) = -Real.log (100000000000 / 168066689631) := by
    rw [show ((168066689631 / 100000000000) : ℝ) = ((100000000000 / 168066689631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12370_neg : (521406097 / 1000000000) ≤ -Real.log (500000000000 / 842197203667) ∧
    -Real.log (500000000000 / 842197203667) ≤ (260703049 / 500000000) := by
  have h := checkLog_sound (w := (342197203667 / 1342197203667)) (n := 12)
    (lo := (521406097 / 1000000000)) (hi := (260703049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842197203667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842197203667 / 500000000000) = 1/(500000000000 / 842197203667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12370 : Bounds (521406097 / 1000000000) (260703049 / 500000000) (Real.log (842197203667 / 500000000000)) := by
  have h := reflection_log_12370_neg
  have he : Real.log (842197203667 / 500000000000) = -Real.log (500000000000 / 842197203667) := by
    rw [show ((842197203667 / 500000000000) : ℝ) = ((500000000000 / 842197203667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12371_neg : (1061619959 / 1000000000) ≤ -Real.log (125000000000 / 361381322957) ∧
    -Real.log (125000000000 / 361381322957) ≤ (1061619961 / 1000000000) := by
  have h := checkLog_sound (w := (111381322957 / 611381322957)) (n := 12)
    (lo := (368472779 / 1000000000)) (hi := (18423639 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361381322957 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361381322957 / 250000000000) = 1/(125000000000 / 361381322957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12371 : Bounds (1061619959 / 1000000000) (1061619961 / 1000000000) (Real.log (361381322957 / 125000000000)) := by
  have h := reflection_log_12371_neg
  have he : Real.log (361381322957 / 125000000000) = -Real.log (125000000000 / 361381322957) := by
    rw [show ((361381322957 / 125000000000) : ℝ) = ((125000000000 / 361381322957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12372_neg : (10642401 / 10000000) ≤ -Real.log (62500000000 / 181164717349) ∧
    -Real.log (62500000000 / 181164717349) ≤ (532120051 / 500000000) := by
  have h := checkLog_sound (w := (56164717349 / 306164717349)) (n := 12)
    (lo := (9277323 / 25000000)) (hi := (371092921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181164717349 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(181164717349 / 125000000000) = 1/(62500000000 / 181164717349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12372 : Bounds (10642401 / 10000000) (532120051 / 500000000) (Real.log (181164717349 / 62500000000)) := by
  have h := reflection_log_12372_neg
  have he : Real.log (181164717349 / 62500000000) = -Real.log (62500000000 / 181164717349) := by
    rw [show ((181164717349 / 62500000000) : ℝ) = ((62500000000 / 181164717349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12373_neg : (49679117 / 125000000) ≤ -Real.log (125 / 186) ∧
    -Real.log (125 / 186) ≤ (397432937 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 311)) (n := 12)
    (lo := (49679117 / 125000000)) (hi := (397432937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186 / 125) = 1/(125 / 186) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12373 : Bounds (49679117 / 125000000) (397432937 / 1000000000) (Real.log (186 / 125)) := by
  have h := reflection_log_12373_neg
  have he : Real.log (186 / 125) = -Real.log (125 / 186) := by
    rw [show ((186 / 125) : ℝ) = ((125 / 186) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12374_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12374 : Bounds (-334715327 / 500000000) (-669430653 / 1000000000) (Real.log (64 / 125)) := by
  have h := reflection_log_12374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12375_neg : (12197 / 25000000) ≤ -Real.log (125000 / 125061) ∧
    -Real.log (125000 / 125061) ≤ (487881 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 250061)) (n := 12)
    (lo := (12197 / 25000000)) (hi := (487881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125061 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125061 / 125000) = 1/(125000 / 125061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12375 : Bounds (12197 / 25000000) (487881 / 1000000000) (Real.log (125061 / 125000)) := by
  have h := reflection_log_12375_neg
  have he : Real.log (125061 / 125000) = -Real.log (125000 / 125061) := by
    rw [show ((125061 / 125000) : ℝ) = ((125000 / 125061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12376_neg : (488119 / 1000000000) ≤ -Real.log (124939 / 125000) ∧
    -Real.log (124939 / 125000) ≤ (12203 / 25000000) := by
  have h := checkLog_sound (w := (61 / 249939)) (n := 12)
    (lo := (488119 / 1000000000)) (hi := (12203 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124939) = 1/(124939 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12376 : Bounds (-12203 / 25000000) (-488119 / 1000000000) (Real.log (124939 / 125000)) := by
  have h := reflection_log_12376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12377_neg : (113364159 / 500000000) ≤ -Real.log (1000000 / 1254489) ∧
    -Real.log (1000000 / 1254489) ≤ (226728319 / 1000000000) := by
  have h := checkLog_sound (w := (254489 / 2254489)) (n := 12)
    (lo := (113364159 / 500000000)) (hi := (226728319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254489 / 1000000) = 1/(1000000 / 1254489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12377 : Bounds (113364159 / 500000000) (226728319 / 1000000000) (Real.log (1254489 / 1000000)) := by
  have h := reflection_log_12377_neg
  have he : Real.log (1254489 / 1000000) = -Real.log (1000000 / 1254489) := by
    rw [show ((1254489 / 1000000) : ℝ) = ((1000000 / 1254489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12378_neg : (293685389 / 1000000000) ≤ -Real.log (745511 / 1000000) ∧
    -Real.log (745511 / 1000000) ≤ (29368539 / 100000000) := by
  have h := checkLog_sound (w := (254489 / 1745511)) (n := 12)
    (lo := (293685389 / 1000000000)) (hi := (29368539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745511) = 1/(745511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12378 : Bounds (-29368539 / 100000000) (-293685389 / 1000000000) (Real.log (745511 / 1000000)) := by
  have h := reflection_log_12378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12379_neg : (14222163 / 62500000) ≤ -Real.log (500000 / 627763) ∧
    -Real.log (500000 / 627763) ≤ (227554609 / 1000000000) := by
  have h := checkLog_sound (w := (127763 / 1127763)) (n := 12)
    (lo := (14222163 / 62500000)) (hi := (227554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627763 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627763 / 500000) = 1/(500000 / 627763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12379 : Bounds (14222163 / 62500000) (227554609 / 1000000000) (Real.log (627763 / 500000)) := by
  have h := reflection_log_12379_neg
  have he : Real.log (627763 / 500000) = -Real.log (500000 / 627763) := by
    rw [show ((627763 / 500000) : ℝ) = ((500000 / 627763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12380_neg : (5901547 / 20000000) ≤ -Real.log (372237 / 500000) ∧
    -Real.log (372237 / 500000) ≤ (295077351 / 1000000000) := by
  have h := checkLog_sound (w := (127763 / 872237)) (n := 12)
    (lo := (5901547 / 20000000)) (hi := (295077351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372237) = 1/(372237 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12380 : Bounds (-295077351 / 1000000000) (-5901547 / 20000000) (Real.log (372237 / 500000)) := by
  have h := reflection_log_12380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12381_neg : (67522741 / 1000000000) ≤ -Real.log (233676615831 / 250000000000) ∧
    -Real.log (233676615831 / 250000000000) ≤ (33761371 / 500000000) := by
  have h := checkLog_sound (w := (16323384169 / 483676615831)) (n := 12)
    (lo := (67522741 / 1000000000)) (hi := (33761371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233676615831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233676615831) = 1/(233676615831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12381 : Bounds (-33761371 / 500000000) (-67522741 / 1000000000) (Real.log (233676615831 / 250000000000)) := by
  have h := reflection_log_12381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12382_neg : (66957071 / 1000000000) ≤ -Real.log (935235348879 / 1000000000000) ∧
    -Real.log (935235348879 / 1000000000000) ≤ (4184817 / 62500000) := by
  have h := checkLog_sound (w := (64764651121 / 1935235348879)) (n := 12)
    (lo := (66957071 / 1000000000)) (hi := (4184817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935235348879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935235348879) = 1/(935235348879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12382 : Bounds (-4184817 / 62500000) (-66957071 / 1000000000) (Real.log (935235348879 / 1000000000000)) := by
  have h := reflection_log_12382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12383_neg : (130103427 / 250000000) ≤ -Real.log (125000000000 / 210340457753) ∧
    -Real.log (125000000000 / 210340457753) ≤ (520413709 / 1000000000) := by
  have h := checkLog_sound (w := (85340457753 / 335340457753)) (n := 12)
    (lo := (130103427 / 250000000)) (hi := (520413709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210340457753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210340457753 / 125000000000) = 1/(125000000000 / 210340457753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12383 : Bounds (130103427 / 250000000) (520413709 / 1000000000) (Real.log (210340457753 / 125000000000)) := by
  have h := reflection_log_12383_neg
  have he : Real.log (210340457753 / 125000000000) = -Real.log (125000000000 / 210340457753) := by
    rw [show ((210340457753 / 125000000000) : ℝ) = ((125000000000 / 210340457753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12384_neg : (261315979 / 500000000) ≤ -Real.log (125000000000 / 210807563461) ∧
    -Real.log (125000000000 / 210807563461) ≤ (522631959 / 1000000000) := by
  have h := checkLog_sound (w := (85807563461 / 335807563461)) (n := 12)
    (lo := (261315979 / 500000000)) (hi := (522631959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210807563461 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210807563461 / 125000000000) = 1/(125000000000 / 210807563461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12384 : Bounds (261315979 / 500000000) (522631959 / 1000000000) (Real.log (210807563461 / 125000000000)) := by
  have h := reflection_log_12384_neg
  have he : Real.log (210807563461 / 125000000000) = -Real.log (125000000000 / 210807563461) := by
    rw [show ((210807563461 / 125000000000) : ℝ) = ((125000000000 / 210807563461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12385_neg : (10642401 / 10000000) ≤ -Real.log (500000000000 / 1449317738791) ∧
    -Real.log (500000000000 / 1449317738791) ≤ (532120051 / 500000000) := by
  have h := checkLog_sound (w := (449317738791 / 2449317738791)) (n := 12)
    (lo := (9277323 / 25000000)) (hi := (371092921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449317738791 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1449317738791 / 1000000000000) = 1/(500000000000 / 1449317738791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12385 : Bounds (10642401 / 10000000) (532120051 / 500000000) (Real.log (1449317738791 / 500000000000)) := by
  have h := reflection_log_12385_neg
  have he : Real.log (1449317738791 / 500000000000) = -Real.log (500000000000 / 1449317738791) := by
    rw [show ((1449317738791 / 500000000000) : ℝ) = ((500000000000 / 1449317738791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12386_neg : (1066863589 / 1000000000) ≤ -Real.log (32 / 93) ∧
    -Real.log (32 / 93) ≤ (1066863591 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(93 / 64) = 1/(32 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12386 : Bounds (1066863589 / 1000000000) (1066863591 / 1000000000) (Real.log (93 / 32)) := by
  have h := reflection_log_12386_neg
  have he : Real.log (93 / 32) = -Real.log (32 / 93) := by
    rw [show ((93 / 32) : ℝ) = ((32 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12387_neg : (398104753 / 1000000000) ≤ -Real.log (1000 / 1489) ∧
    -Real.log (1000 / 1489) ≤ (199052377 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2489)) (n := 12)
    (lo := (398104753 / 1000000000)) (hi := (199052377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 1000) = 1/(1000 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12387 : Bounds (398104753 / 1000000000) (199052377 / 500000000) (Real.log (1489 / 1000)) := by
  have h := reflection_log_12387_neg
  have he : Real.log (1489 / 1000) = -Real.log (1000 / 1489) := by
    rw [show ((1489 / 1000) : ℝ) = ((1000 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12388_neg : (83923211 / 125000000) ≤ -Real.log (511 / 1000) ∧
    -Real.log (511 / 1000) ≤ (671385689 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 1511)) (n := 12)
    (lo := (83923211 / 125000000)) (hi := (671385689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 511) = 1/(511 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12388 : Bounds (-671385689 / 1000000000) (-83923211 / 125000000) (Real.log (511 / 1000)) := by
  have h := reflection_log_12388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12389_neg : (6111 / 12500000) ≤ -Real.log (1000000 / 1000489) ∧
    -Real.log (1000000 / 1000489) ≤ (488881 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2000489)) (n := 12)
    (lo := (6111 / 12500000)) (hi := (488881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000489 / 1000000) = 1/(1000000 / 1000489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12389 : Bounds (6111 / 12500000) (488881 / 1000000000) (Real.log (1000489 / 1000000)) := by
  have h := reflection_log_12389_neg
  have he : Real.log (1000489 / 1000000) = -Real.log (1000000 / 1000489) := by
    rw [show ((1000489 / 1000000) : ℝ) = ((1000000 / 1000489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12390_neg : (489119 / 1000000000) ≤ -Real.log (999511 / 1000000) ∧
    -Real.log (999511 / 1000000) ≤ (3057 / 6250000) := by
  have h := checkLog_sound (w := (489 / 1999511)) (n := 12)
    (lo := (489119 / 1000000000)) (hi := (3057 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999511) = 1/(999511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12390 : Bounds (-3057 / 6250000) (-489119 / 1000000000) (Real.log (999511 / 1000000)) := by
  have h := reflection_log_12390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12391_neg : (227184973 / 1000000000) ≤ -Real.log (500000 / 627531) ∧
    -Real.log (500000 / 627531) ≤ (113592487 / 500000000) := by
  have h := checkLog_sound (w := (127531 / 1127531)) (n := 12)
    (lo := (227184973 / 1000000000)) (hi := (113592487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627531 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627531 / 500000) = 1/(500000 / 627531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12391 : Bounds (227184973 / 1000000000) (113592487 / 500000000) (Real.log (627531 / 500000)) := by
  have h := reflection_log_12391_neg
  have he : Real.log (627531 / 500000) = -Real.log (500000 / 627531) := by
    rw [show ((627531 / 500000) : ℝ) = ((500000 / 627531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12392_neg : (58890857 / 200000000) ≤ -Real.log (372469 / 500000) ∧
    -Real.log (372469 / 500000) ≤ (147227143 / 500000000) := by
  have h := checkLog_sound (w := (127531 / 872469)) (n := 12)
    (lo := (58890857 / 200000000)) (hi := (147227143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372469) = 1/(372469 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12392 : Bounds (-147227143 / 500000000) (-58890857 / 200000000) (Real.log (372469 / 500000)) := by
  have h := reflection_log_12392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12393_neg : (114005841 / 500000000) ≤ -Real.log (10000 / 12561) ∧
    -Real.log (10000 / 12561) ≤ (228011683 / 1000000000) := by
  have h := checkLog_sound (w := (2561 / 22561)) (n := 12)
    (lo := (114005841 / 500000000)) (hi := (228011683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10000) = 1/(10000 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12393 : Bounds (114005841 / 500000000) (228011683 / 1000000000) (Real.log (12561 / 10000)) := by
  have h := reflection_log_12393_neg
  have he : Real.log (12561 / 10000) = -Real.log (10000 / 12561) := by
    rw [show ((12561 / 10000) : ℝ) = ((10000 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12394_neg : (295848661 / 1000000000) ≤ -Real.log (7439 / 10000) ∧
    -Real.log (7439 / 10000) ≤ (147924331 / 500000000) := by
  have h := checkLog_sound (w := (2561 / 17439)) (n := 12)
    (lo := (295848661 / 1000000000)) (hi := (147924331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7439) = 1/(7439 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12394 : Bounds (-147924331 / 500000000) (-295848661 / 1000000000) (Real.log (7439 / 10000)) := by
  have h := reflection_log_12394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12395_neg : (67836979 / 1000000000) ≤ -Real.log (93441279 / 100000000) ∧
    -Real.log (93441279 / 100000000) ≤ (3391849 / 50000000) := by
  have h := checkLog_sound (w := (6558721 / 193441279)) (n := 12)
    (lo := (67836979 / 1000000000)) (hi := (3391849 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 93441279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 93441279) = 1/(93441279 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12395 : Bounds (-3391849 / 50000000) (-67836979 / 1000000000) (Real.log (93441279 / 100000000)) := by
  have h := reflection_log_12395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12396_neg : (67269311 / 1000000000) ≤ -Real.log (233735844039 / 250000000000) ∧
    -Real.log (233735844039 / 250000000000) ≤ (1051083 / 15625000) := by
  have h := checkLog_sound (w := (16264155961 / 483735844039)) (n := 12)
    (lo := (67269311 / 1000000000)) (hi := (1051083 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233735844039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233735844039) = 1/(233735844039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12396 : Bounds (-1051083 / 15625000) (-67269311 / 1000000000) (Real.log (233735844039 / 250000000000)) := by
  have h := reflection_log_12396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12397_neg : (521639259 / 1000000000) ≤ -Real.log (500000000000 / 842393595171) ∧
    -Real.log (500000000000 / 842393595171) ≤ (26081963 / 50000000) := by
  have h := checkLog_sound (w := (342393595171 / 1342393595171)) (n := 12)
    (lo := (521639259 / 1000000000)) (hi := (26081963 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842393595171 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842393595171 / 500000000000) = 1/(500000000000 / 842393595171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12397 : Bounds (521639259 / 1000000000) (26081963 / 50000000) (Real.log (842393595171 / 500000000000)) := by
  have h := reflection_log_12397_neg
  have he : Real.log (842393595171 / 500000000000) = -Real.log (500000000000 / 842393595171) := by
    rw [show ((842393595171 / 500000000000) : ℝ) = ((500000000000 / 842393595171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12398_neg : (65482543 / 125000000) ≤ -Real.log (250000000000 / 422133351257) ∧
    -Real.log (250000000000 / 422133351257) ≤ (104772069 / 200000000) := by
  have h := checkLog_sound (w := (172133351257 / 672133351257)) (n := 12)
    (lo := (65482543 / 125000000)) (hi := (104772069 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422133351257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422133351257 / 250000000000) = 1/(250000000000 / 422133351257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12398 : Bounds (65482543 / 125000000) (104772069 / 200000000) (Real.log (422133351257 / 250000000000)) := by
  have h := reflection_log_12398_neg
  have he : Real.log (422133351257 / 250000000000) = -Real.log (250000000000 / 422133351257) := by
    rw [show ((422133351257 / 250000000000) : ℝ) = ((250000000000 / 422133351257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12399_neg : (1069490441 / 1000000000) ≤ -Real.log (500000000000 / 1456947162427) ∧
    -Real.log (500000000000 / 1456947162427) ≤ (1069490443 / 1000000000) := by
  have h := checkLog_sound (w := (456947162427 / 2456947162427)) (n := 12)
    (lo := (376343261 / 1000000000)) (hi := (188171631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1456947162427 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1456947162427 / 1000000000000) = 1/(500000000000 / 1456947162427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12399 : Bounds (1069490441 / 1000000000) (1069490443 / 1000000000) (Real.log (1456947162427 / 500000000000)) := by
  have h := reflection_log_12399_neg
  have he : Real.log (1456947162427 / 500000000000) = -Real.log (500000000000 / 1456947162427) := by
    rw [show ((1456947162427 / 500000000000) : ℝ) = ((500000000000 / 1456947162427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12400_neg : (398776119 / 1000000000) ≤ -Real.log (100 / 149) ∧
    -Real.log (100 / 149) ≤ (9969403 / 25000000) := by
  have h := checkLog_sound (w := (49 / 249)) (n := 12)
    (lo := (398776119 / 1000000000)) (hi := (9969403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149 / 100) = 1/(100 / 149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12400 : Bounds (398776119 / 1000000000) (9969403 / 25000000) (Real.log (149 / 100)) := by
  have h := reflection_log_12400_neg
  have he : Real.log (149 / 100) = -Real.log (100 / 149) := by
    rw [show ((149 / 100) : ℝ) = ((100 / 149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12401_neg : (673344553 / 1000000000) ≤ -Real.log (51 / 100) ∧
    -Real.log (51 / 100) ≤ (336672277 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 51) = 1/(51 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12401 : Bounds (-336672277 / 500000000) (-673344553 / 1000000000) (Real.log (51 / 100)) := by
  have h := reflection_log_12401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12402_neg : (489879 / 1000000000) ≤ -Real.log (100000 / 100049) ∧
    -Real.log (100000 / 100049) ≤ (12247 / 25000000) := by
  have h := checkLog_sound (w := (49 / 200049)) (n := 12)
    (lo := (489879 / 1000000000)) (hi := (12247 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100049 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100049 / 100000) = 1/(100000 / 100049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12402 : Bounds (489879 / 1000000000) (12247 / 25000000) (Real.log (100049 / 100000)) := by
  have h := reflection_log_12402_neg
  have he : Real.log (100049 / 100000) = -Real.log (100000 / 100049) := by
    rw [show ((100049 / 100000) : ℝ) = ((100000 / 100049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12403_neg : (12253 / 25000000) ≤ -Real.log (99951 / 100000) ∧
    -Real.log (99951 / 100000) ≤ (490121 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 199951)) (n := 12)
    (lo := (12253 / 25000000)) (hi := (490121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99951) = 1/(99951 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12403 : Bounds (-490121 / 1000000000) (-12253 / 25000000) (Real.log (99951 / 100000)) := by
  have h := reflection_log_12403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12404_neg : (11382071 / 50000000) ≤ -Real.log (200000 / 251127) ∧
    -Real.log (200000 / 251127) ≤ (227641421 / 1000000000) := by
  have h := checkLog_sound (w := (51127 / 451127)) (n := 12)
    (lo := (11382071 / 50000000)) (hi := (227641421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251127 / 200000) = 1/(200000 / 251127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12404 : Bounds (11382071 / 50000000) (227641421 / 1000000000) (Real.log (251127 / 200000)) := by
  have h := reflection_log_12404_neg
  have he : Real.log (251127 / 200000) = -Real.log (200000 / 251127) := by
    rw [show ((251127 / 200000) : ℝ) = ((200000 / 251127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12405_neg : (295223773 / 1000000000) ≤ -Real.log (148873 / 200000) ∧
    -Real.log (148873 / 200000) ≤ (147611887 / 500000000) := by
  have h := checkLog_sound (w := (51127 / 348873)) (n := 12)
    (lo := (295223773 / 1000000000)) (hi := (147611887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148873) = 1/(148873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12405 : Bounds (-147611887 / 500000000) (-295223773 / 1000000000) (Real.log (148873 / 200000)) := by
  have h := reflection_log_12405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12406_neg : (57117137 / 250000000) ≤ -Real.log (500000 / 628337) ∧
    -Real.log (500000 / 628337) ≤ (228468549 / 1000000000) := by
  have h := checkLog_sound (w := (128337 / 1128337)) (n := 12)
    (lo := (57117137 / 250000000)) (hi := (228468549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628337 / 500000) = 1/(500000 / 628337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12406 : Bounds (57117137 / 250000000) (228468549 / 1000000000) (Real.log (628337 / 500000)) := by
  have h := reflection_log_12406_neg
  have he : Real.log (628337 / 500000) = -Real.log (500000 / 628337) := by
    rw [show ((628337 / 500000) : ℝ) = ((500000 / 628337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12407_neg : (37077571 / 125000000) ≤ -Real.log (371663 / 500000) ∧
    -Real.log (371663 / 500000) ≤ (296620569 / 1000000000) := by
  have h := checkLog_sound (w := (128337 / 871663)) (n := 12)
    (lo := (37077571 / 125000000)) (hi := (296620569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371663) = 1/(371663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12407 : Bounds (-296620569 / 1000000000) (-37077571 / 125000000) (Real.log (371663 / 500000)) := by
  have h := reflection_log_12407_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12408_neg : (3407601 / 50000000) ≤ -Real.log (233529614431 / 250000000000) ∧
    -Real.log (233529614431 / 250000000000) ≤ (68152021 / 1000000000) := by
  have h := checkLog_sound (w := (16470385569 / 483529614431)) (n := 12)
    (lo := (3407601 / 50000000)) (hi := (68152021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233529614431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233529614431) = 1/(233529614431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12408 : Bounds (-68152021 / 1000000000) (-3407601 / 50000000) (Real.log (233529614431 / 250000000000)) := by
  have h := reflection_log_12408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12409_neg : (4223897 / 62500000) ≤ -Real.log (37386029871 / 40000000000) ∧
    -Real.log (37386029871 / 40000000000) ≤ (67582353 / 1000000000) := by
  have h := checkLog_sound (w := (2613970129 / 77386029871)) (n := 12)
    (lo := (4223897 / 62500000)) (hi := (67582353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37386029871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37386029871) = 1/(37386029871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12409 : Bounds (-67582353 / 1000000000) (-4223897 / 62500000) (Real.log (37386029871 / 40000000000)) := by
  have h := reflection_log_12409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12410_neg : (522865193 / 1000000000) ≤ -Real.log (500000000000 / 843426947801) ∧
    -Real.log (500000000000 / 843426947801) ≤ (261432597 / 500000000) := by
  have h := checkLog_sound (w := (343426947801 / 1343426947801)) (n := 12)
    (lo := (522865193 / 1000000000)) (hi := (261432597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843426947801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843426947801 / 500000000000) = 1/(500000000000 / 843426947801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12410 : Bounds (522865193 / 1000000000) (261432597 / 500000000) (Real.log (843426947801 / 500000000000)) := by
  have h := reflection_log_12410_neg
  have he : Real.log (843426947801 / 500000000000) = -Real.log (500000000000 / 843426947801) := by
    rw [show ((843426947801 / 500000000000) : ℝ) = ((500000000000 / 843426947801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12411_neg : (525089117 / 1000000000) ≤ -Real.log (250000000000 / 422652375943) ∧
    -Real.log (250000000000 / 422652375943) ≤ (262544559 / 500000000) := by
  have h := checkLog_sound (w := (172652375943 / 672652375943)) (n := 12)
    (lo := (525089117 / 1000000000)) (hi := (262544559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422652375943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422652375943 / 250000000000) = 1/(250000000000 / 422652375943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12411 : Bounds (525089117 / 1000000000) (262544559 / 500000000) (Real.log (422652375943 / 250000000000)) := by
  have h := reflection_log_12411_neg
  have he : Real.log (422652375943 / 250000000000) = -Real.log (250000000000 / 422652375943) := by
    rw [show ((422652375943 / 250000000000) : ℝ) = ((250000000000 / 422652375943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12412_neg : (1069490441 / 1000000000) ≤ -Real.log (250000000000 / 728473581213) ∧
    -Real.log (250000000000 / 728473581213) ≤ (1069490443 / 1000000000) := by
  have h := checkLog_sound (w := (228473581213 / 1228473581213)) (n := 12)
    (lo := (376343261 / 1000000000)) (hi := (188171631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728473581213 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(728473581213 / 500000000000) = 1/(250000000000 / 728473581213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12412 : Bounds (1069490441 / 1000000000) (1069490443 / 1000000000) (Real.log (728473581213 / 250000000000)) := by
  have h := reflection_log_12412_neg
  have he : Real.log (728473581213 / 250000000000) = -Real.log (250000000000 / 728473581213) := by
    rw [show ((728473581213 / 250000000000) : ℝ) = ((250000000000 / 728473581213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12413_neg : (33503771 / 31250000) ≤ -Real.log (250000000000 / 730392156863) ∧
    -Real.log (250000000000 / 730392156863) ≤ (536060337 / 500000000) := by
  have h := checkLog_sound (w := (230392156863 / 1230392156863)) (n := 12)
    (lo := (94743373 / 250000000)) (hi := (378973493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730392156863 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(730392156863 / 500000000000) = 1/(250000000000 / 730392156863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12413 : Bounds (33503771 / 31250000) (536060337 / 500000000) (Real.log (730392156863 / 250000000000)) := by
  have h := reflection_log_12413_neg
  have he : Real.log (730392156863 / 250000000000) = -Real.log (250000000000 / 730392156863) := by
    rw [show ((730392156863 / 250000000000) : ℝ) = ((250000000000 / 730392156863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12414_neg : (79889407 / 200000000) ≤ -Real.log (1000 / 1491) ∧
    -Real.log (1000 / 1491) ≤ (99861759 / 250000000) := by
  have h := checkLog_sound (w := (491 / 2491)) (n := 12)
    (lo := (79889407 / 200000000)) (hi := (99861759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491 / 1000) = 1/(1000 / 1491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12414 : Bounds (79889407 / 200000000) (99861759 / 250000000) (Real.log (1491 / 1000)) := by
  have h := reflection_log_12414_neg
  have he : Real.log (1491 / 1000) = -Real.log (1000 / 1491) := by
    rw [show ((1491 / 1000) : ℝ) = ((1000 / 1491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12415_neg : (337653631 / 500000000) ≤ -Real.log (509 / 1000) ∧
    -Real.log (509 / 1000) ≤ (675307263 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1509)) (n := 12)
    (lo := (337653631 / 500000000)) (hi := (675307263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 509) = 1/(509 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12415 : Bounds (-675307263 / 1000000000) (-337653631 / 500000000) (Real.log (509 / 1000)) := by
  have h := reflection_log_12415_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
