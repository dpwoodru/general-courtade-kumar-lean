import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215
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

theorem reflection_log_1_neg : (319589449 / 1000000000) ≤ -Real.log (640 / 881) ∧
    -Real.log (640 / 881) ≤ (6391789 / 20000000) := by
  have h := checkLog_sound (w := (241 / 1521)) (n := 12)
    (lo := (319589449 / 1000000000)) (hi := (6391789 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881 / 640) = 1/(640 / 881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319589449 / 1000000000) (6391789 / 20000000) (Real.log (881 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (881 / 640) = -Real.log (640 / 881) := by
    rw [show ((881 / 640) : ℝ) = ((640 / 881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (472506759 / 1000000000) ≤ -Real.log (399 / 640) ∧
    -Real.log (399 / 640) ≤ (11812669 / 25000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 399) = 1/(399 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) (Real.log (399 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (159581853 / 500000000) ≤ -Real.log (1024 / 1409) ∧
    -Real.log (1024 / 1409) ≤ (319163707 / 1000000000) := by
  have h := checkLog_sound (w := (385 / 2433)) (n := 12)
    (lo := (159581853 / 500000000)) (hi := (319163707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1024) = 1/(1024 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (159581853 / 500000000) (319163707 / 1000000000) (Real.log (1409 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1409 / 1024) = -Real.log (1024 / 1409) := by
    rw [show ((1409 / 1024) : ℝ) = ((1024 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (471567351 / 1000000000) ≤ -Real.log (639 / 1024) ∧
    -Real.log (639 / 1024) ≤ (58945919 / 125000000) := by
  have h := checkLog_sound (w := (385 / 1663)) (n := 12)
    (lo := (471567351 / 1000000000)) (hi := (58945919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 639) = 1/(639 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) (Real.log (639 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47412447 / 200000000) ≤ -Real.log (3125 / 3961) ∧
    -Real.log (3125 / 3961) ≤ (59265559 / 250000000) := by
  have h := checkLog_sound (w := (418 / 3543)) (n := 12)
    (lo := (47412447 / 200000000)) (hi := (59265559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3961 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3961 / 3125) = 1/(3125 / 3961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47412447 / 200000000) (59265559 / 250000000) (Real.log (3961 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3961 / 3125) = -Real.log (3125 / 3961) := by
    rw [show ((3961 / 3125) : ℝ) = ((3125 / 3961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155659621 / 500000000) ≤ -Real.log (2289 / 3125) ∧
    -Real.log (2289 / 3125) ≤ (311319243 / 1000000000) := by
  have h := checkLog_sound (w := (418 / 2707)) (n := 12)
    (lo := (155659621 / 500000000)) (hi := (311319243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2289) = 1/(2289 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-311319243 / 1000000000) (-155659621 / 500000000) (Real.log (2289 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (237396691 / 1000000000) ≤ -Real.log (125000 / 158493) ∧
    -Real.log (125000 / 158493) ≤ (59349173 / 250000000) := by
  have h := checkLog_sound (w := (33493 / 283493)) (n := 12)
    (lo := (237396691 / 1000000000)) (hi := (59349173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158493 / 125000) = 1/(125000 / 158493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (237396691 / 1000000000) (59349173 / 250000000) (Real.log (158493 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158493 / 125000) = -Real.log (125000 / 158493) := by
    rw [show ((158493 / 125000) : ℝ) = ((125000 / 158493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62379653 / 200000000) ≤ -Real.log (91507 / 125000) ∧
    -Real.log (91507 / 125000) ≤ (155949133 / 500000000) := by
  have h := checkLog_sound (w := (33493 / 216507)) (n := 12)
    (lo := (62379653 / 200000000)) (hi := (155949133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91507) = 1/(91507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-155949133 / 500000000) (-62379653 / 200000000) (Real.log (91507 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (176463599 / 1000000000) ≤ -Real.log (1000000 / 1192991) ∧
    -Real.log (1000000 / 1192991) ≤ (441159 / 2500000) := by
  have h := checkLog_sound (w := (192991 / 2192991)) (n := 12)
    (lo := (176463599 / 1000000000)) (hi := (441159 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192991 / 1000000) = 1/(1000000 / 1192991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (176463599 / 1000000000) (441159 / 2500000) (Real.log (1192991 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1192991 / 1000000) = -Real.log (1000000 / 1192991) := by
    rw [show ((1192991 / 1000000) : ℝ) = ((1000000 / 1192991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107210229 / 500000000) ≤ -Real.log (807009 / 1000000) ∧
    -Real.log (807009 / 1000000) ≤ (214420459 / 1000000000) := by
  have h := checkLog_sound (w := (192991 / 1807009)) (n := 12)
    (lo := (107210229 / 500000000)) (hi := (214420459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807009) = 1/(807009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214420459 / 1000000000) (-107210229 / 500000000) (Real.log (807009 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4418253 / 25000000) ≤ -Real.log (1000000 / 1193309) ∧
    -Real.log (1000000 / 1193309) ≤ (176730121 / 1000000000) := by
  have h := checkLog_sound (w := (193309 / 2193309)) (n := 12)
    (lo := (4418253 / 25000000)) (hi := (176730121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193309 / 1000000) = 1/(1000000 / 1193309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4418253 / 25000000) (176730121 / 1000000000) (Real.log (1193309 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1193309 / 1000000) = -Real.log (1000000 / 1193309) := by
    rw [show ((1193309 / 1000000) : ℝ) = ((1000000 / 1193309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214814583 / 1000000000) ≤ -Real.log (806691 / 1000000) ∧
    -Real.log (806691 / 1000000) ≤ (26851823 / 125000000) := by
  have h := checkLog_sound (w := (193309 / 1806691)) (n := 12)
    (lo := (214814583 / 1000000000)) (hi := (26851823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806691) = 1/(806691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-26851823 / 125000000) (-214814583 / 1000000000) (Real.log (806691 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49420691 / 62500000) ≤ -Real.log (500000000000 / 1102503912363) ∧
    -Real.log (500000000000 / 1102503912363) ≤ (395365529 / 500000000) := by
  have h := checkLog_sound (w := (102503912363 / 2102503912363)) (n := 12)
    (lo := (24395969 / 250000000)) (hi := (97583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102503912363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1102503912363 / 1000000000000) = 1/(500000000000 / 1102503912363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49420691 / 62500000) (395365529 / 500000000) (Real.log (1102503912363 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1102503912363 / 500000000000) = -Real.log (500000000000 / 1102503912363) := by
    rw [show ((1102503912363 / 500000000000) : ℝ) = ((500000000000 / 1102503912363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49506013 / 62500000) ≤ -Real.log (500000000000 / 1104010025063) ∧
    -Real.log (500000000000 / 1104010025063) ≤ (79209621 / 100000000) := by
  have h := checkLog_sound (w := (104010025063 / 2104010025063)) (n := 12)
    (lo := (24737257 / 250000000)) (hi := (98949029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104010025063 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1104010025063 / 1000000000000) = 1/(500000000000 / 1104010025063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (49506013 / 62500000) (79209621 / 100000000) (Real.log (1104010025063 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1104010025063 / 500000000000) = -Real.log (500000000000 / 1104010025063) := by
    rw [show ((1104010025063 / 500000000000) : ℝ) = ((500000000000 / 1104010025063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (548381477 / 1000000000) ≤ -Real.log (250000000000 / 432612494539) ∧
    -Real.log (250000000000 / 432612494539) ≤ (274190739 / 500000000) := by
  have h := checkLog_sound (w := (182612494539 / 682612494539)) (n := 12)
    (lo := (548381477 / 1000000000)) (hi := (274190739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432612494539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432612494539 / 250000000000) = 1/(250000000000 / 432612494539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (548381477 / 1000000000) (274190739 / 500000000) (Real.log (432612494539 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (432612494539 / 250000000000) = -Real.log (250000000000 / 432612494539) := by
    rw [show ((432612494539 / 250000000000) : ℝ) = ((250000000000 / 432612494539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (137323739 / 250000000) ≤ -Real.log (100000000000 / 173203142929) ∧
    -Real.log (100000000000 / 173203142929) ≤ (549294957 / 1000000000) := by
  have h := checkLog_sound (w := (73203142929 / 273203142929)) (n := 12)
    (lo := (137323739 / 250000000)) (hi := (549294957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173203142929 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173203142929 / 100000000000) = 1/(100000000000 / 173203142929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (137323739 / 250000000) (549294957 / 1000000000) (Real.log (173203142929 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (173203142929 / 100000000000) = -Real.log (100000000000 / 173203142929) := by
    rw [show ((173203142929 / 100000000000) : ℝ) = ((100000000000 / 173203142929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (390884057 / 1000000000) ≤ -Real.log (500000000000 / 739143553541) ∧
    -Real.log (500000000000 / 739143553541) ≤ (195442029 / 500000000) := by
  have h := checkLog_sound (w := (239143553541 / 1239143553541)) (n := 12)
    (lo := (390884057 / 1000000000)) (hi := (195442029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739143553541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739143553541 / 500000000000) = 1/(500000000000 / 739143553541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (390884057 / 1000000000) (195442029 / 500000000) (Real.log (739143553541 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (739143553541 / 500000000000) = -Real.log (500000000000 / 739143553541) := by
    rw [show ((739143553541 / 500000000000) : ℝ) = ((500000000000 / 739143553541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3058943 / 7812500) ≤ -Real.log (500000000000 / 739632027629) ∧
    -Real.log (500000000000 / 739632027629) ≤ (78308941 / 200000000) := by
  have h := checkLog_sound (w := (239632027629 / 1239632027629)) (n := 12)
    (lo := (3058943 / 7812500)) (hi := (78308941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739632027629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739632027629 / 500000000000) = 1/(500000000000 / 739632027629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3058943 / 7812500) (78308941 / 200000000) (Real.log (739632027629 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (739632027629 / 500000000000) = -Real.log (500000000000 / 739632027629) := by
    rw [show ((739632027629 / 500000000000) : ℝ) = ((500000000000 / 739632027629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38084463 / 1000000000) ≤ -Real.log (962631630519 / 1000000000000) ∧
    -Real.log (962631630519 / 1000000000000) ≤ (2380279 / 62500000) := by
  have h := checkLog_sound (w := (37368369481 / 1962631630519)) (n := 12)
    (lo := (38084463 / 1000000000)) (hi := (2380279 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962631630519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962631630519) = 1/(962631630519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2380279 / 62500000) (-38084463 / 1000000000) (Real.log (962631630519 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37956859 / 1000000000) ≤ -Real.log (962754473919 / 1000000000000) ∧
    -Real.log (962754473919 / 1000000000000) ≤ (1897843 / 50000000) := by
  have h := checkLog_sound (w := (37245526081 / 1962754473919)) (n := 12)
    (lo := (37956859 / 1000000000)) (hi := (1897843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962754473919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962754473919) = 1/(962754473919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1897843 / 50000000) (-37956859 / 1000000000) (Real.log (962754473919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215
