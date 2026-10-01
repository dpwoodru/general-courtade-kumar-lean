import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0188
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

theorem reflection_log_1_neg : (306620591 / 500000000) ≤ -Real.log (6400 / 11817) ∧
    -Real.log (6400 / 11817) ≤ (613241183 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 18217)) (n := 12)
    (lo := (306620591 / 500000000)) (hi := (613241183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817 / 6400) = 1/(6400 / 11817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (306620591 / 500000000) (613241183 / 1000000000) (Real.log (11817 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11817 / 6400) = -Real.log (6400 / 11817) := by
    rw [show ((11817 / 6400) : ℝ) = ((6400 / 11817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (468361037 / 250000000) ≤ -Real.log (983 / 6400) ∧
    -Real.log (983 / 6400) ≤ (1873444151 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 983) = 1/(983 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1873444151 / 1000000000) (-468361037 / 250000000) (Real.log (983 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (122326407 / 200000000) ≤ -Real.log (3200 / 5899) ∧
    -Real.log (3200 / 5899) ≤ (152908009 / 250000000) := by
  have h := checkLog_sound (w := (2699 / 9099)) (n := 12)
    (lo := (122326407 / 200000000)) (hi := (152908009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 3200) = 1/(3200 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (122326407 / 200000000) (152908009 / 250000000) (Real.log (5899 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5899 / 3200) = -Real.log (3200 / 5899) := by
    rw [show ((5899 / 3200) : ℝ) = ((3200 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (927149993 / 500000000) ≤ -Real.log (501 / 3200) ∧
    -Real.log (501 / 3200) ≤ (1854299989 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 501) = 1/(501 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1854299989 / 1000000000) (-927149993 / 500000000) (Real.log (501 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (263195673 / 500000000) ≤ -Real.log (3200 / 5417) ∧
    -Real.log (3200 / 5417) ≤ (526391347 / 1000000000) := by
  have h := checkLog_sound (w := (2217 / 8617)) (n := 12)
    (lo := (263195673 / 500000000)) (hi := (526391347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5417 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5417 / 3200) = 1/(3200 / 5417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (263195673 / 500000000) (526391347 / 1000000000) (Real.log (5417 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5417 / 3200) = -Real.log (3200 / 5417) := by
    rw [show ((5417 / 3200) : ℝ) = ((3200 / 5417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (147537121 / 125000000) ≤ -Real.log (983 / 3200) ∧
    -Real.log (983 / 3200) ≤ (118029697 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 983) = 1/(983 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118029697 / 100000000) (-147537121 / 125000000) (Real.log (983 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (65359713 / 125000000) ≤ -Real.log (1600 / 2699) ∧
    -Real.log (1600 / 2699) ≤ (104575541 / 200000000) := by
  have h := checkLog_sound (w := (1099 / 4299)) (n := 12)
    (lo := (65359713 / 125000000)) (hi := (104575541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2699 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2699 / 1600) = 1/(1600 / 2699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (65359713 / 125000000) (104575541 / 200000000) (Real.log (2699 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2699 / 1600) = -Real.log (1600 / 2699) := by
    rw [show ((2699 / 1600) : ℝ) = ((1600 / 2699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (580576403 / 500000000) ≤ -Real.log (501 / 1600) ∧
    -Real.log (501 / 1600) ≤ (145144101 / 125000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 501) = 1/(501 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-145144101 / 125000000) (-580576403 / 500000000) (Real.log (501 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (248081 / 390625) ≤ -Real.log (1000000 / 1887187) ∧
    -Real.log (1000000 / 1887187) ≤ (635087361 / 1000000000) := by
  have h := checkLog_sound (w := (887187 / 2887187)) (n := 12)
    (lo := (248081 / 390625)) (hi := (635087361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887187 / 1000000) = 1/(1000000 / 1887187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (248081 / 390625) (635087361 / 1000000000) (Real.log (1887187 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1887187 / 1000000) = -Real.log (1000000 / 1887187) := by
    rw [show ((1887187 / 1000000) : ℝ) = ((1000000 / 1887187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (136376481 / 62500000) ≤ -Real.log (112813 / 1000000) ∧
    -Real.log (112813 / 1000000) ≤ (21820237 / 10000000) := by
  have h := checkLog_sound (w := (12187 / 237813)) (n := 12)
    (lo := (25645539 / 250000000)) (hi := (102582157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112813) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 112813) = 1/(112813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21820237 / 10000000) (-136376481 / 62500000) (Real.log (112813 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (636031177 / 1000000000) ≤ -Real.log (1000000 / 1888969) ∧
    -Real.log (1000000 / 1888969) ≤ (318015589 / 500000000) := by
  have h := checkLog_sound (w := (888969 / 2888969)) (n := 12)
    (lo := (636031177 / 1000000000)) (hi := (318015589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1888969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1888969 / 1000000) = 1/(1000000 / 1888969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (636031177 / 1000000000) (318015589 / 500000000) (Real.log (1888969 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1888969 / 1000000) = -Real.log (1000000 / 1888969) := by
    rw [show ((1888969 / 1000000) : ℝ) = ((1000000 / 1888969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (439589167 / 200000000) ≤ -Real.log (111031 / 1000000) ∧
    -Real.log (111031 / 1000000) ≤ (2197945839 / 1000000000) := by
  have h := checkLog_sound (w := (13969 / 236031)) (n := 12)
    (lo := (23700859 / 200000000)) (hi := (14813037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 111031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 111031) = 1/(111031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2197945839 / 1000000000) (-439589167 / 200000000) (Real.log (111031 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315733219 / 500000000) ≤ -Real.log (500000 / 940183) ∧
    -Real.log (500000 / 940183) ≤ (631466439 / 1000000000) := by
  have h := checkLog_sound (w := (440183 / 1440183)) (n := 12)
    (lo := (315733219 / 500000000)) (hi := (631466439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940183 / 500000) = 1/(500000 / 940183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315733219 / 500000000) (631466439 / 1000000000) (Real.log (940183 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (940183 / 500000) = -Real.log (500000 / 940183) := by
    rw [show ((940183 / 500000) : ℝ) = ((500000 / 940183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (424663639 / 200000000) ≤ -Real.log (59817 / 500000) ∧
    -Real.log (59817 / 500000) ≤ (2123318199 / 1000000000) := by
  have h := checkLog_sound (w := (2683 / 122317)) (n := 12)
    (lo := (8775331 / 200000000)) (hi := (2742291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59817) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59817) = 1/(59817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2123318199 / 1000000000) (-424663639 / 200000000) (Real.log (59817 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158144061 / 250000000) ≤ -Real.log (500000 / 941227) ∧
    -Real.log (500000 / 941227) ≤ (126515249 / 200000000) := by
  have h := checkLog_sound (w := (441227 / 1441227)) (n := 12)
    (lo := (158144061 / 250000000)) (hi := (126515249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941227 / 500000) = 1/(500000 / 941227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158144061 / 250000000) (126515249 / 200000000) (Real.log (941227 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (941227 / 500000) = -Real.log (500000 / 941227) := by
    rw [show ((941227 / 500000) : ℝ) = ((500000 / 941227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (214092553 / 100000000) ≤ -Real.log (58773 / 500000) ∧
    -Real.log (58773 / 500000) ≤ (1070462767 / 500000000) := by
  have h := checkLog_sound (w := (3727 / 121273)) (n := 12)
    (lo := (6148399 / 100000000)) (hi := (61483991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58773) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 58773) = 1/(58773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1070462767 / 500000000) (-214092553 / 100000000) (Real.log (58773 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (176069441 / 62500000) ≤ -Real.log (250000000000 / 4182113320273) ∧
    -Real.log (250000000000 / 4182113320273) ≤ (2817111061 / 1000000000) := by
  have h := checkLog_sound (w := (182113320273 / 8182113320273)) (n := 12)
    (lo := (1391323 / 31250000)) (hi := (44522337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4182113320273 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4182113320273 / 4000000000000) = 1/(250000000000 / 4182113320273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (176069441 / 62500000) (2817111061 / 1000000000) (Real.log (4182113320273 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4182113320273 / 250000000000) = -Real.log (250000000000 / 4182113320273) := by
    rw [show ((4182113320273 / 250000000000) : ℝ) = ((250000000000 / 4182113320273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (708494253 / 250000000) ≤ -Real.log (100000000000 / 1701298736389) ∧
    -Real.log (100000000000 / 1701298736389) ≤ (2833977017 / 1000000000) := by
  have h := checkLog_sound (w := (101298736389 / 3301298736389)) (n := 12)
    (lo := (15347073 / 250000000)) (hi := (61388293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701298736389 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1701298736389 / 1600000000000) = 1/(100000000000 / 1701298736389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (708494253 / 250000000) (2833977017 / 1000000000) (Real.log (1701298736389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1701298736389 / 100000000000) = -Real.log (100000000000 / 1701298736389) := by
    rw [show ((1701298736389 / 100000000000) : ℝ) = ((100000000000 / 1701298736389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2754784633 / 1000000000) ≤ -Real.log (100000000000 / 1571765551599) ∧
    -Real.log (100000000000 / 1571765551599) ≤ (2754784637 / 1000000000) := by
  have h := checkLog_sound (w := (771765551599 / 2371765551599)) (n := 12)
    (lo := (675343093 / 1000000000)) (hi := (337671547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571765551599 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1571765551599 / 800000000000) = 1/(100000000000 / 1571765551599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2754784633 / 1000000000) (2754784637 / 1000000000) (Real.log (1571765551599 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1571765551599 / 100000000000) = -Real.log (100000000000 / 1571765551599) := by
    rw [show ((1571765551599 / 100000000000) : ℝ) = ((100000000000 / 1571765551599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (110940071 / 40000000) ≤ -Real.log (500000000000 / 8007307777381) ∧
    -Real.log (500000000000 / 8007307777381) ≤ (138675089 / 50000000) := by
  have h := checkLog_sound (w := (7307777381 / 16007307777381)) (n := 12)
    (lo := (182611 / 200000000)) (hi := (28533 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007307777381 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8007307777381 / 8000000000000) = 1/(500000000000 / 8007307777381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (110940071 / 40000000) (138675089 / 50000000) (Real.log (8007307777381 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8007307777381 / 500000000000) = -Real.log (500000000000 / 8007307777381) := by
    rw [show ((8007307777381 / 500000000000) : ℝ) = ((500000000000 / 8007307777381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0188
