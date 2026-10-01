import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0092
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

theorem reflection_log_1_neg : (672924543 / 1000000000) ≤ -Real.log (1024 / 2007) ∧
    -Real.log (1024 / 2007) ≤ (5257223 / 7812500) := by
  have h := checkLog_sound (w := (983 / 3031)) (n := 12)
    (lo := (672924543 / 1000000000)) (hi := (5257223 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2007 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2007 / 1024) = 1/(1024 / 2007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672924543 / 1000000000) (5257223 / 7812500) (Real.log (2007 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2007 / 1024) = -Real.log (1024 / 2007) := by
    rw [show ((2007 / 1024) : ℝ) = ((1024 / 2007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (402237467 / 125000000) ≤ -Real.log (41 / 1024) ∧
    -Real.log (41 / 1024) ≤ (3217899741 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 41) = 1/(41 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3217899741 / 1000000000) (-402237467 / 125000000) (Real.log (41 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672735187 / 1000000000) ≤ -Real.log (51200 / 100331) ∧
    -Real.log (51200 / 100331) ≤ (168183797 / 250000000) := by
  have h := checkLog_sound (w := (49131 / 151531)) (n := 12)
    (lo := (672735187 / 1000000000)) (hi := (168183797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100331 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100331 / 51200) = 1/(51200 / 100331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672735187 / 1000000000) (168183797 / 250000000) (Real.log (100331 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100331 / 51200) = -Real.log (51200 / 100331) := by
    rw [show ((100331 / 51200) : ℝ) = ((51200 / 100331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3208674131 / 1000000000) ≤ -Real.log (2069 / 51200) ∧
    -Real.log (2069 / 51200) ≤ (401084267 / 125000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2069) = 1/(2069 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-401084267 / 125000000) (-3208674131 / 1000000000) (Real.log (2069 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (130456899 / 200000000) ≤ -Real.log (512 / 983) ∧
    -Real.log (512 / 983) ≤ (40767781 / 62500000) := by
  have h := checkLog_sound (w := (471 / 1495)) (n := 12)
    (lo := (130456899 / 200000000)) (hi := (40767781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 512) = 1/(512 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (130456899 / 200000000) (40767781 / 62500000) (Real.log (983 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (983 / 512) = -Real.log (512 / 983) := by
    rw [show ((983 / 512) : ℝ) = ((512 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (631188139 / 250000000) ≤ -Real.log (41 / 512) ∧
    -Real.log (41 / 512) ≤ (31559407 / 12500000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 41) = 1/(41 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31559407 / 12500000) (-631188139 / 250000000) (Real.log (41 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81487231 / 125000000) ≤ -Real.log (25600 / 49131) ∧
    -Real.log (25600 / 49131) ≤ (651897849 / 1000000000) := by
  have h := checkLog_sound (w := (23531 / 74731)) (n := 12)
    (lo := (81487231 / 125000000)) (hi := (651897849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49131 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49131 / 25600) = 1/(25600 / 49131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81487231 / 125000000) (651897849 / 1000000000) (Real.log (49131 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49131 / 25600) = -Real.log (25600 / 49131) := by
    rw [show ((49131 / 25600) : ℝ) = ((25600 / 49131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2515526951 / 1000000000) ≤ -Real.log (2069 / 25600) ∧
    -Real.log (2069 / 25600) ≤ (503105391 / 200000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2069) = 1/(2069 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-503105391 / 200000000) (-2515526951 / 1000000000) (Real.log (2069 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135275063 / 200000000) ≤ -Real.log (62500 / 122921) ∧
    -Real.log (62500 / 122921) ≤ (169093829 / 250000000) := by
  have h := checkLog_sound (w := (60421 / 185421)) (n := 12)
    (lo := (135275063 / 200000000)) (hi := (169093829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122921 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122921 / 62500) = 1/(62500 / 122921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135275063 / 200000000) (169093829 / 250000000) (Real.log (122921 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (122921 / 62500) = -Real.log (62500 / 122921) := by
    rw [show ((122921 / 62500) : ℝ) = ((62500 / 122921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (680655909 / 200000000) ≤ -Real.log (2079 / 62500) ∧
    -Real.log (2079 / 62500) ≤ (68065591 / 20000000) := by
  have h := checkLog_sound (w := (7309 / 23941)) (n := 12)
    (lo := (25227633 / 40000000)) (hi := (315345413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8316) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8316) = 1/(2079 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68065591 / 20000000) (-680655909 / 200000000) (Real.log (2079 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676522757 / 1000000000) ≤ -Real.log (500000 / 983513) ∧
    -Real.log (500000 / 983513) ≤ (338261379 / 500000000) := by
  have h := checkLog_sound (w := (483513 / 1483513)) (n := 12)
    (lo := (676522757 / 1000000000)) (hi := (338261379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983513 / 500000) = 1/(500000 / 983513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676522757 / 1000000000) (338261379 / 500000000) (Real.log (983513 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983513 / 500000) = -Real.log (500000 / 983513) := by
    rw [show ((983513 / 500000) : ℝ) = ((500000 / 983513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53313061 / 15625000) ≤ -Real.log (16487 / 500000) ∧
    -Real.log (16487 / 500000) ≤ (3412035909 / 1000000000) := by
  have h := checkLog_sound (w := (14763 / 47737)) (n := 12)
    (lo := (39965449 / 62500000)) (hi := (127889437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16487) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16487) = 1/(16487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3412035909 / 1000000000) (-53313061 / 15625000) (Real.log (16487 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676224801 / 1000000000) ≤ -Real.log (25000 / 49161) ∧
    -Real.log (25000 / 49161) ≤ (338112401 / 500000000) := by
  have h := checkLog_sound (w := (24161 / 74161)) (n := 12)
    (lo := (676224801 / 1000000000)) (hi := (338112401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49161 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49161 / 25000) = 1/(25000 / 49161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676224801 / 1000000000) (338112401 / 500000000) (Real.log (49161 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (49161 / 25000) = -Real.log (25000 / 49161) := by
    rw [show ((49161 / 25000) : ℝ) = ((25000 / 49161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (678884079 / 200000000) ≤ -Real.log (839 / 25000) ∧
    -Real.log (839 / 25000) ≤ (8486051 / 2500000) := by
  have h := checkLog_sound (w := (1447 / 4803)) (n := 12)
    (lo := (24873267 / 40000000)) (hi := (155457919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1678) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1678) = 1/(839 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8486051 / 2500000) (-678884079 / 200000000) (Real.log (839 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676374807 / 1000000000) ≤ -Real.log (200000 / 393347) ∧
    -Real.log (200000 / 393347) ≤ (84546851 / 125000000) := by
  have h := checkLog_sound (w := (193347 / 593347)) (n := 12)
    (lo := (676374807 / 1000000000)) (hi := (84546851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393347 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393347 / 200000) = 1/(200000 / 393347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676374807 / 1000000000) (84546851 / 125000000) (Real.log (393347 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393347 / 200000) = -Real.log (200000 / 393347) := by
    rw [show ((393347 / 200000) : ℝ) = ((200000 / 393347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3403249483 / 1000000000) ≤ -Real.log (6653 / 200000) ∧
    -Real.log (6653 / 200000) ≤ (212703093 / 62500000) := by
  have h := checkLog_sound (w := (5847 / 19153)) (n := 12)
    (lo := (630660763 / 1000000000)) (hi := (157665191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6653) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6653) = 1/(6653 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-212703093 / 62500000) (-3403249483 / 1000000000) (Real.log (6653 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (203982743 / 50000000) ≤ -Real.log (50000000000 / 2956253006253) ∧
    -Real.log (50000000000 / 2956253006253) ≤ (2039827433 / 500000000) := by
  have h := checkLog_sound (w := (1356253006253 / 4556253006253)) (n := 12)
    (lo := (7673987 / 12500000)) (hi := (613918961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2956253006253 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2956253006253 / 1600000000000) = 1/(50000000000 / 2956253006253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (203982743 / 50000000) (2039827433 / 500000000) (Real.log (2956253006253 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2956253006253 / 50000000000) = -Real.log (50000000000 / 2956253006253) := by
    rw [show ((2956253006253 / 50000000000) : ℝ) = ((50000000000 / 2956253006253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4088558661 / 1000000000) ≤ -Real.log (31250000000 / 1864182765209) ∧
    -Real.log (31250000000 / 1864182765209) ≤ (4088558667 / 1000000000) := by
  have h := checkLog_sound (w := (864182765209 / 2864182765209)) (n := 12)
    (lo := (622822761 / 1000000000)) (hi := (311411381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1864182765209 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1864182765209 / 1000000000000) = 1/(31250000000 / 1864182765209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4088558661 / 1000000000) (4088558667 / 1000000000) (Real.log (1864182765209 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1864182765209 / 31250000000) = -Real.log (31250000000 / 1864182765209) := by
    rw [show ((1864182765209 / 31250000000) : ℝ) = ((31250000000 / 1864182765209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (814129039 / 200000000) ≤ -Real.log (2000000000 / 117189511323) ∧
    -Real.log (2000000000 / 117189511323) ≤ (4070645201 / 1000000000) := by
  have h := checkLog_sound (w := (53189511323 / 181189511323)) (n := 12)
    (lo := (120981859 / 200000000)) (hi := (37806831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117189511323 / 64000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(117189511323 / 64000000000) = 1/(2000000000 / 117189511323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (814129039 / 200000000) (4070645201 / 1000000000) (Real.log (117189511323 / 2000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (117189511323 / 2000000000) = -Real.log (2000000000 / 117189511323) := by
    rw [show ((117189511323 / 2000000000) : ℝ) = ((2000000000 / 117189511323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (407962429 / 100000000) ≤ -Real.log (100000000000 / 5912325266797) ∧
    -Real.log (100000000000 / 5912325266797) ≤ (509953037 / 125000000) := by
  have h := checkLog_sound (w := (2712325266797 / 9112325266797)) (n := 12)
    (lo := (61388839 / 100000000)) (hi := (613888391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5912325266797 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5912325266797 / 3200000000000) = 1/(100000000000 / 5912325266797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (407962429 / 100000000) (509953037 / 125000000) (Real.log (5912325266797 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5912325266797 / 100000000000) = -Real.log (100000000000 / 5912325266797) := by
    rw [show ((5912325266797 / 100000000000) : ℝ) = ((100000000000 / 5912325266797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0092
