import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227
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

theorem reflection_log_1_neg : (477398097 / 1000000000) ≤ -Real.log (1600 / 2579) ∧
    -Real.log (1600 / 2579) ≤ (238699049 / 500000000) := by
  have h := checkLog_sound (w := (979 / 4179)) (n := 12)
    (lo := (477398097 / 1000000000)) (hi := (238699049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2579 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2579 / 1600) = 1/(1600 / 2579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (477398097 / 1000000000) (238699049 / 500000000) (Real.log (2579 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2579 / 1600) = -Real.log (1600 / 2579) := by
    rw [show ((2579 / 1600) : ℝ) = ((1600 / 2579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (37857113 / 40000000) ≤ -Real.log (621 / 1600) ∧
    -Real.log (621 / 1600) ≤ (946427827 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 621) = 1/(621 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-946427827 / 1000000000) (-37857113 / 40000000) (Real.log (621 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (470003629 / 1000000000) (47000363 / 100000000) (Real.log (8 / 5)) := by
  have h := reflection_log_3_neg
  have he : Real.log (8 / 5) = -Real.log (5 / 8) := by
    rw [show ((8 / 5) : ℝ) = ((5 / 8) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (916290731 / 1000000000) ≤ -Real.log (2 / 5) ∧
    -Real.log (2 / 5) ≤ (916290733 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 4) = 1/(2 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-916290733 / 1000000000) (-916290731 / 1000000000) (Real.log (2 / 5)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (100959957 / 500000000) ≤ -Real.log (800 / 979) ∧
    -Real.log (800 / 979) ≤ (40383983 / 200000000) := by
  have h := checkLog_sound (w := (179 / 1779)) (n := 12)
    (lo := (100959957 / 500000000)) (hi := (40383983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 800) = 1/(800 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (100959957 / 500000000) (40383983 / 200000000) (Real.log (979 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (979 / 800) = -Real.log (800 / 979) := by
    rw [show ((979 / 800) : ℝ) = ((800 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50656129 / 200000000) ≤ -Real.log (621 / 800) ∧
    -Real.log (621 / 800) ≤ (126640323 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 621) = 1/(621 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-126640323 / 500000000) (-50656129 / 200000000) (Real.log (621 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
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


theorem reflection_log_8 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (581916133 / 1000000000) ≤ -Real.log (125000 / 223683) ∧
    -Real.log (125000 / 223683) ≤ (290958067 / 500000000) := by
  have h := checkLog_sound (w := (98683 / 348683)) (n := 12)
    (lo := (581916133 / 1000000000)) (hi := (290958067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223683 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223683 / 125000) = 1/(125000 / 223683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (581916133 / 1000000000) (290958067 / 500000000) (Real.log (223683 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (223683 / 125000) = -Real.log (125000 / 223683) := by
    rw [show ((223683 / 125000) : ℝ) = ((125000 / 223683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1558098617 / 1000000000) ≤ -Real.log (26317 / 125000) ∧
    -Real.log (26317 / 125000) ≤ (77904931 / 50000000) := by
  have h := checkLog_sound (w := (4933 / 57567)) (n := 12)
    (lo := (171804257 / 1000000000)) (hi := (85902129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 26317) = 1/(26317 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77904931 / 50000000) (-1558098617 / 1000000000) (Real.log (26317 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (116649163 / 200000000) ≤ -Real.log (200000 / 358369) ∧
    -Real.log (200000 / 358369) ≤ (72905727 / 125000000) := by
  have h := checkLog_sound (w := (158369 / 558369)) (n := 12)
    (lo := (116649163 / 200000000)) (hi := (72905727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358369 / 200000) = 1/(200000 / 358369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (116649163 / 200000000) (72905727 / 125000000) (Real.log (358369 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (358369 / 200000) = -Real.log (200000 / 358369) := by
    rw [show ((358369 / 200000) : ℝ) = ((200000 / 358369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1569472283 / 1000000000) ≤ -Real.log (41631 / 200000) ∧
    -Real.log (41631 / 200000) ≤ (784736143 / 500000000) := by
  have h := checkLog_sound (w := (8369 / 91631)) (n := 12)
    (lo := (183177923 / 1000000000)) (hi := (45794481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41631) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 41631) = 1/(41631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-784736143 / 500000000) (-1569472283 / 1000000000) (Real.log (41631 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33923859 / 62500000) ≤ -Real.log (1000000 / 1720787) ∧
    -Real.log (1000000 / 1720787) ≤ (108556349 / 200000000) := by
  have h := checkLog_sound (w := (720787 / 2720787)) (n := 12)
    (lo := (33923859 / 62500000)) (hi := (108556349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1720787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1720787 / 1000000) = 1/(1000000 / 1720787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33923859 / 62500000) (108556349 / 200000000) (Real.log (1720787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1720787 / 1000000) = -Real.log (1000000 / 1720787) := by
    rw [show ((1720787 / 1000000) : ℝ) = ((1000000 / 1720787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1275780347 / 1000000000) ≤ -Real.log (279213 / 1000000) ∧
    -Real.log (279213 / 1000000) ≤ (1275780349 / 1000000000) := by
  have h := checkLog_sound (w := (220787 / 779213)) (n := 12)
    (lo := (582633167 / 1000000000)) (hi := (36414573 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 279213) = 1/(279213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1275780349 / 1000000000) (-1275780347 / 1000000000) (Real.log (279213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (547085033 / 1000000000) ≤ -Real.log (62500 / 108013) ∧
    -Real.log (62500 / 108013) ≤ (273542517 / 500000000) := by
  have h := checkLog_sound (w := (45513 / 170513)) (n := 12)
    (lo := (547085033 / 1000000000)) (hi := (273542517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108013 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108013 / 62500) = 1/(62500 / 108013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (547085033 / 1000000000) (273542517 / 500000000) (Real.log (108013 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (108013 / 62500) = -Real.log (62500 / 108013) := by
    rw [show ((108013 / 62500) : ℝ) = ((62500 / 108013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (130271821 / 100000000) ≤ -Real.log (16987 / 62500) ∧
    -Real.log (16987 / 62500) ≤ (325679553 / 250000000) := by
  have h := checkLog_sound (w := (14263 / 48237)) (n := 12)
    (lo := (60957103 / 100000000)) (hi := (609571031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 16987) = 1/(16987 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-325679553 / 250000000) (-130271821 / 100000000) (Real.log (16987 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2140014751 / 1000000000) ≤ -Real.log (10000000000 / 84995630201) ∧
    -Real.log (10000000000 / 84995630201) ≤ (428002951 / 200000000) := by
  have h := checkLog_sound (w := (4995630201 / 164995630201)) (n := 12)
    (lo := (60573211 / 1000000000)) (hi := (15143303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84995630201 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(84995630201 / 80000000000) = 1/(10000000000 / 84995630201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2140014751 / 1000000000) (428002951 / 200000000) (Real.log (84995630201 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84995630201 / 10000000000) = -Real.log (10000000000 / 84995630201) := by
    rw [show ((84995630201 / 10000000000) : ℝ) = ((10000000000 / 84995630201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1076359049 / 500000000) ≤ -Real.log (500000000000 / 4304112320147) ∧
    -Real.log (500000000000 / 4304112320147) ≤ (1076359051 / 500000000) := by
  have h := checkLog_sound (w := (304112320147 / 8304112320147)) (n := 12)
    (lo := (36638279 / 500000000)) (hi := (73276559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4304112320147 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4304112320147 / 4000000000000) = 1/(500000000000 / 4304112320147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1076359049 / 500000000) (1076359051 / 500000000) (Real.log (4304112320147 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4304112320147 / 500000000000) = -Real.log (500000000000 / 4304112320147) := by
    rw [show ((4304112320147 / 500000000000) : ℝ) = ((500000000000 / 4304112320147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (181856209 / 100000000) ≤ -Real.log (500000000000 / 3081495130957) ∧
    -Real.log (500000000000 / 3081495130957) ≤ (1818562093 / 1000000000) := by
  have h := checkLog_sound (w := (1081495130957 / 5081495130957)) (n := 12)
    (lo := (43226773 / 100000000)) (hi := (432267731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081495130957 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3081495130957 / 2000000000000) = 1/(500000000000 / 3081495130957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (181856209 / 100000000) (1818562093 / 1000000000) (Real.log (3081495130957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3081495130957 / 500000000000) = -Real.log (500000000000 / 3081495130957) := by
    rw [show ((3081495130957 / 500000000000) : ℝ) = ((500000000000 / 3081495130957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1849803243 / 1000000000) ≤ -Real.log (20000000000 / 127171366339) ∧
    -Real.log (20000000000 / 127171366339) ≤ (924901623 / 500000000) := by
  have h := checkLog_sound (w := (47171366339 / 207171366339)) (n := 12)
    (lo := (463508883 / 1000000000)) (hi := (115877221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127171366339 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(127171366339 / 80000000000) = 1/(20000000000 / 127171366339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1849803243 / 1000000000) (924901623 / 500000000) (Real.log (127171366339 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (127171366339 / 20000000000) = -Real.log (20000000000 / 127171366339) := by
    rw [show ((127171366339 / 20000000000) : ℝ) = ((20000000000 / 127171366339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227
