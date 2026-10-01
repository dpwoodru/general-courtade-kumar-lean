import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell093
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

theorem reflection_log_1_neg : (33282863 / 125000000) ≤ -Real.log (2560 / 3341) ∧
    -Real.log (2560 / 3341) ≤ (53252581 / 200000000) := by
  have h := checkLog_sound (w := (781 / 5901)) (n := 12)
    (lo := (33282863 / 125000000)) (hi := (53252581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3341 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3341 / 2560) = 1/(2560 / 3341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33282863 / 125000000) (53252581 / 200000000) (Real.log (3341 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3341 / 2560) = -Real.log (2560 / 3341) := by
    rw [show ((3341 / 2560) : ℝ) = ((2560 / 3341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (363955849 / 1000000000) ≤ -Real.log (1779 / 2560) ∧
    -Real.log (1779 / 2560) ≤ (7279117 / 20000000) := by
  have h := checkLog_sound (w := (781 / 4339)) (n := 12)
    (lo := (363955849 / 1000000000)) (hi := (7279117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1779) = 1/(1779 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7279117 / 20000000) (-363955849 / 1000000000) (Real.log (1779 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66453459 / 250000000) ≤ -Real.log (5120 / 6679) ∧
    -Real.log (5120 / 6679) ≤ (265813837 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 11799)) (n := 12)
    (lo := (66453459 / 250000000)) (hi := (265813837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6679 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6679 / 5120) = 1/(5120 / 6679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66453459 / 250000000) (265813837 / 1000000000) (Real.log (6679 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6679 / 5120) = -Real.log (5120 / 6679) := by
    rw [show ((6679 / 5120) : ℝ) = ((5120 / 6679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (181556517 / 500000000) ≤ -Real.log (3561 / 5120) ∧
    -Real.log (3561 / 5120) ≤ (72622607 / 200000000) := by
  have h := checkLog_sound (w := (1559 / 8681)) (n := 12)
    (lo := (181556517 / 500000000)) (hi := (72622607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3561) = 1/(3561 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72622607 / 200000000) (-181556517 / 500000000) (Real.log (3561 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (195709043 / 1000000000) ≤ -Real.log (1000000 / 1216173) ∧
    -Real.log (1000000 / 1216173) ≤ (48927261 / 250000000) := by
  have h := checkLog_sound (w := (216173 / 2216173)) (n := 12)
    (lo := (195709043 / 1000000000)) (hi := (48927261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216173 / 1000000) = 1/(1000000 / 1216173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (195709043 / 1000000000) (48927261 / 250000000) (Real.log (1216173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1216173 / 1000000) = -Real.log (1000000 / 1216173) := by
    rw [show ((1216173 / 1000000) : ℝ) = ((1000000 / 1216173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (121783473 / 500000000) ≤ -Real.log (783827 / 1000000) ∧
    -Real.log (783827 / 1000000) ≤ (243566947 / 1000000000) := by
  have h := checkLog_sound (w := (216173 / 1783827)) (n := 12)
    (lo := (121783473 / 500000000)) (hi := (243566947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783827) = 1/(783827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-243566947 / 1000000000) (-121783473 / 500000000) (Real.log (783827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196055151 / 1000000000) ≤ -Real.log (500000 / 608297) ∧
    -Real.log (500000 / 608297) ≤ (12253447 / 62500000) := by
  have h := checkLog_sound (w := (108297 / 1108297)) (n := 12)
    (lo := (196055151 / 1000000000)) (hi := (12253447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608297 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608297 / 500000) = 1/(500000 / 608297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196055151 / 1000000000) (12253447 / 62500000) (Real.log (608297 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (608297 / 500000) = -Real.log (500000 / 608297) := by
    rw [show ((608297 / 500000) : ℝ) = ((500000 / 608297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122052099 / 500000000) ≤ -Real.log (391703 / 500000) ∧
    -Real.log (391703 / 500000) ≤ (244104199 / 1000000000) := by
  have h := checkLog_sound (w := (108297 / 891703)) (n := 12)
    (lo := (122052099 / 500000000)) (hi := (244104199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391703) = 1/(391703 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-244104199 / 1000000000) (-122052099 / 500000000) (Real.log (391703 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (71990861 / 500000000) ≤ -Real.log (1000000 / 1154863) ∧
    -Real.log (1000000 / 1154863) ≤ (143981723 / 1000000000) := by
  have h := checkLog_sound (w := (154863 / 2154863)) (n := 12)
    (lo := (71990861 / 500000000)) (hi := (143981723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1154863 / 1000000) = 1/(1000000 / 1154863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (71990861 / 500000000) (143981723 / 1000000000) (Real.log (1154863 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1154863 / 1000000) = -Real.log (1000000 / 1154863) := by
    rw [show ((1154863 / 1000000) : ℝ) = ((1000000 / 1154863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84128267 / 500000000) ≤ -Real.log (845137 / 1000000) ∧
    -Real.log (845137 / 1000000) ≤ (33651307 / 200000000) := by
  have h := checkLog_sound (w := (154863 / 1845137)) (n := 12)
    (lo := (84128267 / 500000000)) (hi := (33651307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 845137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 845137) = 1/(845137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-33651307 / 200000000) (-84128267 / 500000000) (Real.log (845137 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576997 / 4000000) ≤ -Real.log (250000 / 288793) ∧
    -Real.log (250000 / 288793) ≤ (144249251 / 1000000000) := by
  have h := checkLog_sound (w := (38793 / 538793)) (n := 12)
    (lo := (576997 / 4000000)) (hi := (144249251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288793 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288793 / 250000) = 1/(250000 / 288793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576997 / 4000000) (144249251 / 1000000000) (Real.log (288793 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288793 / 250000) = -Real.log (250000 / 288793) := by
    rw [show ((288793 / 250000) : ℝ) = ((250000 / 288793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84311111 / 500000000) ≤ -Real.log (211207 / 250000) ∧
    -Real.log (211207 / 250000) ≤ (168622223 / 1000000000) := by
  have h := checkLog_sound (w := (38793 / 461207)) (n := 12)
    (lo := (84311111 / 500000000)) (hi := (168622223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211207) = 1/(211207 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-168622223 / 1000000000) (-84311111 / 500000000) (Real.log (211207 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (628926871 / 1000000000) ≤ -Real.log (125000000000 / 234449592811) ∧
    -Real.log (125000000000 / 234449592811) ≤ (78615859 / 125000000) := by
  have h := checkLog_sound (w := (109449592811 / 359449592811)) (n := 12)
    (lo := (628926871 / 1000000000)) (hi := (78615859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234449592811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234449592811 / 125000000000) = 1/(125000000000 / 234449592811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (628926871 / 1000000000) (78615859 / 125000000) (Real.log (234449592811 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (234449592811 / 125000000000) = -Real.log (125000000000 / 234449592811) := by
    rw [show ((234449592811 / 125000000000) : ℝ) = ((125000000000 / 234449592811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (315109377 / 500000000) ≤ -Real.log (250000000000 / 469505340079) ∧
    -Real.log (250000000000 / 469505340079) ≤ (126043751 / 200000000) := by
  have h := checkLog_sound (w := (219505340079 / 719505340079)) (n := 12)
    (lo := (315109377 / 500000000)) (hi := (126043751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469505340079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469505340079 / 250000000000) = 1/(250000000000 / 469505340079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (315109377 / 500000000) (126043751 / 200000000) (Real.log (469505340079 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (469505340079 / 250000000000) = -Real.log (250000000000 / 469505340079) := by
    rw [show ((469505340079 / 250000000000) : ℝ) = ((250000000000 / 469505340079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (439275989 / 1000000000) ≤ -Real.log (500000000000 / 775791724449) ∧
    -Real.log (500000000000 / 775791724449) ≤ (43927599 / 100000000) := by
  have h := checkLog_sound (w := (275791724449 / 1275791724449)) (n := 12)
    (lo := (439275989 / 1000000000)) (hi := (43927599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775791724449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775791724449 / 500000000000) = 1/(500000000000 / 775791724449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (439275989 / 1000000000) (43927599 / 100000000) (Real.log (775791724449 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (775791724449 / 500000000000) = -Real.log (500000000000 / 775791724449) := by
    rw [show ((775791724449 / 500000000000) : ℝ) = ((500000000000 / 775791724449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (440159349 / 1000000000) ≤ -Real.log (3125000000 / 4852983319) ∧
    -Real.log (3125000000 / 4852983319) ≤ (8803187 / 20000000) := by
  have h := checkLog_sound (w := (1727983319 / 7977983319)) (n := 12)
    (lo := (440159349 / 1000000000)) (hi := (8803187 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4852983319 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4852983319 / 3125000000) = 1/(3125000000 / 4852983319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (440159349 / 1000000000) (8803187 / 20000000) (Real.log (4852983319 / 3125000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4852983319 / 3125000000) = -Real.log (3125000000 / 4852983319) := by
    rw [show ((4852983319 / 3125000000) : ℝ) = ((3125000000 / 4852983319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (19514891 / 62500000) ≤ -Real.log (500000000000 / 683240113733) ∧
    -Real.log (500000000000 / 683240113733) ≤ (312238257 / 1000000000) := by
  have h := checkLog_sound (w := (183240113733 / 1183240113733)) (n := 12)
    (lo := (19514891 / 62500000)) (hi := (312238257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683240113733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683240113733 / 500000000000) = 1/(500000000000 / 683240113733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (19514891 / 62500000) (312238257 / 1000000000) (Real.log (683240113733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (683240113733 / 500000000000) = -Real.log (500000000000 / 683240113733) := by
    rw [show ((683240113733 / 500000000000) : ℝ) = ((500000000000 / 683240113733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (312871473 / 1000000000) ≤ -Real.log (50000000000 / 68367288963) ∧
    -Real.log (50000000000 / 68367288963) ≤ (156435737 / 500000000) := by
  have h := checkLog_sound (w := (18367288963 / 118367288963)) (n := 12)
    (lo := (312871473 / 1000000000)) (hi := (156435737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68367288963 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68367288963 / 50000000000) = 1/(50000000000 / 68367288963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (312871473 / 1000000000) (156435737 / 500000000) (Real.log (68367288963 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68367288963 / 50000000000) = -Real.log (50000000000 / 68367288963) := by
    rw [show ((68367288963 / 50000000000) : ℝ) = ((50000000000 / 68367288963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6093243 / 250000000) ≤ -Real.log (60995103151 / 62500000000) ∧
    -Real.log (60995103151 / 62500000000) ≤ (24372973 / 1000000000) := by
  have h := checkLog_sound (w := (1504896849 / 123495103151)) (n := 12)
    (lo := (6093243 / 250000000)) (hi := (24372973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60995103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60995103151) = 1/(60995103151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24372973 / 1000000000) (-6093243 / 250000000) (Real.log (60995103151 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6068703 / 250000000) ≤ -Real.log (976017451231 / 1000000000000) ∧
    -Real.log (976017451231 / 1000000000000) ≤ (24274813 / 1000000000) := by
  have h := checkLog_sound (w := (23982548769 / 1976017451231)) (n := 12)
    (lo := (6068703 / 250000000)) (hi := (24274813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976017451231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976017451231) = 1/(976017451231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24274813 / 1000000000) (-6068703 / 250000000) (Real.log (976017451231 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell093
