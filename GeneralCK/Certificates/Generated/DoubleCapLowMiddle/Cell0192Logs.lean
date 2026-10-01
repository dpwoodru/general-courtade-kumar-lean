import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0192
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

theorem reflection_log_1_neg : (606788999 / 1000000000) ≤ -Real.log (6400 / 11741) ∧
    -Real.log (6400 / 11741) ≤ (606789 / 1000000) := by
  have h := checkLog_sound (w := (5341 / 18141)) (n := 12)
    (lo := (606788999 / 1000000000)) (hi := (606789 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11741 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11741 / 6400) = 1/(6400 / 11741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (606788999 / 1000000000) (606789 / 1000000) (Real.log (11741 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11741 / 6400) = -Real.log (6400 / 11741) := by
    rw [show ((11741 / 6400) : ℝ) = ((6400 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (899486461 / 500000000) ≤ -Real.log (1059 / 6400) ∧
    -Real.log (1059 / 6400) ≤ (71958917 / 40000000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1059) = 1/(1059 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71958917 / 40000000) (-899486461 / 500000000) (Real.log (1059 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (605169427 / 1000000000) ≤ -Real.log (3200 / 5861) ∧
    -Real.log (3200 / 5861) ≤ (151292357 / 250000000) := by
  have h := checkLog_sound (w := (2661 / 9061)) (n := 12)
    (lo := (605169427 / 1000000000)) (hi := (151292357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861 / 3200) = 1/(3200 / 5861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (605169427 / 1000000000) (151292357 / 250000000) (Real.log (5861 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5861 / 3200) = -Real.log (3200 / 5861) := by
    rw [show ((5861 / 3200) : ℝ) = ((3200 / 5861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445297629 / 250000000) ≤ -Real.log (539 / 3200) ∧
    -Real.log (539 / 3200) ≤ (1781190519 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 539) = 1/(539 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1781190519 / 1000000000) (-445297629 / 250000000) (Real.log (539 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (512262091 / 1000000000) ≤ -Real.log (3200 / 5341) ∧
    -Real.log (3200 / 5341) ≤ (128065523 / 250000000) := by
  have h := checkLog_sound (w := (2141 / 8541)) (n := 12)
    (lo := (512262091 / 1000000000)) (hi := (128065523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5341 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5341 / 3200) = 1/(3200 / 5341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (512262091 / 1000000000) (128065523 / 250000000) (Real.log (5341 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5341 / 3200) = -Real.log (3200 / 5341) := by
    rw [show ((5341 / 3200) : ℝ) = ((3200 / 5341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (552912871 / 500000000) ≤ -Real.log (1059 / 3200) ∧
    -Real.log (1059 / 3200) ≤ (69114109 / 62500000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1059) = 1/(1059 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-69114109 / 62500000) (-552912871 / 500000000) (Real.log (1059 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (254349181 / 500000000) ≤ -Real.log (1600 / 2661) ∧
    -Real.log (1600 / 2661) ≤ (508698363 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 4261)) (n := 12)
    (lo := (254349181 / 500000000)) (hi := (508698363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2661 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2661 / 1600) = 1/(1600 / 2661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (254349181 / 500000000) (508698363 / 1000000000) (Real.log (2661 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2661 / 1600) = -Real.log (1600 / 2661) := by
    rw [show ((2661 / 1600) : ℝ) = ((1600 / 2661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (136005417 / 125000000) ≤ -Real.log (539 / 1600) ∧
    -Real.log (539 / 1600) ≤ (544021669 / 500000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 539) = 1/(539 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-544021669 / 500000000) (-136005417 / 125000000) (Real.log (539 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (631374963 / 1000000000) ≤ -Real.log (500000 / 940097) ∧
    -Real.log (500000 / 940097) ≤ (157843741 / 250000000) := by
  have h := checkLog_sound (w := (440097 / 1440097)) (n := 12)
    (lo := (631374963 / 1000000000)) (hi := (157843741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940097 / 500000) = 1/(500000 / 940097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (631374963 / 1000000000) (157843741 / 250000000) (Real.log (940097 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (940097 / 500000) = -Real.log (500000 / 940097) := by
    rw [show ((940097 / 500000) : ℝ) = ((500000 / 940097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2121881509 / 1000000000) ≤ -Real.log (59903 / 500000) ∧
    -Real.log (59903 / 500000) ≤ (2121881513 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 122403)) (n := 12)
    (lo := (42439969 / 1000000000)) (hi := (4243997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59903) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59903) = 1/(59903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2121881513 / 1000000000) (-2121881509 / 1000000000) (Real.log (59903 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (316147063 / 500000000) ≤ -Real.log (1000000 / 1881923) ∧
    -Real.log (1000000 / 1881923) ≤ (632294127 / 1000000000) := by
  have h := checkLog_sound (w := (881923 / 2881923)) (n := 12)
    (lo := (316147063 / 500000000)) (hi := (632294127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881923 / 1000000) = 1/(1000000 / 1881923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (316147063 / 500000000) (632294127 / 1000000000) (Real.log (1881923 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1881923 / 1000000) = -Real.log (1000000 / 1881923) := by
    rw [show ((1881923 / 1000000) : ℝ) = ((1000000 / 1881923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2136418323 / 1000000000) ≤ -Real.log (118077 / 1000000) ∧
    -Real.log (118077 / 1000000) ≤ (2136418327 / 1000000000) := by
  have h := checkLog_sound (w := (6923 / 243077)) (n := 12)
    (lo := (56976783 / 1000000000)) (hi := (3561049 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118077) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 118077) = 1/(118077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2136418327 / 1000000000) (-2136418323 / 1000000000) (Real.log (118077 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (313521851 / 500000000) ≤ -Real.log (250000 / 468017) ∧
    -Real.log (250000 / 468017) ≤ (627043703 / 1000000000) := by
  have h := checkLog_sound (w := (218017 / 718017)) (n := 12)
    (lo := (313521851 / 500000000)) (hi := (627043703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468017 / 250000) = 1/(250000 / 468017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (313521851 / 500000000) (627043703 / 1000000000) (Real.log (468017 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (468017 / 250000) = -Real.log (250000 / 468017) := by
    rw [show ((468017 / 250000) : ℝ) = ((250000 / 468017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (411251281 / 200000000) ≤ -Real.log (31983 / 250000) ∧
    -Real.log (31983 / 250000) ≤ (257032051 / 125000000) := by
  have h := checkLog_sound (w := (30517 / 94483)) (n := 12)
    (lo := (133992409 / 200000000)) (hi := (334981023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 31983) = 1/(31983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-257032051 / 125000000) (-411251281 / 200000000) (Real.log (31983 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (314074143 / 500000000) ≤ -Real.log (1000000 / 1874137) ∧
    -Real.log (1000000 / 1874137) ≤ (628148287 / 1000000000) := by
  have h := checkLog_sound (w := (874137 / 2874137)) (n := 12)
    (lo := (314074143 / 500000000)) (hi := (628148287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1874137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1874137 / 1000000) = 1/(1000000 / 1874137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (314074143 / 500000000) (628148287 / 1000000000) (Real.log (1874137 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1874137 / 1000000) = -Real.log (1000000 / 1874137) := by
    rw [show ((1874137 / 1000000) : ℝ) = ((1000000 / 1874137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (129535079 / 62500000) ≤ -Real.log (125863 / 1000000) ∧
    -Real.log (125863 / 1000000) ≤ (2072561267 / 1000000000) := by
  have h := checkLog_sound (w := (124137 / 375863)) (n := 12)
    (lo := (85783363 / 125000000)) (hi := (137253381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125863) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 125863) = 1/(125863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2072561267 / 1000000000) (-129535079 / 62500000) (Real.log (125863 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (344157059 / 125000000) ≤ -Real.log (125000000000 / 1961706842729) ∧
    -Real.log (125000000000 / 1961706842729) ≤ (688314119 / 250000000) := by
  have h := checkLog_sound (w := (961706842729 / 2961706842729)) (n := 12)
    (lo := (168453733 / 250000000)) (hi := (673814933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961706842729 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1961706842729 / 1000000000000) = 1/(125000000000 / 1961706842729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (344157059 / 125000000) (688314119 / 250000000) (Real.log (1961706842729 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1961706842729 / 125000000000) = -Real.log (125000000000 / 1961706842729) := by
    rw [show ((1961706842729 / 125000000000) : ℝ) = ((125000000000 / 1961706842729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2768712449 / 1000000000) ≤ -Real.log (500000000000 / 7969049857297) ∧
    -Real.log (500000000000 / 7969049857297) ≤ (2768712453 / 1000000000) := by
  have h := checkLog_sound (w := (3969049857297 / 11969049857297)) (n := 12)
    (lo := (689270909 / 1000000000)) (hi := (68927091 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7969049857297 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7969049857297 / 4000000000000) = 1/(500000000000 / 7969049857297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2768712449 / 1000000000) (2768712453 / 1000000000) (Real.log (7969049857297 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7969049857297 / 500000000000) = -Real.log (500000000000 / 7969049857297) := by
    rw [show ((7969049857297 / 500000000000) : ℝ) = ((500000000000 / 7969049857297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1341650053 / 500000000) ≤ -Real.log (500000000000 / 7316652596691) ∧
    -Real.log (500000000000 / 7316652596691) ≤ (268330011 / 100000000) := by
  have h := checkLog_sound (w := (3316652596691 / 11316652596691)) (n := 12)
    (lo := (301929283 / 500000000)) (hi := (603858567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7316652596691 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7316652596691 / 4000000000000) = 1/(500000000000 / 7316652596691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1341650053 / 500000000) (268330011 / 100000000) (Real.log (7316652596691 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7316652596691 / 500000000000) = -Real.log (500000000000 / 7316652596691) := by
    rw [show ((7316652596691 / 500000000000) : ℝ) = ((500000000000 / 7316652596691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (54014191 / 20000000) ≤ -Real.log (250000000000 / 3722573353567) ∧
    -Real.log (250000000000 / 3722573353567) ≤ (1350354777 / 500000000) := by
  have h := checkLog_sound (w := (1722573353567 / 5722573353567)) (n := 12)
    (lo := (62126801 / 100000000)) (hi := (621268011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3722573353567 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3722573353567 / 2000000000000) = 1/(250000000000 / 3722573353567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (54014191 / 20000000) (1350354777 / 500000000) (Real.log (3722573353567 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3722573353567 / 250000000000) = -Real.log (250000000000 / 3722573353567) := by
    rw [show ((3722573353567 / 250000000000) : ℝ) = ((250000000000 / 3722573353567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0192
