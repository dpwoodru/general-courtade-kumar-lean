import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0191
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

theorem reflection_log_1_neg : (9506343 / 15625000) ≤ -Real.log (80 / 147) ∧
    -Real.log (80 / 147) ≤ (608405953 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 227)) (n := 12)
    (lo := (9506343 / 15625000)) (hi := (608405953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 80) = 1/(80 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9506343 / 15625000) (608405953 / 1000000000) (Real.log (147 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (147 / 80) = -Real.log (80 / 147) := by
    rw [show ((147 / 80) : ℝ) = ((80 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (454269319 / 250000000) ≤ -Real.log (13 / 80) ∧
    -Real.log (13 / 80) ≤ (1817077279 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20 / 13) = 1/(13 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1817077279 / 1000000000) (-454269319 / 250000000) (Real.log (13 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (606788999 / 1000000000) ≤ -Real.log (6400 / 11741) ∧
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


theorem reflection_log_3 : Bounds (606788999 / 1000000000) (606789 / 1000000) (Real.log (11741 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11741 / 6400) = -Real.log (6400 / 11741) := by
    rw [show ((11741 / 6400) : ℝ) = ((6400 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (899486461 / 500000000) ≤ -Real.log (1059 / 6400) ∧
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


theorem reflection_log_4 : Bounds (-71958917 / 40000000) (-899486461 / 500000000) (Real.log (1059 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103162633 / 200000000) ≤ -Real.log (40 / 67) ∧
    -Real.log (40 / 67) ≤ (257906583 / 500000000) := by
  have h := checkLog_sound (w := (27 / 107)) (n := 12)
    (lo := (103162633 / 200000000)) (hi := (257906583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67 / 40) = 1/(40 / 67) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103162633 / 200000000) (257906583 / 500000000) (Real.log (67 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (67 / 40) = -Real.log (40 / 67) := by
    rw [show ((67 / 40) : ℝ) = ((40 / 67) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70245631 / 62500000) ≤ -Real.log (13 / 40) ∧
    -Real.log (13 / 40) ≤ (561965049 / 500000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 13) = 1/(13 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-561965049 / 500000000) (-70245631 / 62500000) (Real.log (13 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (512262091 / 1000000000) ≤ -Real.log (3200 / 5341) ∧
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


theorem reflection_log_7 : Bounds (512262091 / 1000000000) (128065523 / 250000000) (Real.log (5341 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5341 / 3200) = -Real.log (3200 / 5341) := by
    rw [show ((5341 / 3200) : ℝ) = ((3200 / 5341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (552912871 / 500000000) ≤ -Real.log (1059 / 3200) ∧
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


theorem reflection_log_8 : Bounds (-69114109 / 62500000) (-552912871 / 500000000) (Real.log (1059 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (126458719 / 200000000) ≤ -Real.log (500000 / 940961) ∧
    -Real.log (500000 / 940961) ≤ (158073399 / 250000000) := by
  have h := checkLog_sound (w := (440961 / 1440961)) (n := 12)
    (lo := (126458719 / 200000000)) (hi := (158073399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940961 / 500000) = 1/(500000 / 940961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (126458719 / 200000000) (158073399 / 250000000) (Real.log (940961 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (940961 / 500000) = -Real.log (500000 / 940961) := by
    rw [show ((940961 / 500000) : ℝ) = ((500000 / 940961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1068204927 / 500000000) ≤ -Real.log (59039 / 500000) ∧
    -Real.log (59039 / 500000) ≤ (1068204929 / 500000000) := by
  have h := checkLog_sound (w := (3461 / 121539)) (n := 12)
    (lo := (28484157 / 500000000)) (hi := (11393663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59039) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59039) = 1/(59039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1068204929 / 500000000) (-1068204927 / 500000000) (Real.log (59039 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (633219347 / 1000000000) ≤ -Real.log (200000 / 376733) ∧
    -Real.log (200000 / 376733) ≤ (158304837 / 250000000) := by
  have h := checkLog_sound (w := (176733 / 576733)) (n := 12)
    (lo := (633219347 / 1000000000)) (hi := (158304837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376733 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376733 / 200000) = 1/(200000 / 376733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (633219347 / 1000000000) (158304837 / 250000000) (Real.log (376733 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376733 / 200000) = -Real.log (200000 / 376733) := by
    rw [show ((376733 / 200000) : ℝ) = ((200000 / 376733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2151281317 / 1000000000) ≤ -Real.log (23267 / 200000) ∧
    -Real.log (23267 / 200000) ≤ (2151281321 / 1000000000) := by
  have h := checkLog_sound (w := (1733 / 48267)) (n := 12)
    (lo := (71839777 / 1000000000)) (hi := (35919889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23267) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23267) = 1/(23267 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2151281321 / 1000000000) (-2151281317 / 1000000000) (Real.log (23267 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (628147753 / 1000000000) ≤ -Real.log (125000 / 234267) ∧
    -Real.log (125000 / 234267) ≤ (314073877 / 500000000) := by
  have h := checkLog_sound (w := (109267 / 359267)) (n := 12)
    (lo := (628147753 / 1000000000)) (hi := (314073877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234267 / 125000) = 1/(125000 / 234267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (628147753 / 1000000000) (314073877 / 500000000) (Real.log (234267 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (234267 / 125000) = -Real.log (125000 / 234267) := by
    rw [show ((234267 / 125000) : ℝ) = ((125000 / 234267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1036276659 / 500000000) ≤ -Real.log (15733 / 125000) ∧
    -Real.log (15733 / 125000) ≤ (2072553321 / 1000000000) := by
  have h := checkLog_sound (w := (15517 / 46983)) (n := 12)
    (lo := (343129479 / 500000000)) (hi := (686258959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15733) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 15733) = 1/(15733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2072553321 / 1000000000) (-1036276659 / 500000000) (Real.log (15733 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (629253251 / 1000000000) ≤ -Real.log (1000000 / 1876209) ∧
    -Real.log (1000000 / 1876209) ≤ (157313313 / 250000000) := by
  have h := checkLog_sound (w := (876209 / 2876209)) (n := 12)
    (lo := (629253251 / 1000000000)) (hi := (157313313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1876209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1876209 / 1000000) = 1/(1000000 / 1876209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (629253251 / 1000000000) (157313313 / 250000000) (Real.log (1876209 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1876209 / 1000000) = -Real.log (1000000 / 1876209) := by
    rw [show ((1876209 / 1000000) : ℝ) = ((1000000 / 1876209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2089160617 / 1000000000) ≤ -Real.log (123791 / 1000000) ∧
    -Real.log (123791 / 1000000) ≤ (2089160621 / 1000000000) := by
  have h := checkLog_sound (w := (1209 / 248791)) (n := 12)
    (lo := (9719077 / 1000000000)) (hi := (4859539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123791) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 123791) = 1/(123791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2089160621 / 1000000000) (-2089160617 / 1000000000) (Real.log (123791 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2768703449 / 1000000000) ≤ -Real.log (250000000000 / 3984489066549) ∧
    -Real.log (250000000000 / 3984489066549) ≤ (2768703453 / 1000000000) := by
  have h := checkLog_sound (w := (1984489066549 / 5984489066549)) (n := 12)
    (lo := (689261909 / 1000000000)) (hi := (68926191 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3984489066549 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3984489066549 / 2000000000000) = 1/(250000000000 / 3984489066549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2768703449 / 1000000000) (2768703453 / 1000000000) (Real.log (3984489066549 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3984489066549 / 250000000000) = -Real.log (250000000000 / 3984489066549) := by
    rw [show ((3984489066549 / 250000000000) : ℝ) = ((250000000000 / 3984489066549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2784500663 / 1000000000) ≤ -Real.log (500000000000 / 8095865388749) ∧
    -Real.log (500000000000 / 8095865388749) ≤ (696125167 / 250000000) := by
  have h := checkLog_sound (w := (95865388749 / 16095865388749)) (n := 12)
    (lo := (11911943 / 1000000000)) (hi := (1488993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8095865388749 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8095865388749 / 8000000000000) = 1/(500000000000 / 8095865388749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2784500663 / 1000000000) (696125167 / 250000000) (Real.log (8095865388749 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8095865388749 / 500000000000) = -Real.log (500000000000 / 8095865388749) := by
    rw [show ((8095865388749 / 500000000000) : ℝ) = ((500000000000 / 8095865388749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2700701071 / 1000000000) ≤ -Real.log (500000000000 / 7445083582279) ∧
    -Real.log (500000000000 / 7445083582279) ≤ (108028043 / 40000000) := by
  have h := checkLog_sound (w := (3445083582279 / 11445083582279)) (n := 12)
    (lo := (621259531 / 1000000000)) (hi := (155314883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7445083582279 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7445083582279 / 4000000000000) = 1/(500000000000 / 7445083582279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2700701071 / 1000000000) (108028043 / 40000000) (Real.log (7445083582279 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7445083582279 / 500000000000) = -Real.log (500000000000 / 7445083582279) := by
    rw [show ((7445083582279 / 500000000000) : ℝ) = ((500000000000 / 7445083582279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2718413869 / 1000000000) ≤ -Real.log (500000000000 / 7578131689703) ∧
    -Real.log (500000000000 / 7578131689703) ≤ (2718413873 / 1000000000) := by
  have h := checkLog_sound (w := (3578131689703 / 11578131689703)) (n := 12)
    (lo := (638972329 / 1000000000)) (hi := (63897233 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7578131689703 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7578131689703 / 4000000000000) = 1/(500000000000 / 7578131689703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2718413869 / 1000000000) (2718413873 / 1000000000) (Real.log (7578131689703 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7578131689703 / 500000000000) = -Real.log (500000000000 / 7578131689703) := by
    rw [show ((7578131689703 / 500000000000) : ℝ) = ((500000000000 / 7578131689703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0191
