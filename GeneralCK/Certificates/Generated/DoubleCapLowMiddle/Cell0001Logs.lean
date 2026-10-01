import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0001
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

theorem reflection_log_1_neg : (170762497 / 250000000) ≤ -Real.log (1000000000000 / 1979907226563) ∧
    -Real.log (1000000000000 / 1979907226563) ≤ (683049989 / 1000000000) := by
  have h := checkLog_sound (w := (979907226563 / 2979907226563)) (n := 12)
    (lo := (170762497 / 250000000)) (hi := (683049989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979907226563 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979907226563 / 1000000000000) = 1/(1000000000000 / 1979907226563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170762497 / 250000000) (683049989 / 1000000000) (Real.log (1979907226563 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979907226563 / 1000000000000) = -Real.log (1000000000000 / 1979907226563) := by
    rw [show ((1979907226563 / 1000000000000) : ℝ) = ((1000000000000 / 1979907226563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244212191 / 62500000) ≤ -Real.log (20092773437 / 1000000000000) ∧
    -Real.log (20092773437 / 1000000000000) ≤ (1953697531 / 500000000) := by
  have h := checkLog_sound (w := (11157226563 / 51342773437)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20092773437) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20092773437) = 1/(20092773437 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1953697531 / 500000000) (-244212191 / 62500000) (Real.log (20092773437 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (683003129 / 1000000000) ≤ -Real.log (102400 / 202733) ∧
    -Real.log (102400 / 202733) ≤ (68300313 / 100000000) := by
  have h := checkLog_sound (w := (100333 / 305133)) (n := 12)
    (lo := (683003129 / 1000000000)) (hi := (68300313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202733 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202733 / 102400) = 1/(102400 / 202733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (683003129 / 1000000000) (68300313 / 100000000) (Real.log (202733 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202733 / 102400) = -Real.log (102400 / 202733) := by
    rw [show ((202733 / 102400) : ℝ) = ((102400 / 202733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3902788429 / 1000000000) ≤ -Real.log (2067 / 102400) ∧
    -Real.log (2067 / 102400) ≤ (780557687 / 200000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2067) = 1/(2067 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-780557687 / 200000000) (-3902788429 / 1000000000) (Real.log (2067 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672849801 / 1000000000) ≤ -Real.log (20480 / 40137) ∧
    -Real.log (20480 / 40137) ≤ (336424901 / 500000000) := by
  have h := checkLog_sound (w := (19657 / 60617)) (n := 12)
    (lo := (672849801 / 1000000000)) (hi := (336424901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40137 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40137 / 20480) = 1/(20480 / 40137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672849801 / 1000000000) (336424901 / 500000000) (Real.log (40137 / 20480)) := by
  have h := reflection_log_5_neg
  have he : Real.log (40137 / 20480) = -Real.log (20480 / 40137) := by
    rw [show ((40137 / 20480) : ℝ) = ((20480 / 40137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (803561969 / 250000000) ≤ -Real.log (823 / 20480) ∧
    -Real.log (823 / 20480) ≤ (3214247881 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 823) = 1/(823 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3214247881 / 1000000000) (-803561969 / 250000000) (Real.log (823 / 20480)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672755121 / 1000000000) ≤ -Real.log (51200 / 100333) ∧
    -Real.log (51200 / 100333) ≤ (336377561 / 500000000) := by
  have h := checkLog_sound (w := (49133 / 151533)) (n := 12)
    (lo := (672755121 / 1000000000)) (hi := (336377561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100333 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100333 / 51200) = 1/(51200 / 100333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672755121 / 1000000000) (336377561 / 500000000) (Real.log (100333 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100333 / 51200) = -Real.log (51200 / 100333) := by
    rw [show ((100333 / 51200) : ℝ) = ((51200 / 100333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3209641249 / 1000000000) ≤ -Real.log (2067 / 51200) ∧
    -Real.log (2067 / 51200) ≤ (1604820627 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2067) = 1/(2067 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1604820627 / 500000000) (-3209641249 / 1000000000) (Real.log (2067 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (342263819 / 500000000) ≤ -Real.log (200000 / 396567) ∧
    -Real.log (200000 / 396567) ≤ (684527639 / 1000000000) := by
  have h := checkLog_sound (w := (196567 / 596567)) (n := 12)
    (lo := (342263819 / 500000000)) (hi := (684527639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396567 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396567 / 200000) = 1/(200000 / 396567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (342263819 / 500000000) (684527639 / 1000000000) (Real.log (396567 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (396567 / 200000) = -Real.log (200000 / 396567) := by
    rw [show ((396567 / 200000) : ℝ) = ((200000 / 396567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4064882849 / 1000000000) ≤ -Real.log (3433 / 200000) ∧
    -Real.log (3433 / 200000) ≤ (812976571 / 200000000) := by
  have h := checkLog_sound (w := (2817 / 9683)) (n := 12)
    (lo := (599146949 / 1000000000)) (hi := (11982939 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3433) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3433) = 1/(3433 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-812976571 / 200000000) (-4064882849 / 1000000000) (Real.log (3433 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684566471 / 1000000000) ≤ -Real.log (15625 / 30983) ∧
    -Real.log (15625 / 30983) ≤ (85570809 / 125000000) := by
  have h := checkLog_sound (w := (7679 / 23304)) (n := 12)
    (lo := (684566471 / 1000000000)) (hi := (85570809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30983 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30983 / 15625) = 1/(15625 / 30983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684566471 / 1000000000) (85570809 / 125000000) (Real.log (30983 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30983 / 15625) = -Real.log (15625 / 30983) := by
    rw [show ((30983 / 15625) : ℝ) = ((15625 / 30983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4069378813 / 1000000000) ≤ -Real.log (267 / 15625) ∧
    -Real.log (267 / 15625) ≤ (4069378819 / 1000000000) := by
  have h := checkLog_sound (w := (7081 / 24169)) (n := 12)
    (lo := (603642913 / 1000000000)) (hi := (301821457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8544) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8544) = 1/(267 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4069378819 / 1000000000) (-4069378813 / 1000000000) (Real.log (267 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136899173 / 200000000) ≤ -Real.log (250000 / 495693) ∧
    -Real.log (250000 / 495693) ≤ (342247933 / 500000000) := by
  have h := checkLog_sound (w := (245693 / 745693)) (n := 12)
    (lo := (136899173 / 200000000)) (hi := (342247933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495693 / 250000) = 1/(250000 / 495693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136899173 / 200000000) (342247933 / 500000000) (Real.log (495693 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (495693 / 250000) = -Real.log (250000 / 495693) := by
    rw [show ((495693 / 250000) : ℝ) = ((250000 / 495693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1015304827 / 250000000) ≤ -Real.log (4307 / 250000) ∧
    -Real.log (4307 / 250000) ≤ (2030609657 / 500000000) := by
  have h := checkLog_sound (w := (7011 / 24239)) (n := 12)
    (lo := (37217713 / 62500000)) (hi := (595483409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8614) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8614) = 1/(4307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2030609657 / 500000000) (-1015304827 / 250000000) (Real.log (4307 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684535203 / 1000000000) ≤ -Real.log (20000 / 39657) ∧
    -Real.log (20000 / 39657) ≤ (171133801 / 250000000) := by
  have h := checkLog_sound (w := (19657 / 59657)) (n := 12)
    (lo := (684535203 / 1000000000)) (hi := (171133801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39657 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39657 / 20000) = 1/(20000 / 39657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684535203 / 1000000000) (171133801 / 250000000) (Real.log (39657 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39657 / 20000) = -Real.log (20000 / 39657) := by
    rw [show ((39657 / 20000) : ℝ) = ((20000 / 39657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2032878551 / 500000000) ≤ -Real.log (343 / 20000) ∧
    -Real.log (343 / 20000) ≤ (1016439277 / 250000000) := by
  have h := checkLog_sound (w := (141 / 484)) (n := 12)
    (lo := (300010601 / 500000000)) (hi := (600021203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 343) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 343) = 1/(343 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1016439277 / 250000000) (-2032878551 / 500000000) (Real.log (343 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4749410487 / 1000000000) ≤ -Real.log (500000000000 / 57758083309059) ∧
    -Real.log (500000000000 / 57758083309059) ≤ (2374705247 / 500000000) := by
  have h := checkLog_sound (w := (25758083309059 / 89758083309059)) (n := 12)
    (lo := (590527407 / 1000000000)) (hi := (36907963 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57758083309059 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57758083309059 / 32000000000000) = 1/(500000000000 / 57758083309059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4749410487 / 1000000000) (2374705247 / 500000000) (Real.log (57758083309059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (57758083309059 / 500000000000) = -Real.log (500000000000 / 57758083309059) := by
    rw [show ((57758083309059 / 500000000000) : ℝ) = ((500000000000 / 57758083309059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1188486321 / 250000000) ≤ -Real.log (500000000000 / 58020599250937) ∧
    -Real.log (500000000000 / 58020599250937) ≤ (4753945291 / 1000000000) := by
  have h := checkLog_sound (w := (26020599250937 / 90020599250937)) (n := 12)
    (lo := (148765551 / 250000000)) (hi := (119012441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58020599250937 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(58020599250937 / 32000000000000) = 1/(500000000000 / 58020599250937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1188486321 / 250000000) (4753945291 / 1000000000) (Real.log (58020599250937 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (58020599250937 / 500000000000) = -Real.log (500000000000 / 58020599250937) := by
    rw [show ((58020599250937 / 500000000000) : ℝ) = ((500000000000 / 58020599250937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2372857587 / 500000000) ≤ -Real.log (500000000000 / 57545042953331) ∧
    -Real.log (500000000000 / 57545042953331) ≤ (4745715181 / 1000000000) := by
  have h := checkLog_sound (w := (25545042953331 / 89545042953331)) (n := 12)
    (lo := (293416047 / 500000000)) (hi := (117366419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57545042953331 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57545042953331 / 32000000000000) = 1/(500000000000 / 57545042953331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2372857587 / 500000000) (4745715181 / 1000000000) (Real.log (57545042953331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57545042953331 / 500000000000) = -Real.log (500000000000 / 57545042953331) := by
    rw [show ((57545042953331 / 500000000000) : ℝ) = ((500000000000 / 57545042953331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (950058461 / 200000000) ≤ -Real.log (4000000000 / 462472303207) ∧
    -Real.log (4000000000 / 462472303207) ≤ (593786539 / 125000000) := by
  have h := checkLog_sound (w := (206472303207 / 718472303207)) (n := 12)
    (lo := (23656369 / 40000000)) (hi := (295704613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462472303207 / 256000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(462472303207 / 256000000000) = 1/(4000000000 / 462472303207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (950058461 / 200000000) (593786539 / 125000000) (Real.log (462472303207 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (462472303207 / 4000000000) = -Real.log (4000000000 / 462472303207) := by
    rw [show ((462472303207 / 4000000000) : ℝ) = ((4000000000 / 462472303207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0001
