import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0010
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

theorem reflection_log_1_neg : (341314091 / 500000000) ≤ -Real.log (102400 / 202657) ∧
    -Real.log (102400 / 202657) ≤ (682628183 / 1000000000) := by
  have h := checkLog_sound (w := (100257 / 305057)) (n := 12)
    (lo := (341314091 / 500000000)) (hi := (682628183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202657 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202657 / 102400) = 1/(102400 / 202657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341314091 / 500000000) (682628183 / 1000000000) (Real.log (202657 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202657 / 102400) = -Real.log (102400 / 202657) := by
    rw [show ((202657 / 102400) : ℝ) = ((102400 / 202657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3866679993 / 1000000000) ≤ -Real.log (2143 / 102400) ∧
    -Real.log (2143 / 102400) ≤ (3866679999 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2143) = 1/(2143 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3866679999 / 1000000000) (-3866679993 / 1000000000) (Real.log (2143 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682581303 / 1000000000) ≤ -Real.log (1000000000000 / 1978979492187) ∧
    -Real.log (1000000000000 / 1978979492187) ≤ (85322663 / 125000000) := by
  have h := checkLog_sound (w := (978979492187 / 2978979492187)) (n := 12)
    (lo := (682581303 / 1000000000)) (hi := (85322663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978979492187 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978979492187 / 1000000000000) = 1/(1000000000000 / 1978979492187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682581303 / 1000000000) (85322663 / 125000000) (Real.log (1978979492187 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1978979492187 / 1000000000000) = -Real.log (1000000000000 / 1978979492187) := by
    rw [show ((1978979492187 / 1000000000000) : ℝ) = ((1000000000000 / 1978979492187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241391047 / 62500000) ≤ -Real.log (21020507813 / 1000000000000) ∧
    -Real.log (21020507813 / 1000000000000) ≤ (1931128379 / 500000000) := by
  have h := checkLog_sound (w := (10229492187 / 52270507813)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 21020507813) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 21020507813) = 1/(21020507813 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1931128379 / 500000000) (-241391047 / 62500000) (Real.log (21020507813 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671997357 / 1000000000) ≤ -Real.log (51200 / 100257) ∧
    -Real.log (51200 / 100257) ≤ (335998679 / 500000000) := by
  have h := checkLog_sound (w := (49057 / 151457)) (n := 12)
    (lo := (671997357 / 1000000000)) (hi := (335998679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100257 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100257 / 51200) = 1/(51200 / 100257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671997357 / 1000000000) (335998679 / 500000000) (Real.log (100257 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100257 / 51200) = -Real.log (51200 / 100257) := by
    rw [show ((100257 / 51200) : ℝ) = ((51200 / 100257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3173532813 / 1000000000) ≤ -Real.log (2143 / 51200) ∧
    -Real.log (2143 / 51200) ≤ (1586766409 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2143) = 1/(2143 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1586766409 / 500000000) (-3173532813 / 1000000000) (Real.log (2143 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167975649 / 250000000) ≤ -Real.log (20480 / 40099) ∧
    -Real.log (20480 / 40099) ≤ (671902597 / 1000000000) := by
  have h := checkLog_sound (w := (19619 / 60579)) (n := 12)
    (lo := (167975649 / 250000000)) (hi := (671902597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40099 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40099 / 20480) = 1/(20480 / 40099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167975649 / 250000000) (671902597 / 1000000000) (Real.log (40099 / 20480)) := by
  have h := reflection_log_7_neg
  have he : Real.log (40099 / 20480) = -Real.log (20480 / 40099) := by
    rw [show ((40099 / 20480) : ℝ) = ((20480 / 40099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (792277393 / 250000000) ≤ -Real.log (861 / 20480) ∧
    -Real.log (861 / 20480) ≤ (3169109577 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 861) = 1/(861 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3169109577 / 1000000000) (-792277393 / 250000000) (Real.log (861 / 20480)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684183627 / 1000000000) ≤ -Real.log (1000000 / 1982153) ∧
    -Real.log (1000000 / 1982153) ≤ (171045907 / 250000000) := by
  have h := checkLog_sound (w := (982153 / 2982153)) (n := 12)
    (lo := (684183627 / 1000000000)) (hi := (171045907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982153 / 1000000) = 1/(1000000 / 1982153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684183627 / 1000000000) (171045907 / 250000000) (Real.log (1982153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982153 / 1000000) = -Real.log (1000000 / 1982153) := by
    rw [show ((1982153 / 1000000) : ℝ) = ((1000000 / 1982153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4025919849 / 1000000000) ≤ -Real.log (17847 / 1000000) ∧
    -Real.log (17847 / 1000000) ≤ (805183971 / 200000000) := by
  have h := checkLog_sound (w := (13403 / 49097)) (n := 12)
    (lo := (560183949 / 1000000000)) (hi := (11203679 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17847) = 1/(17847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-805183971 / 200000000) (-4025919849 / 1000000000) (Real.log (17847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684222473 / 1000000000) ≤ -Real.log (100000 / 198223) ∧
    -Real.log (100000 / 198223) ≤ (342111237 / 500000000) := by
  have h := checkLog_sound (w := (98223 / 298223)) (n := 12)
    (lo := (684222473 / 1000000000)) (hi := (342111237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198223 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198223 / 100000) = 1/(100000 / 198223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684222473 / 1000000000) (342111237 / 500000000) (Real.log (198223 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (198223 / 100000) = -Real.log (100000 / 198223) := by
    rw [show ((198223 / 100000) : ℝ) = ((100000 / 198223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2015121817 / 500000000) ≤ -Real.log (1777 / 100000) ∧
    -Real.log (1777 / 100000) ≤ (100756091 / 25000000) := by
  have h := checkLog_sound (w := (674 / 2451)) (n := 12)
    (lo := (282253867 / 500000000)) (hi := (112901547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1777) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1777) = 1/(1777 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100756091 / 25000000) (-2015121817 / 500000000) (Real.log (1777 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (17103733 / 25000000) ≤ -Real.log (200000 / 396417) ∧
    -Real.log (200000 / 396417) ≤ (684149321 / 1000000000) := by
  have h := checkLog_sound (w := (196417 / 596417)) (n := 12)
    (lo := (17103733 / 25000000)) (hi := (684149321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396417 / 200000) = 1/(200000 / 396417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (17103733 / 25000000) (684149321 / 1000000000) (Real.log (396417 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (396417 / 200000) = -Real.log (200000 / 396417) := by
    rw [show ((396417 / 200000) : ℝ) = ((200000 / 396417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (160884677 / 40000000) ≤ -Real.log (3583 / 200000) ∧
    -Real.log (3583 / 200000) ≤ (4022116931 / 1000000000) := by
  have h := checkLog_sound (w := (2667 / 9833)) (n := 12)
    (lo := (22255241 / 40000000)) (hi := (278190513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3583) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3583) = 1/(3583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4022116931 / 1000000000) (-160884677 / 40000000) (Real.log (3583 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85523521 / 125000000) ≤ -Real.log (500000 / 991081) ∧
    -Real.log (500000 / 991081) ≤ (684188169 / 1000000000) := by
  have h := checkLog_sound (w := (491081 / 1491081)) (n := 12)
    (lo := (85523521 / 125000000)) (hi := (684188169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991081 / 500000) = 1/(500000 / 991081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85523521 / 125000000) (684188169 / 1000000000) (Real.log (991081 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991081 / 500000) = -Real.log (500000 / 991081) := by
    rw [show ((991081 / 500000) : ℝ) = ((500000 / 991081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2013212131 / 500000000) ≤ -Real.log (8919 / 500000) ∧
    -Real.log (8919 / 500000) ≤ (1006606067 / 250000000) := by
  have h := checkLog_sound (w := (3353 / 12272)) (n := 12)
    (lo := (280344181 / 500000000)) (hi := (560688363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8919) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8919) = 1/(8919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1006606067 / 250000000) (-2013212131 / 500000000) (Real.log (8919 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1177525869 / 250000000) ≤ -Real.log (500000000000 / 55531826077211) ∧
    -Real.log (500000000000 / 55531826077211) ≤ (4710103483 / 1000000000) := by
  have h := checkLog_sound (w := (23531826077211 / 87531826077211)) (n := 12)
    (lo := (137805099 / 250000000)) (hi := (551220397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55531826077211 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55531826077211 / 32000000000000) = 1/(500000000000 / 55531826077211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1177525869 / 250000000) (4710103483 / 1000000000) (Real.log (55531826077211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55531826077211 / 500000000000) = -Real.log (500000000000 / 55531826077211) := by
    rw [show ((55531826077211 / 500000000000) : ℝ) = ((500000000000 / 55531826077211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4714466107 / 1000000000) ≤ -Real.log (100000000000 / 11154924029263) ∧
    -Real.log (100000000000 / 11154924029263) ≤ (2357233057 / 500000000) := by
  have h := checkLog_sound (w := (4754924029263 / 17554924029263)) (n := 12)
    (lo := (555583027 / 1000000000)) (hi := (138895757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11154924029263 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11154924029263 / 6400000000000) = 1/(100000000000 / 11154924029263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4714466107 / 1000000000) (2357233057 / 500000000) (Real.log (11154924029263 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11154924029263 / 100000000000) = -Real.log (100000000000 / 11154924029263) := by
    rw [show ((11154924029263 / 100000000000) : ℝ) = ((100000000000 / 11154924029263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (941253249 / 200000000) ≤ -Real.log (250000000000 / 27659572983533) ∧
    -Real.log (250000000000 / 27659572983533) ≤ (1176566563 / 250000000) := by
  have h := checkLog_sound (w := (11659572983533 / 43659572983533)) (n := 12)
    (lo := (109476633 / 200000000)) (hi := (273691583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27659572983533 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27659572983533 / 16000000000000) = 1/(250000000000 / 27659572983533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (941253249 / 200000000) (1176566563 / 250000000) (Real.log (27659572983533 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27659572983533 / 250000000000) = -Real.log (250000000000 / 27659572983533) := by
    rw [show ((27659572983533 / 250000000000) : ℝ) = ((250000000000 / 27659572983533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (471061243 / 100000000) ≤ -Real.log (250000000000 / 27780048211683) ∧
    -Real.log (250000000000 / 27780048211683) ≤ (4710612437 / 1000000000) := by
  have h := checkLog_sound (w := (11780048211683 / 43780048211683)) (n := 12)
    (lo := (11034587 / 20000000)) (hi := (551729351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27780048211683 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27780048211683 / 16000000000000) = 1/(250000000000 / 27780048211683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (471061243 / 100000000) (4710612437 / 1000000000) (Real.log (27780048211683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (27780048211683 / 250000000000) = -Real.log (250000000000 / 27780048211683) := by
    rw [show ((27780048211683 / 250000000000) : ℝ) = ((250000000000 / 27780048211683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0010
