import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0009
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

theorem reflection_log_1_neg : (341337529 / 500000000) ≤ -Real.log (1000000000000 / 1979165039063) ∧
    -Real.log (1000000000000 / 1979165039063) ≤ (682675059 / 1000000000) := by
  have h := checkLog_sound (w := (979165039063 / 2979165039063)) (n := 12)
    (lo := (341337529 / 500000000)) (hi := (682675059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979165039063 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979165039063 / 1000000000000) = 1/(1000000000000 / 1979165039063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341337529 / 500000000) (682675059 / 1000000000) (Real.log (1979165039063 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979165039063 / 1000000000000) = -Real.log (1000000000000 / 1979165039063) := by
    rw [show ((1979165039063 / 1000000000000) : ℝ) = ((1000000000000 / 1979165039063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1935561443 / 500000000) ≤ -Real.log (20834960937 / 1000000000000) ∧
    -Real.log (20834960937 / 1000000000000) ≤ (967780723 / 250000000) := by
  have h := checkLog_sound (w := (10415039063 / 52084960937)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20834960937) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20834960937) = 1/(20834960937 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-967780723 / 250000000) (-1935561443 / 500000000) (Real.log (20834960937 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341314091 / 500000000) ≤ -Real.log (102400 / 202657) ∧
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


theorem reflection_log_3 : Bounds (341314091 / 500000000) (682628183 / 1000000000) (Real.log (202657 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202657 / 102400) = -Real.log (102400 / 202657) := by
    rw [show ((202657 / 102400) : ℝ) = ((102400 / 202657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3866679993 / 1000000000) ≤ -Real.log (2143 / 102400) ∧
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


theorem reflection_log_4 : Bounds (-3866679999 / 1000000000) (-3866679993 / 1000000000) (Real.log (2143 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672092109 / 1000000000) ≤ -Real.log (102400 / 200533) ∧
    -Real.log (102400 / 200533) ≤ (67209211 / 100000000) := by
  have h := checkLog_sound (w := (98133 / 302933)) (n := 12)
    (lo := (672092109 / 1000000000)) (hi := (67209211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200533 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200533 / 102400) = 1/(102400 / 200533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672092109 / 1000000000) (67209211 / 100000000) (Real.log (200533 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200533 / 102400) = -Real.log (102400 / 200533) := by
    rw [show ((200533 / 102400) : ℝ) = ((102400 / 200533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1588987853 / 500000000) ≤ -Real.log (4267 / 102400) ∧
    -Real.log (4267 / 102400) ≤ (3177975711 / 1000000000) := by
  have h := checkLog_sound (w := (2133 / 10667)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4267) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4267) = 1/(4267 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3177975711 / 1000000000) (-1588987853 / 500000000) (Real.log (4267 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671997357 / 1000000000) ≤ -Real.log (51200 / 100257) ∧
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


theorem reflection_log_7 : Bounds (671997357 / 1000000000) (335998679 / 500000000) (Real.log (100257 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100257 / 51200) = -Real.log (51200 / 100257) := by
    rw [show ((100257 / 51200) : ℝ) = ((51200 / 100257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3173532813 / 1000000000) ≤ -Real.log (2143 / 51200) ∧
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


theorem reflection_log_8 : Bounds (-1586766409 / 500000000) (-3173532813 / 1000000000) (Real.log (2143 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684221969 / 1000000000) ≤ -Real.log (1000000 / 1982229) ∧
    -Real.log (1000000 / 1982229) ≤ (68422197 / 100000000) := by
  have h := checkLog_sound (w := (982229 / 2982229)) (n := 12)
    (lo := (684221969 / 1000000000)) (hi := (68422197 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982229 / 1000000) = 1/(1000000 / 1982229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684221969 / 1000000000) (68422197 / 100000000) (Real.log (1982229 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982229 / 1000000) = -Real.log (1000000 / 1982229) := by
    rw [show ((1982229 / 1000000) : ℝ) = ((1000000 / 1982229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (25188671 / 6250000) ≤ -Real.log (17771 / 1000000) ∧
    -Real.log (17771 / 1000000) ≤ (2015093683 / 500000000) := by
  have h := checkLog_sound (w := (13479 / 49021)) (n := 12)
    (lo := (28222573 / 50000000)) (hi := (564451461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17771) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17771) = 1/(17771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2015093683 / 500000000) (-25188671 / 6250000) (Real.log (17771 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684260813 / 1000000000) ≤ -Real.log (500000 / 991153) ∧
    -Real.log (500000 / 991153) ≤ (342130407 / 500000000) := by
  have h := checkLog_sound (w := (491153 / 1491153)) (n := 12)
    (lo := (684260813 / 1000000000)) (hi := (342130407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991153 / 500000) = 1/(500000 / 991153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684260813 / 1000000000) (342130407 / 500000000) (Real.log (991153 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (991153 / 500000) = -Real.log (500000 / 991153) := by
    rw [show ((991153 / 500000) : ℝ) = ((500000 / 991153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4034529677 / 1000000000) ≤ -Real.log (8847 / 500000) ∧
    -Real.log (8847 / 500000) ≤ (4034529683 / 1000000000) := by
  have h := checkLog_sound (w := (3389 / 12236)) (n := 12)
    (lo := (568793777 / 1000000000)) (hi := (284396889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8847) = 1/(8847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4034529683 / 1000000000) (-4034529677 / 1000000000) (Real.log (8847 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684187663 / 1000000000) ≤ -Real.log (1000000 / 1982161) ∧
    -Real.log (1000000 / 1982161) ≤ (42761729 / 62500000) := by
  have h := checkLog_sound (w := (982161 / 2982161)) (n := 12)
    (lo := (684187663 / 1000000000)) (hi := (42761729 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982161 / 1000000) = 1/(1000000 / 1982161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684187663 / 1000000000) (42761729 / 62500000) (Real.log (1982161 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982161 / 1000000) = -Real.log (1000000 / 1982161) := by
    rw [show ((1982161 / 1000000) : ℝ) = ((1000000 / 1982161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1006592051 / 250000000) ≤ -Real.log (17839 / 1000000) ∧
    -Real.log (17839 / 1000000) ≤ (402636821 / 100000000) := by
  have h := checkLog_sound (w := (13411 / 49089)) (n := 12)
    (lo := (35039519 / 62500000)) (hi := (112126461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17839) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17839) = 1/(17839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-402636821 / 100000000) (-1006592051 / 250000000) (Real.log (17839 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684226509 / 1000000000) ≤ -Real.log (500000 / 991119) ∧
    -Real.log (500000 / 991119) ≤ (68422651 / 100000000) := by
  have h := checkLog_sound (w := (491119 / 1491119)) (n := 12)
    (lo := (684226509 / 1000000000)) (hi := (68422651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991119 / 500000) = 1/(500000 / 991119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684226509 / 1000000000) (68422651 / 100000000) (Real.log (991119 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991119 / 500000) = -Real.log (500000 / 991119) := by
    rw [show ((991119 / 500000) : ℝ) = ((500000 / 991119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1007673483 / 250000000) ≤ -Real.log (8881 / 500000) ∧
    -Real.log (8881 / 500000) ≤ (2015346969 / 500000000) := by
  have h := checkLog_sound (w := (3372 / 12253)) (n := 12)
    (lo := (35309877 / 62500000)) (hi := (564958033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8881) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8881) = 1/(8881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2015346969 / 500000000) (-1007673483 / 250000000) (Real.log (8881 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4714409329 / 1000000000) ≤ -Real.log (500000000000 / 55771453491643) ∧
    -Real.log (500000000000 / 55771453491643) ≤ (589301167 / 125000000) := by
  have h := checkLog_sound (w := (23771453491643 / 87771453491643)) (n := 12)
    (lo := (555526249 / 1000000000)) (hi := (444421 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55771453491643 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55771453491643 / 32000000000000) = 1/(500000000000 / 55771453491643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4714409329 / 1000000000) (589301167 / 125000000) (Real.log (55771453491643 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55771453491643 / 500000000000) = -Real.log (500000000000 / 55771453491643) := by
    rw [show ((55771453491643 / 500000000000) : ℝ) = ((500000000000 / 55771453491643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (471879049 / 100000000) ≤ -Real.log (500000000000 / 56016333220301) ∧
    -Real.log (500000000000 / 56016333220301) ≤ (4718790497 / 1000000000) := by
  have h := checkLog_sound (w := (24016333220301 / 88016333220301)) (n := 12)
    (lo := (55990741 / 100000000)) (hi := (559907411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56016333220301 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56016333220301 / 32000000000000) = 1/(500000000000 / 56016333220301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (471879049 / 100000000) (4718790497 / 1000000000) (Real.log (56016333220301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (56016333220301 / 500000000000) = -Real.log (500000000000 / 56016333220301) := by
    rw [show ((56016333220301 / 500000000000) : ℝ) = ((500000000000 / 56016333220301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4710555867 / 1000000000) ≤ -Real.log (250000000000 / 27778476932563) ∧
    -Real.log (250000000000 / 27778476932563) ≤ (2355277937 / 500000000) := by
  have h := checkLog_sound (w := (11778476932563 / 43778476932563)) (n := 12)
    (lo := (551672787 / 1000000000)) (hi := (137918197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27778476932563 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27778476932563 / 16000000000000) = 1/(250000000000 / 27778476932563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4710555867 / 1000000000) (2355277937 / 500000000) (Real.log (27778476932563 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27778476932563 / 250000000000) = -Real.log (250000000000 / 27778476932563) := by
    rw [show ((27778476932563 / 250000000000) : ℝ) = ((250000000000 / 27778476932563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4714920441 / 1000000000) ≤ -Real.log (500000000000 / 55799966220021) ∧
    -Real.log (500000000000 / 55799966220021) ≤ (9208829 / 1953125) := by
  have h := checkLog_sound (w := (23799966220021 / 87799966220021)) (n := 12)
    (lo := (556037361 / 1000000000)) (hi := (278018681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55799966220021 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55799966220021 / 32000000000000) = 1/(500000000000 / 55799966220021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4714920441 / 1000000000) (9208829 / 1953125) (Real.log (55799966220021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55799966220021 / 500000000000) = -Real.log (500000000000 / 55799966220021) := by
    rw [show ((55799966220021 / 500000000000) : ℝ) = ((500000000000 / 55799966220021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0009
