import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0082
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

theorem reflection_log_1_neg : (337408063 / 500000000) ≤ -Real.log (2560 / 5027) ∧
    -Real.log (2560 / 5027) ≤ (674816127 / 1000000000) := by
  have h := checkLog_sound (w := (2467 / 7587)) (n := 12)
    (lo := (337408063 / 500000000)) (hi := (674816127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5027 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5027 / 2560) = 1/(2560 / 5027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337408063 / 500000000) (674816127 / 1000000000) (Real.log (5027 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5027 / 2560) = -Real.log (2560 / 5027) := by
    rw [show ((5027 / 2560) : ℝ) = ((2560 / 5027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1657581521 / 500000000) ≤ -Real.log (93 / 2560) ∧
    -Real.log (93 / 2560) ≤ (3315163047 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 93) = 1/(93 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3315163047 / 1000000000) (-1657581521 / 500000000) (Real.log (93 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84328391 / 125000000) ≤ -Real.log (51200 / 100521) ∧
    -Real.log (51200 / 100521) ≤ (674627129 / 1000000000) := by
  have h := checkLog_sound (w := (49321 / 151721)) (n := 12)
    (lo := (84328391 / 125000000)) (hi := (674627129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100521 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100521 / 51200) = 1/(51200 / 100521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84328391 / 125000000) (674627129 / 1000000000) (Real.log (100521 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100521 / 51200) = -Real.log (51200 / 100521) := by
    rw [show ((100521 / 51200) : ℝ) = ((51200 / 100521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3304999809 / 1000000000) ≤ -Real.log (1879 / 51200) ∧
    -Real.log (1879 / 51200) ≤ (1652499907 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1879) = 1/(1879 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1652499907 / 500000000) (-3304999809 / 1000000000) (Real.log (1879 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (327878801 / 500000000) ≤ -Real.log (25600 / 49321) ∧
    -Real.log (25600 / 49321) ≤ (655757603 / 1000000000) := by
  have h := checkLog_sound (w := (23721 / 74921)) (n := 12)
    (lo := (327878801 / 500000000)) (hi := (655757603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49321 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49321 / 25600) = 1/(25600 / 49321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (327878801 / 500000000) (655757603 / 1000000000) (Real.log (49321 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49321 / 25600) = -Real.log (25600 / 49321) := by
    rw [show ((49321 / 25600) : ℝ) = ((25600 / 49321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2611852629 / 1000000000) ≤ -Real.log (1879 / 25600) ∧
    -Real.log (1879 / 25600) ≤ (2611852633 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 5079)) (n := 12)
    (lo := (532411089 / 1000000000)) (hi := (53241109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1879) = 1/(1879 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2611852633 / 1000000000) (-2611852629 / 1000000000) (Real.log (1879 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677845707 / 1000000000) ≤ -Real.log (100000 / 196963) ∧
    -Real.log (100000 / 196963) ≤ (169461427 / 250000000) := by
  have h := checkLog_sound (w := (96963 / 296963)) (n := 12)
    (lo := (677845707 / 1000000000)) (hi := (169461427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196963 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196963 / 100000) = 1/(100000 / 196963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677845707 / 1000000000) (169461427 / 250000000) (Real.log (196963 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196963 / 100000) = -Real.log (100000 / 196963) := by
    rw [show ((196963 / 100000) : ℝ) = ((100000 / 196963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3494299997 / 1000000000) ≤ -Real.log (3037 / 100000) ∧
    -Real.log (3037 / 100000) ≤ (3494300003 / 1000000000) := by
  have h := checkLog_sound (w := (44 / 3081)) (n := 12)
    (lo := (28564097 / 1000000000)) (hi := (14282049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3037) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3037) = 1/(3037 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3494300003 / 1000000000) (-3494299997 / 1000000000) (Real.log (3037 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169498487 / 250000000) ≤ -Real.log (500000 / 984961) ∧
    -Real.log (500000 / 984961) ≤ (677993949 / 1000000000) := by
  have h := checkLog_sound (w := (484961 / 1484961)) (n := 12)
    (lo := (169498487 / 250000000)) (hi := (677993949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(984961 / 500000) = 1/(500000 / 984961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169498487 / 250000000) (677993949 / 1000000000) (Real.log (984961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (984961 / 500000) = -Real.log (500000 / 984961) := by
    rw [show ((984961 / 500000) : ℝ) = ((500000 / 984961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (875990317 / 250000000) ≤ -Real.log (15039 / 500000) ∧
    -Real.log (15039 / 500000) ≤ (1751980637 / 500000000) := by
  have h := checkLog_sound (w := (293 / 15332)) (n := 12)
    (lo := (4778171 / 125000000)) (hi := (38225369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15039) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15039) = 1/(15039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1751980637 / 500000000) (-875990317 / 250000000) (Real.log (15039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135544973 / 200000000) ≤ -Real.log (62500 / 123087) ∧
    -Real.log (62500 / 123087) ≤ (338862433 / 500000000) := by
  have h := checkLog_sound (w := (60587 / 185587)) (n := 12)
    (lo := (135544973 / 200000000)) (hi := (338862433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123087 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123087 / 62500) = 1/(62500 / 123087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135544973 / 200000000) (338862433 / 500000000) (Real.log (123087 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123087 / 62500) = -Real.log (62500 / 123087) := by
    rw [show ((123087 / 62500) : ℝ) = ((62500 / 123087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3486493863 / 1000000000) ≤ -Real.log (1913 / 62500) ∧
    -Real.log (1913 / 62500) ≤ (3486493869 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 30929)) (n := 12)
    (lo := (20757963 / 1000000000)) (hi := (5189491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15304) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15304) = 1/(1913 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3486493869 / 1000000000) (-3486493863 / 1000000000) (Real.log (1913 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338937831 / 500000000) ≤ -Real.log (1000000 / 1969689) ∧
    -Real.log (1000000 / 1969689) ≤ (677875663 / 1000000000) := by
  have h := checkLog_sound (w := (969689 / 2969689)) (n := 12)
    (lo := (338937831 / 500000000)) (hi := (677875663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969689 / 1000000) = 1/(1000000 / 1969689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338937831 / 500000000) (677875663 / 1000000000) (Real.log (1969689 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969689 / 1000000) = -Real.log (1000000 / 1969689) := by
    rw [show ((1969689 / 1000000) : ℝ) = ((1000000 / 1969689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3496244593 / 1000000000) ≤ -Real.log (30311 / 1000000) ∧
    -Real.log (30311 / 1000000) ≤ (3496244599 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 61561)) (n := 12)
    (lo := (30508693 / 1000000000)) (hi := (15254347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30311) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30311) = 1/(30311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3496244599 / 1000000000) (-3496244593 / 1000000000) (Real.log (30311 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (521518213 / 125000000) ≤ -Real.log (31250000000 / 2026701926243) ∧
    -Real.log (31250000000 / 2026701926243) ≤ (4172145711 / 1000000000) := by
  have h := checkLog_sound (w := (26701926243 / 4026701926243)) (n := 12)
    (lo := (414457 / 31250000)) (hi := (106101 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2026701926243 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2026701926243 / 2000000000000) = 1/(31250000000 / 2026701926243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (521518213 / 125000000) (4172145711 / 1000000000) (Real.log (2026701926243 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2026701926243 / 31250000000) = -Real.log (31250000000 / 2026701926243) := by
    rw [show ((2026701926243 / 31250000000) : ℝ) = ((31250000000 / 2026701926243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261372201 / 62500000) ≤ -Real.log (500000000000 / 32746891415653) ∧
    -Real.log (500000000000 / 32746891415653) ≤ (4181955223 / 1000000000) := by
  have h := checkLog_sound (w := (746891415653 / 64746891415653)) (n := 12)
    (lo := (2884017 / 125000000)) (hi := (23072137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32746891415653 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32746891415653 / 32000000000000) = 1/(500000000000 / 32746891415653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261372201 / 62500000) (4181955223 / 1000000000) (Real.log (32746891415653 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32746891415653 / 500000000000) = -Real.log (500000000000 / 32746891415653) := by
    rw [show ((32746891415653 / 500000000000) : ℝ) = ((500000000000 / 32746891415653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (520527341 / 125000000) ≤ -Real.log (25000000000 / 1608559853633) ∧
    -Real.log (25000000000 / 1608559853633) ≤ (832843747 / 200000000) := by
  have h := checkLog_sound (w := (8559853633 / 3208559853633)) (n := 12)
    (lo := (166739 / 31250000)) (hi := (5335649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1608559853633 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1608559853633 / 1600000000000) = 1/(25000000000 / 1608559853633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (520527341 / 125000000) (832843747 / 200000000) (Real.log (1608559853633 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1608559853633 / 25000000000) = -Real.log (25000000000 / 1608559853633) := by
    rw [show ((1608559853633 / 25000000000) : ℝ) = ((25000000000 / 1608559853633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2087060127 / 500000000) ≤ -Real.log (500000000000 / 32491323281977) ∧
    -Real.log (500000000000 / 32491323281977) ≤ (4174120261 / 1000000000) := by
  have h := checkLog_sound (w := (491323281977 / 64491323281977)) (n := 12)
    (lo := (7618587 / 500000000)) (hi := (609487 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32491323281977 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32491323281977 / 32000000000000) = 1/(500000000000 / 32491323281977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2087060127 / 500000000) (4174120261 / 1000000000) (Real.log (32491323281977 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (32491323281977 / 500000000000) = -Real.log (500000000000 / 32491323281977) := by
    rw [show ((32491323281977 / 500000000000) : ℝ) = ((500000000000 / 32491323281977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0082
