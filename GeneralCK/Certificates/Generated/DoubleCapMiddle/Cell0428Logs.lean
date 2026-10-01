import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0428
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

theorem reflection_log_1_neg : (24186179 / 125000000) ≤ -Real.log (5120 / 6213) ∧
    -Real.log (5120 / 6213) ≤ (193489433 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 11333)) (n := 12)
    (lo := (24186179 / 125000000)) (hi := (193489433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6213 / 5120) = 1/(5120 / 6213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24186179 / 125000000) (193489433 / 1000000000) (Real.log (6213 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6213 / 5120) = -Real.log (5120 / 6213) := by
    rw [show ((6213 / 5120) : ℝ) = ((5120 / 6213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (240132757 / 1000000000) ≤ -Real.log (4027 / 5120) ∧
    -Real.log (4027 / 5120) ≤ (120066379 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 9147)) (n := 12)
    (lo := (240132757 / 1000000000)) (hi := (120066379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4027) = 1/(4027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-120066379 / 500000000) (-240132757 / 1000000000) (Real.log (4027 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (193247973 / 1000000000) ≤ -Real.log (10240 / 12423) ∧
    -Real.log (10240 / 12423) ≤ (96623987 / 500000000) := by
  have h := checkLog_sound (w := (2183 / 22663)) (n := 12)
    (lo := (193247973 / 1000000000)) (hi := (96623987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12423 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12423 / 10240) = 1/(10240 / 12423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (193247973 / 1000000000) (96623987 / 500000000) (Real.log (12423 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12423 / 10240) = -Real.log (10240 / 12423) := by
    rw [show ((12423 / 10240) : ℝ) = ((10240 / 12423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11988017 / 50000000) ≤ -Real.log (8057 / 10240) ∧
    -Real.log (8057 / 10240) ≤ (239760341 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 18297)) (n := 12)
    (lo := (11988017 / 50000000)) (hi := (239760341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8057) = 1/(8057 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-239760341 / 1000000000) (-11988017 / 50000000) (Real.log (8057 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (355541489 / 1000000000) ≤ -Real.log (2560 / 3653) ∧
    -Real.log (2560 / 3653) ≤ (35554149 / 100000000) := by
  have h := checkLog_sound (w := (1093 / 6213)) (n := 12)
    (lo := (355541489 / 1000000000)) (hi := (35554149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3653 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3653 / 2560) = 1/(2560 / 3653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (355541489 / 1000000000) (35554149 / 100000000) (Real.log (3653 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3653 / 2560) = -Real.log (2560 / 3653) := by
    rw [show ((3653 / 2560) : ℝ) = ((2560 / 3653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (556787759 / 1000000000) ≤ -Real.log (1467 / 2560) ∧
    -Real.log (1467 / 2560) ≤ (6959847 / 12500000) := by
  have h := checkLog_sound (w := (1093 / 4027)) (n := 12)
    (lo := (556787759 / 1000000000)) (hi := (6959847 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1467) = 1/(1467 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6959847 / 12500000) (-556787759 / 1000000000) (Real.log (1467 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (355130783 / 1000000000) ≤ -Real.log (5120 / 7303) ∧
    -Real.log (5120 / 7303) ≤ (11097837 / 31250000) := by
  have h := checkLog_sound (w := (2183 / 12423)) (n := 12)
    (lo := (355130783 / 1000000000)) (hi := (11097837 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7303 / 5120) = 1/(5120 / 7303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (355130783 / 1000000000) (11097837 / 31250000) (Real.log (7303 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7303 / 5120) = -Real.log (5120 / 7303) := by
    rw [show ((7303 / 5120) : ℝ) = ((5120 / 7303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (277882893 / 500000000) ≤ -Real.log (2937 / 5120) ∧
    -Real.log (2937 / 5120) ≤ (555765787 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 8057)) (n := 12)
    (lo := (277882893 / 500000000)) (hi := (555765787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2937) = 1/(2937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-555765787 / 1000000000) (-277882893 / 500000000) (Real.log (2937 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (53081311 / 200000000) ≤ -Real.log (1000000 / 1303961) ∧
    -Real.log (1000000 / 1303961) ≤ (66351639 / 250000000) := by
  have h := checkLog_sound (w := (303961 / 2303961)) (n := 12)
    (lo := (53081311 / 200000000)) (hi := (66351639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303961 / 1000000) = 1/(1000000 / 1303961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (53081311 / 200000000) (66351639 / 250000000) (Real.log (1303961 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1303961 / 1000000) = -Real.log (1000000 / 1303961) := by
    rw [show ((1303961 / 1000000) : ℝ) = ((1000000 / 1303961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72469917 / 200000000) ≤ -Real.log (696039 / 1000000) ∧
    -Real.log (696039 / 1000000) ≤ (181174793 / 500000000) := by
  have h := checkLog_sound (w := (303961 / 1696039)) (n := 12)
    (lo := (72469917 / 200000000)) (hi := (181174793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696039) = 1/(696039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-181174793 / 500000000) (-72469917 / 200000000) (Real.log (696039 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132866599 / 500000000) ≤ -Real.log (1000000 / 1304387) ∧
    -Real.log (1000000 / 1304387) ≤ (265733199 / 1000000000) := by
  have h := checkLog_sound (w := (304387 / 2304387)) (n := 12)
    (lo := (132866599 / 500000000)) (hi := (265733199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304387 / 1000000) = 1/(1000000 / 1304387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132866599 / 500000000) (265733199 / 1000000000) (Real.log (1304387 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1304387 / 1000000) = -Real.log (1000000 / 1304387) := by
    rw [show ((1304387 / 1000000) : ℝ) = ((1000000 / 1304387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (362961807 / 1000000000) ≤ -Real.log (695613 / 1000000) ∧
    -Real.log (695613 / 1000000) ≤ (22685113 / 62500000) := by
  have h := checkLog_sound (w := (304387 / 1695613)) (n := 12)
    (lo := (362961807 / 1000000000)) (hi := (22685113 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695613) = 1/(695613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22685113 / 62500000) (-362961807 / 1000000000) (Real.log (695613 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199322059 / 1000000000) ≤ -Real.log (40000 / 48823) ∧
    -Real.log (40000 / 48823) ≤ (9966103 / 50000000) := by
  have h := checkLog_sound (w := (8823 / 88823)) (n := 12)
    (lo := (199322059 / 1000000000)) (hi := (9966103 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48823 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48823 / 40000) = 1/(40000 / 48823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199322059 / 1000000000) (9966103 / 50000000) (Real.log (48823 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48823 / 40000) = -Real.log (40000 / 48823) := by
    rw [show ((48823 / 40000) : ℝ) = ((40000 / 48823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (24919881 / 100000000) ≤ -Real.log (31177 / 40000) ∧
    -Real.log (31177 / 40000) ≤ (249198811 / 1000000000) := by
  have h := checkLog_sound (w := (8823 / 71177)) (n := 12)
    (lo := (24919881 / 100000000)) (hi := (249198811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31177) = 1/(31177 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-249198811 / 1000000000) (-24919881 / 100000000) (Real.log (31177 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19958911 / 100000000) ≤ -Real.log (1000000 / 1220901) ∧
    -Real.log (1000000 / 1220901) ≤ (199589111 / 1000000000) := by
  have h := checkLog_sound (w := (220901 / 2220901)) (n := 12)
    (lo := (19958911 / 100000000)) (hi := (199589111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220901 / 1000000) = 1/(1000000 / 1220901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19958911 / 100000000) (199589111 / 1000000000) (Real.log (1220901 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1220901 / 1000000) = -Real.log (1000000 / 1220901) := by
    rw [show ((1220901 / 1000000) : ℝ) = ((1000000 / 1220901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49923431 / 200000000) ≤ -Real.log (779099 / 1000000) ∧
    -Real.log (779099 / 1000000) ≤ (62404289 / 250000000) := by
  have h := checkLog_sound (w := (220901 / 1779099)) (n := 12)
    (lo := (49923431 / 200000000)) (hi := (62404289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779099) = 1/(779099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-62404289 / 250000000) (-49923431 / 200000000) (Real.log (779099 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (31387807 / 50000000) ≤ -Real.log (62500000000 / 117087638049) ∧
    -Real.log (62500000000 / 117087638049) ≤ (627756141 / 1000000000) := by
  have h := checkLog_sound (w := (54587638049 / 179587638049)) (n := 12)
    (lo := (31387807 / 50000000)) (hi := (627756141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117087638049 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117087638049 / 62500000000) = 1/(62500000000 / 117087638049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (31387807 / 50000000) (627756141 / 1000000000) (Real.log (117087638049 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (117087638049 / 62500000000) = -Real.log (62500000000 / 117087638049) := by
    rw [show ((117087638049 / 62500000000) : ℝ) = ((62500000000 / 117087638049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (314347503 / 500000000) ≤ -Real.log (250000000000 / 468790476889) ∧
    -Real.log (250000000000 / 468790476889) ≤ (628695007 / 1000000000) := by
  have h := checkLog_sound (w := (218790476889 / 718790476889)) (n := 12)
    (lo := (314347503 / 500000000)) (hi := (628695007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468790476889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468790476889 / 250000000000) = 1/(250000000000 / 468790476889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (314347503 / 500000000) (628695007 / 1000000000) (Real.log (468790476889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (468790476889 / 250000000000) = -Real.log (250000000000 / 468790476889) := by
    rw [show ((468790476889 / 250000000000) : ℝ) = ((250000000000 / 468790476889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (448520869 / 1000000000) ≤ -Real.log (500000000000 / 782997081181) ∧
    -Real.log (500000000000 / 782997081181) ≤ (44852087 / 100000000) := by
  have h := checkLog_sound (w := (282997081181 / 1282997081181)) (n := 12)
    (lo := (448520869 / 1000000000)) (hi := (44852087 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782997081181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782997081181 / 500000000000) = 1/(500000000000 / 782997081181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (448520869 / 1000000000) (44852087 / 100000000) (Real.log (782997081181 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (782997081181 / 500000000000) = -Real.log (500000000000 / 782997081181) := by
    rw [show ((782997081181 / 500000000000) : ℝ) = ((500000000000 / 782997081181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (89841253 / 200000000) ≤ -Real.log (100000000000 / 156706785659) ∧
    -Real.log (100000000000 / 156706785659) ≤ (224603133 / 500000000) := by
  have h := checkLog_sound (w := (56706785659 / 256706785659)) (n := 12)
    (lo := (89841253 / 200000000)) (hi := (224603133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156706785659 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156706785659 / 100000000000) = 1/(100000000000 / 156706785659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (89841253 / 200000000) (224603133 / 500000000) (Real.log (156706785659 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (156706785659 / 100000000000) = -Real.log (100000000000 / 156706785659) := by
    rw [show ((156706785659 / 100000000000) : ℝ) = ((100000000000 / 156706785659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0428
