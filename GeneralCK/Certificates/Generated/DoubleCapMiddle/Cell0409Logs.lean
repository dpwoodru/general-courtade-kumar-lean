import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0409
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

theorem reflection_log_1_neg : (198066099 / 1000000000) ≤ -Real.log (10240 / 12483) ∧
    -Real.log (10240 / 12483) ≤ (1980661 / 10000000) := by
  have h := checkLog_sound (w := (2243 / 22723)) (n := 12)
    (lo := (198066099 / 1000000000)) (hi := (1980661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12483 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12483 / 10240) = 1/(10240 / 12483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198066099 / 1000000000) (1980661 / 10000000) (Real.log (12483 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12483 / 10240) = -Real.log (10240 / 12483) := by
    rw [show ((12483 / 10240) : ℝ) = ((10240 / 12483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (61808787 / 250000000) ≤ -Real.log (7997 / 10240) ∧
    -Real.log (7997 / 10240) ≤ (247235149 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 18237)) (n := 12)
    (lo := (61808787 / 250000000)) (hi := (247235149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7997) = 1/(7997 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-247235149 / 1000000000) (-61808787 / 250000000) (Real.log (7997 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197825743 / 1000000000) ≤ -Real.log (32 / 39) ∧
    -Real.log (32 / 39) ≤ (12364109 / 62500000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 32) = 1/(32 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197825743 / 1000000000) (12364109 / 62500000) (Real.log (39 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (39 / 32) = -Real.log (32 / 39) := by
    rw [show ((39 / 32) : ℝ) = ((32 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246860077 / 1000000000) ≤ -Real.log (25 / 32) ∧
    -Real.log (25 / 32) ≤ (123430039 / 500000000) := by
  have h := checkLog_sound (w := (7 / 57)) (n := 12)
    (lo := (246860077 / 1000000000)) (hi := (123430039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 25) = 1/(25 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123430039 / 500000000) (-246860077 / 1000000000) (Real.log (25 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (363313019 / 1000000000) ≤ -Real.log (5120 / 7363) ∧
    -Real.log (5120 / 7363) ≤ (18165651 / 50000000) := by
  have h := checkLog_sound (w := (2243 / 12483)) (n := 12)
    (lo := (363313019 / 1000000000)) (hi := (18165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7363 / 5120) = 1/(5120 / 7363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (363313019 / 1000000000) (18165651 / 50000000) (Real.log (7363 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7363 / 5120) = -Real.log (5120 / 7363) := by
    rw [show ((7363 / 5120) : ℝ) = ((5120 / 7363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288203177 / 500000000) ≤ -Real.log (2877 / 5120) ∧
    -Real.log (2877 / 5120) ≤ (115281271 / 200000000) := by
  have h := checkLog_sound (w := (2243 / 7997)) (n := 12)
    (lo := (288203177 / 500000000)) (hi := (115281271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2877) = 1/(2877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115281271 / 200000000) (-288203177 / 500000000) (Real.log (2877 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135793113 / 500000000) ≤ -Real.log (250000 / 328011) ∧
    -Real.log (250000 / 328011) ≤ (271586227 / 1000000000) := by
  have h := checkLog_sound (w := (78011 / 578011)) (n := 12)
    (lo := (135793113 / 500000000)) (hi := (271586227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328011 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328011 / 250000) = 1/(250000 / 328011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135793113 / 500000000) (271586227 / 1000000000) (Real.log (328011 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328011 / 250000) = -Real.log (250000 / 328011) := by
    rw [show ((328011 / 250000) : ℝ) = ((250000 / 328011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93507599 / 250000000) ≤ -Real.log (171989 / 250000) ∧
    -Real.log (171989 / 250000) ≤ (374030397 / 1000000000) := by
  have h := checkLog_sound (w := (78011 / 421989)) (n := 12)
    (lo := (93507599 / 250000000)) (hi := (374030397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171989) = 1/(171989 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-374030397 / 1000000000) (-93507599 / 250000000) (Real.log (171989 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13595581 / 50000000) ≤ -Real.log (1000000 / 1312471) ∧
    -Real.log (1000000 / 1312471) ≤ (271911621 / 1000000000) := by
  have h := checkLog_sound (w := (312471 / 2312471)) (n := 12)
    (lo := (13595581 / 50000000)) (hi := (271911621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312471 / 1000000) = 1/(1000000 / 1312471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13595581 / 50000000) (271911621 / 1000000000) (Real.log (1312471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1312471 / 1000000) = -Real.log (1000000 / 1312471) := by
    rw [show ((1312471 / 1000000) : ℝ) = ((1000000 / 1312471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93662817 / 250000000) ≤ -Real.log (687529 / 1000000) ∧
    -Real.log (687529 / 1000000) ≤ (374651269 / 1000000000) := by
  have h := checkLog_sound (w := (312471 / 1687529)) (n := 12)
    (lo := (93662817 / 250000000)) (hi := (374651269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687529) = 1/(687529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-374651269 / 1000000000) (-93662817 / 250000000) (Real.log (687529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102188681 / 500000000) ≤ -Real.log (1000000 / 1226761) ∧
    -Real.log (1000000 / 1226761) ≤ (204377363 / 1000000000) := by
  have h := checkLog_sound (w := (226761 / 2226761)) (n := 12)
    (lo := (102188681 / 500000000)) (hi := (204377363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226761 / 1000000) = 1/(1000000 / 1226761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102188681 / 500000000) (204377363 / 1000000000) (Real.log (1226761 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1226761 / 1000000) = -Real.log (1000000 / 1226761) := by
    rw [show ((1226761 / 1000000) : ℝ) = ((1000000 / 1226761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257167093 / 1000000000) ≤ -Real.log (773239 / 1000000) ∧
    -Real.log (773239 / 1000000) ≤ (128583547 / 500000000) := by
  have h := checkLog_sound (w := (226761 / 1773239)) (n := 12)
    (lo := (257167093 / 1000000000)) (hi := (128583547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773239) = 1/(773239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-128583547 / 500000000) (-257167093 / 1000000000) (Real.log (773239 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204644697 / 1000000000) ≤ -Real.log (1000000 / 1227089) ∧
    -Real.log (1000000 / 1227089) ≤ (102322349 / 500000000) := by
  have h := checkLog_sound (w := (227089 / 2227089)) (n := 12)
    (lo := (204644697 / 1000000000)) (hi := (102322349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227089 / 1000000) = 1/(1000000 / 1227089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204644697 / 1000000000) (102322349 / 500000000) (Real.log (1227089 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1227089 / 1000000) = -Real.log (1000000 / 1227089) := by
    rw [show ((1227089 / 1000000) : ℝ) = ((1000000 / 1227089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (64397843 / 250000000) ≤ -Real.log (772911 / 1000000) ∧
    -Real.log (772911 / 1000000) ≤ (257591373 / 1000000000) := by
  have h := checkLog_sound (w := (227089 / 1772911)) (n := 12)
    (lo := (64397843 / 250000000)) (hi := (257591373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772911) = 1/(772911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-257591373 / 1000000000) (-64397843 / 250000000) (Real.log (772911 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (645616623 / 1000000000) ≤ -Real.log (500000000000 / 953581333689) ∧
    -Real.log (500000000000 / 953581333689) ≤ (40351039 / 62500000) := by
  have h := checkLog_sound (w := (453581333689 / 1453581333689)) (n := 12)
    (lo := (645616623 / 1000000000)) (hi := (40351039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953581333689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953581333689 / 500000000000) = 1/(500000000000 / 953581333689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (645616623 / 1000000000) (40351039 / 62500000) (Real.log (953581333689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (953581333689 / 500000000000) = -Real.log (500000000000 / 953581333689) := by
    rw [show ((953581333689 / 500000000000) : ℝ) = ((500000000000 / 953581333689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (80820361 / 125000000) ≤ -Real.log (250000000000 / 477242050881) ∧
    -Real.log (250000000000 / 477242050881) ≤ (646562889 / 1000000000) := by
  have h := checkLog_sound (w := (227242050881 / 727242050881)) (n := 12)
    (lo := (80820361 / 125000000)) (hi := (646562889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477242050881 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477242050881 / 250000000000) = 1/(250000000000 / 477242050881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (80820361 / 125000000) (646562889 / 1000000000) (Real.log (477242050881 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (477242050881 / 250000000000) = -Real.log (250000000000 / 477242050881) := by
    rw [show ((477242050881 / 250000000000) : ℝ) = ((250000000000 / 477242050881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92308891 / 200000000) ≤ -Real.log (100000000000 / 158652240769) ∧
    -Real.log (100000000000 / 158652240769) ≤ (57693057 / 125000000) := by
  have h := checkLog_sound (w := (58652240769 / 258652240769)) (n := 12)
    (lo := (92308891 / 200000000)) (hi := (57693057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158652240769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158652240769 / 100000000000) = 1/(100000000000 / 158652240769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92308891 / 200000000) (57693057 / 125000000) (Real.log (158652240769 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (158652240769 / 100000000000) = -Real.log (100000000000 / 158652240769) := by
    rw [show ((158652240769 / 100000000000) : ℝ) = ((100000000000 / 158652240769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (46223607 / 100000000) ≤ -Real.log (500000000000 / 793810024699) ∧
    -Real.log (500000000000 / 793810024699) ≤ (462236071 / 1000000000) := by
  have h := checkLog_sound (w := (293810024699 / 1293810024699)) (n := 12)
    (lo := (46223607 / 100000000)) (hi := (462236071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793810024699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793810024699 / 500000000000) = 1/(500000000000 / 793810024699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (46223607 / 100000000) (462236071 / 1000000000) (Real.log (793810024699 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (793810024699 / 500000000000) = -Real.log (500000000000 / 793810024699) := by
    rw [show ((793810024699 / 500000000000) : ℝ) = ((500000000000 / 793810024699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0409
