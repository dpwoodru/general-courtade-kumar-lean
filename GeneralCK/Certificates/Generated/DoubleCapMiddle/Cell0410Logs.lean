import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0410
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

theorem reflection_log_1_neg : (197825743 / 1000000000) ≤ -Real.log (32 / 39) ∧
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


theorem reflection_log_1 : Bounds (197825743 / 1000000000) (12364109 / 62500000) (Real.log (39 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (39 / 32) = -Real.log (32 / 39) := by
    rw [show ((39 / 32) : ℝ) = ((32 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246860077 / 1000000000) ≤ -Real.log (25 / 32) ∧
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


theorem reflection_log_2 : Bounds (-123430039 / 500000000) (-246860077 / 1000000000) (Real.log (25 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197585329 / 1000000000) ≤ -Real.log (10240 / 12477) ∧
    -Real.log (10240 / 12477) ≤ (19758533 / 100000000) := by
  have h := checkLog_sound (w := (2237 / 22717)) (n := 12)
    (lo := (197585329 / 1000000000)) (hi := (19758533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12477 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12477 / 10240) = 1/(10240 / 12477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197585329 / 1000000000) (19758533 / 100000000) (Real.log (12477 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12477 / 10240) = -Real.log (10240 / 12477) := by
    rw [show ((12477 / 10240) : ℝ) = ((10240 / 12477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (61621287 / 250000000) ≤ -Real.log (8003 / 10240) ∧
    -Real.log (8003 / 10240) ≤ (246485149 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 18243)) (n := 12)
    (lo := (61621287 / 250000000)) (hi := (246485149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8003) = 1/(8003 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-246485149 / 1000000000) (-61621287 / 250000000) (Real.log (8003 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
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


theorem reflection_log_5 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
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


theorem reflection_log_6 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362497801 / 1000000000) ≤ -Real.log (5120 / 7357) ∧
    -Real.log (5120 / 7357) ≤ (181248901 / 500000000) := by
  have h := checkLog_sound (w := (2237 / 12477)) (n := 12)
    (lo := (362497801 / 1000000000)) (hi := (181248901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7357 / 5120) = 1/(5120 / 7357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362497801 / 1000000000) (181248901 / 500000000) (Real.log (7357 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7357 / 5120) = -Real.log (5120 / 7357) := by
    rw [show ((7357 / 5120) : ℝ) = ((5120 / 7357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28716151 / 50000000) ≤ -Real.log (2883 / 5120) ∧
    -Real.log (2883 / 5120) ≤ (574323021 / 1000000000) := by
  have h := checkLog_sound (w := (2237 / 8003)) (n := 12)
    (lo := (28716151 / 50000000)) (hi := (574323021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2883) = 1/(2883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-574323021 / 1000000000) (-28716151 / 50000000) (Real.log (2883 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67815563 / 250000000) ≤ -Real.log (1000000 / 1311619) ∧
    -Real.log (1000000 / 1311619) ≤ (271262253 / 1000000000) := by
  have h := checkLog_sound (w := (311619 / 2311619)) (n := 12)
    (lo := (67815563 / 250000000)) (hi := (271262253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311619 / 1000000) = 1/(1000000 / 1311619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67815563 / 250000000) (271262253 / 1000000000) (Real.log (1311619 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1311619 / 1000000) = -Real.log (1000000 / 1311619) := by
    rw [show ((1311619 / 1000000) : ℝ) = ((1000000 / 1311619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (74682563 / 200000000) ≤ -Real.log (688381 / 1000000) ∧
    -Real.log (688381 / 1000000) ≤ (23338301 / 62500000) := by
  have h := checkLog_sound (w := (311619 / 1688381)) (n := 12)
    (lo := (74682563 / 200000000)) (hi := (23338301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688381) = 1/(688381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23338301 / 62500000) (-74682563 / 200000000) (Real.log (688381 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67896747 / 250000000) ≤ -Real.log (200000 / 262409) ∧
    -Real.log (200000 / 262409) ≤ (271586989 / 1000000000) := by
  have h := checkLog_sound (w := (62409 / 462409)) (n := 12)
    (lo := (67896747 / 250000000)) (hi := (271586989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262409 / 200000) = 1/(200000 / 262409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67896747 / 250000000) (271586989 / 1000000000) (Real.log (262409 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (262409 / 200000) = -Real.log (200000 / 262409) := by
    rw [show ((262409 / 200000) : ℝ) = ((200000 / 262409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7480637 / 20000000) ≤ -Real.log (137591 / 200000) ∧
    -Real.log (137591 / 200000) ≤ (374031851 / 1000000000) := by
  have h := checkLog_sound (w := (62409 / 337591)) (n := 12)
    (lo := (7480637 / 20000000)) (hi := (374031851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137591) = 1/(137591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-374031851 / 1000000000) (-7480637 / 20000000) (Real.log (137591 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102055793 / 500000000) ≤ -Real.log (200000 / 245287) ∧
    -Real.log (200000 / 245287) ≤ (204111587 / 1000000000) := by
  have h := checkLog_sound (w := (45287 / 445287)) (n := 12)
    (lo := (102055793 / 500000000)) (hi := (204111587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245287 / 200000) = 1/(200000 / 245287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102055793 / 500000000) (204111587 / 1000000000) (Real.log (245287 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (245287 / 200000) = -Real.log (200000 / 245287) := by
    rw [show ((245287 / 200000) : ℝ) = ((200000 / 245287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (128372789 / 500000000) ≤ -Real.log (154713 / 200000) ∧
    -Real.log (154713 / 200000) ≤ (256745579 / 1000000000) := by
  have h := checkLog_sound (w := (45287 / 354713)) (n := 12)
    (lo := (128372789 / 500000000)) (hi := (256745579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154713) = 1/(154713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256745579 / 1000000000) (-128372789 / 500000000) (Real.log (154713 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204378177 / 1000000000) ≤ -Real.log (500000 / 613381) ∧
    -Real.log (500000 / 613381) ≤ (102189089 / 500000000) := by
  have h := checkLog_sound (w := (113381 / 1113381)) (n := 12)
    (lo := (204378177 / 1000000000)) (hi := (102189089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613381 / 500000) = 1/(500000 / 613381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204378177 / 1000000000) (102189089 / 500000000) (Real.log (613381 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (613381 / 500000) = -Real.log (500000 / 613381) := by
    rw [show ((613381 / 500000) : ℝ) = ((500000 / 613381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128584193 / 500000000) ≤ -Real.log (386619 / 500000) ∧
    -Real.log (386619 / 500000) ≤ (257168387 / 1000000000) := by
  have h := checkLog_sound (w := (113381 / 886619)) (n := 12)
    (lo := (128584193 / 500000000)) (hi := (257168387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386619) = 1/(386619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-257168387 / 1000000000) (-128584193 / 500000000) (Real.log (386619 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (644675067 / 1000000000) ≤ -Real.log (10000000000 / 19053678123) ∧
    -Real.log (10000000000 / 19053678123) ≤ (161168767 / 250000000) := by
  have h := checkLog_sound (w := (9053678123 / 29053678123)) (n := 12)
    (lo := (644675067 / 1000000000)) (hi := (161168767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19053678123 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19053678123 / 10000000000) = 1/(10000000000 / 19053678123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (644675067 / 1000000000) (161168767 / 250000000) (Real.log (19053678123 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19053678123 / 10000000000) = -Real.log (10000000000 / 19053678123) := by
    rw [show ((19053678123 / 10000000000) : ℝ) = ((10000000000 / 19053678123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322809419 / 500000000) ≤ -Real.log (7812500000 / 14899741353) ∧
    -Real.log (7812500000 / 14899741353) ≤ (645618839 / 1000000000) := by
  have h := checkLog_sound (w := (7087241353 / 22712241353)) (n := 12)
    (lo := (322809419 / 500000000)) (hi := (645618839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14899741353 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14899741353 / 7812500000) = 1/(7812500000 / 14899741353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322809419 / 500000000) (645618839 / 1000000000) (Real.log (14899741353 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14899741353 / 7812500000) = -Real.log (7812500000 / 14899741353) := by
    rw [show ((14899741353 / 7812500000) : ℝ) = ((7812500000 / 14899741353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92171433 / 200000000) ≤ -Real.log (500000000000 / 792716190623) ∧
    -Real.log (500000000000 / 792716190623) ≤ (230428583 / 500000000) := by
  have h := checkLog_sound (w := (292716190623 / 1292716190623)) (n := 12)
    (lo := (92171433 / 200000000)) (hi := (230428583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792716190623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792716190623 / 500000000000) = 1/(500000000000 / 792716190623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92171433 / 200000000) (230428583 / 500000000) (Real.log (792716190623 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (792716190623 / 500000000000) = -Real.log (500000000000 / 792716190623) := by
    rw [show ((792716190623 / 500000000000) : ℝ) = ((500000000000 / 792716190623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (115386641 / 250000000) ≤ -Real.log (125000000000 / 198315719093) ∧
    -Real.log (125000000000 / 198315719093) ≤ (92309313 / 200000000) := by
  have h := checkLog_sound (w := (73315719093 / 323315719093)) (n := 12)
    (lo := (115386641 / 250000000)) (hi := (92309313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198315719093 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198315719093 / 125000000000) = 1/(125000000000 / 198315719093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (115386641 / 250000000) (92309313 / 200000000) (Real.log (198315719093 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (198315719093 / 125000000000) = -Real.log (125000000000 / 198315719093) := by
    rw [show ((198315719093 / 125000000000) : ℝ) = ((125000000000 / 198315719093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0410
