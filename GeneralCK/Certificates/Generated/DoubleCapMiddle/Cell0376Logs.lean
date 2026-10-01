import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0376
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

theorem reflection_log_1_neg : (205965601 / 1000000000) ≤ -Real.log (5120 / 6291) ∧
    -Real.log (5120 / 6291) ≤ (102982801 / 500000000) := by
  have h := checkLog_sound (w := (1171 / 11411)) (n := 12)
    (lo := (205965601 / 1000000000)) (hi := (102982801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6291 / 5120) = 1/(5120 / 6291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205965601 / 1000000000) (102982801 / 500000000) (Real.log (6291 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6291 / 5120) = -Real.log (5120 / 6291) := by
    rw [show ((6291 / 5120) : ℝ) = ((5120 / 6291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32461507 / 125000000) ≤ -Real.log (3949 / 5120) ∧
    -Real.log (3949 / 5120) ≤ (259692057 / 1000000000) := by
  have h := checkLog_sound (w := (1171 / 9069)) (n := 12)
    (lo := (32461507 / 125000000)) (hi := (259692057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3949) = 1/(3949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-259692057 / 1000000000) (-32461507 / 125000000) (Real.log (3949 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205727137 / 1000000000) ≤ -Real.log (10240 / 12579) ∧
    -Real.log (10240 / 12579) ≤ (102863569 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 22819)) (n := 12)
    (lo := (205727137 / 1000000000)) (hi := (102863569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12579 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12579 / 10240) = 1/(10240 / 12579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205727137 / 1000000000) (102863569 / 500000000) (Real.log (12579 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12579 / 10240) = -Real.log (10240 / 12579) := by
    rw [show ((12579 / 10240) : ℝ) = ((10240 / 12579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (51862457 / 200000000) ≤ -Real.log (7901 / 10240) ∧
    -Real.log (7901 / 10240) ≤ (129656143 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 18141)) (n := 12)
    (lo := (51862457 / 200000000)) (hi := (129656143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7901) = 1/(7901 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129656143 / 500000000) (-51862457 / 200000000) (Real.log (7901 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (75333807 / 200000000) ≤ -Real.log (2560 / 3731) ∧
    -Real.log (2560 / 3731) ≤ (94167259 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 6291)) (n := 12)
    (lo := (75333807 / 200000000)) (hi := (94167259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3731 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3731 / 2560) = 1/(2560 / 3731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (75333807 / 200000000) (94167259 / 250000000) (Real.log (3731 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3731 / 2560) = -Real.log (2560 / 3731) := by
    rw [show ((3731 / 2560) : ℝ) = ((2560 / 3731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (305711597 / 500000000) ≤ -Real.log (1389 / 2560) ∧
    -Real.log (1389 / 2560) ≤ (122284639 / 200000000) := by
  have h := checkLog_sound (w := (1171 / 3949)) (n := 12)
    (lo := (305711597 / 500000000)) (hi := (122284639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1389) = 1/(1389 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122284639 / 200000000) (-305711597 / 500000000) (Real.log (1389 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (376266917 / 1000000000) ≤ -Real.log (5120 / 7459) ∧
    -Real.log (5120 / 7459) ≤ (188133459 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 12579)) (n := 12)
    (lo := (376266917 / 1000000000)) (hi := (188133459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7459 / 5120) = 1/(5120 / 7459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (376266917 / 1000000000) (188133459 / 500000000) (Real.log (7459 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7459 / 5120) = -Real.log (5120 / 7459) := by
    rw [show ((7459 / 5120) : ℝ) = ((5120 / 7459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (610343863 / 1000000000) ≤ -Real.log (2781 / 5120) ∧
    -Real.log (2781 / 5120) ≤ (76292983 / 125000000) := by
  have h := checkLog_sound (w := (2339 / 7901)) (n := 12)
    (lo := (610343863 / 1000000000)) (hi := (76292983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2781) = 1/(2781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-76292983 / 125000000) (-610343863 / 1000000000) (Real.log (2781 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14112643 / 50000000) ≤ -Real.log (500000 / 663057) ∧
    -Real.log (500000 / 663057) ≤ (282252861 / 1000000000) := by
  have h := checkLog_sound (w := (163057 / 1163057)) (n := 12)
    (lo := (14112643 / 50000000)) (hi := (282252861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663057 / 500000) = 1/(500000 / 663057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14112643 / 50000000) (282252861 / 1000000000) (Real.log (663057 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (663057 / 500000) = -Real.log (500000 / 663057) := by
    rw [show ((663057 / 500000) : ℝ) = ((500000 / 663057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (394694321 / 1000000000) ≤ -Real.log (336943 / 500000) ∧
    -Real.log (336943 / 500000) ≤ (197347161 / 500000000) := by
  have h := checkLog_sound (w := (163057 / 836943)) (n := 12)
    (lo := (394694321 / 1000000000)) (hi := (197347161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 336943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 336943) = 1/(336943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197347161 / 500000000) (-394694321 / 1000000000) (Real.log (336943 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (28257631 / 100000000) ≤ -Real.log (1000000 / 1326543) ∧
    -Real.log (1000000 / 1326543) ≤ (282576311 / 1000000000) := by
  have h := checkLog_sound (w := (326543 / 2326543)) (n := 12)
    (lo := (28257631 / 100000000)) (hi := (282576311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326543 / 1000000) = 1/(1000000 / 1326543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (28257631 / 100000000) (282576311 / 1000000000) (Real.log (1326543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1326543 / 1000000) = -Real.log (1000000 / 1326543) := by
    rw [show ((1326543 / 1000000) : ℝ) = ((1000000 / 1326543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39533113 / 100000000) ≤ -Real.log (673457 / 1000000) ∧
    -Real.log (673457 / 1000000) ≤ (395331131 / 1000000000) := by
  have h := checkLog_sound (w := (326543 / 1673457)) (n := 12)
    (lo := (39533113 / 100000000)) (hi := (395331131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673457) = 1/(673457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-395331131 / 1000000000) (-39533113 / 100000000) (Real.log (673457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (53291889 / 250000000) ≤ -Real.log (125000 / 154699) ∧
    -Real.log (125000 / 154699) ≤ (213167557 / 1000000000) := by
  have h := checkLog_sound (w := (29699 / 279699)) (n := 12)
    (lo := (53291889 / 250000000)) (hi := (213167557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154699 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154699 / 125000) = 1/(125000 / 154699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (53291889 / 250000000) (213167557 / 1000000000) (Real.log (154699 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (154699 / 125000) = -Real.log (125000 / 154699) := by
    rw [show ((154699 / 125000) : ℝ) = ((125000 / 154699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271273433 / 1000000000) ≤ -Real.log (95301 / 125000) ∧
    -Real.log (95301 / 125000) ≤ (135636717 / 500000000) := by
  have h := checkLog_sound (w := (29699 / 220301)) (n := 12)
    (lo := (271273433 / 1000000000)) (hi := (135636717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95301) = 1/(95301 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-135636717 / 500000000) (-271273433 / 1000000000) (Real.log (95301 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (213434167 / 1000000000) ≤ -Real.log (500000 / 618961) ∧
    -Real.log (500000 / 618961) ≤ (26679271 / 125000000) := by
  have h := checkLog_sound (w := (118961 / 1118961)) (n := 12)
    (lo := (213434167 / 1000000000)) (hi := (26679271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618961 / 500000) = 1/(500000 / 618961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (213434167 / 1000000000) (26679271 / 125000000) (Real.log (618961 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (618961 / 500000) = -Real.log (500000 / 618961) := by
    rw [show ((618961 / 500000) : ℝ) = ((500000 / 618961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (135853183 / 500000000) ≤ -Real.log (381039 / 500000) ∧
    -Real.log (381039 / 500000) ≤ (271706367 / 1000000000) := by
  have h := checkLog_sound (w := (118961 / 881039)) (n := 12)
    (lo := (135853183 / 500000000)) (hi := (271706367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381039) = 1/(381039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-271706367 / 1000000000) (-135853183 / 500000000) (Real.log (381039 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (338473591 / 500000000) ≤ -Real.log (500000000000 / 983930516437) ∧
    -Real.log (500000000000 / 983930516437) ≤ (676947183 / 1000000000) := by
  have h := checkLog_sound (w := (483930516437 / 1483930516437)) (n := 12)
    (lo := (338473591 / 500000000)) (hi := (676947183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983930516437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983930516437 / 500000000000) = 1/(500000000000 / 983930516437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (338473591 / 500000000) (676947183 / 1000000000) (Real.log (983930516437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (983930516437 / 500000000000) = -Real.log (500000000000 / 983930516437) := by
    rw [show ((983930516437 / 500000000000) : ℝ) = ((500000000000 / 983930516437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8473843 / 12500000) ≤ -Real.log (125000000000 / 246218949391) ∧
    -Real.log (125000000000 / 246218949391) ≤ (677907441 / 1000000000) := by
  have h := checkLog_sound (w := (121218949391 / 371218949391)) (n := 12)
    (lo := (8473843 / 12500000)) (hi := (677907441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246218949391 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246218949391 / 125000000000) = 1/(125000000000 / 246218949391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8473843 / 12500000) (677907441 / 1000000000) (Real.log (246218949391 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (246218949391 / 125000000000) = -Real.log (125000000000 / 246218949391) := by
    rw [show ((246218949391 / 125000000000) : ℝ) = ((125000000000 / 246218949391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (484440989 / 1000000000) ≤ -Real.log (500000000000 / 811633665963) ∧
    -Real.log (500000000000 / 811633665963) ≤ (48444099 / 100000000) := by
  have h := checkLog_sound (w := (311633665963 / 1311633665963)) (n := 12)
    (lo := (484440989 / 1000000000)) (hi := (48444099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811633665963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811633665963 / 500000000000) = 1/(500000000000 / 811633665963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (484440989 / 1000000000) (48444099 / 100000000) (Real.log (811633665963 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (811633665963 / 500000000000) = -Real.log (500000000000 / 811633665963) := by
    rw [show ((811633665963 / 500000000000) : ℝ) = ((500000000000 / 811633665963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (485140533 / 1000000000) ≤ -Real.log (500000000000 / 812201638153) ∧
    -Real.log (500000000000 / 812201638153) ≤ (242570267 / 500000000) := by
  have h := checkLog_sound (w := (312201638153 / 1312201638153)) (n := 12)
    (lo := (485140533 / 1000000000)) (hi := (242570267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812201638153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812201638153 / 500000000000) = 1/(500000000000 / 812201638153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (485140533 / 1000000000) (242570267 / 500000000) (Real.log (812201638153 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (812201638153 / 500000000000) = -Real.log (500000000000 / 812201638153) := by
    rw [show ((812201638153 / 500000000000) : ℝ) = ((500000000000 / 812201638153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0376
