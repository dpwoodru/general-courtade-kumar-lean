import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0292
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

theorem reflection_log_1_neg : (225796279 / 1000000000) ≤ -Real.log (5120 / 6417) ∧
    -Real.log (5120 / 6417) ≤ (5644907 / 25000000) := by
  have h := checkLog_sound (w := (1297 / 11537)) (n := 12)
    (lo := (225796279 / 1000000000)) (hi := (5644907 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6417 / 5120) = 1/(5120 / 6417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225796279 / 1000000000) (5644907 / 25000000) (Real.log (6417 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6417 / 5120) = -Real.log (5120 / 6417) := by
    rw [show ((6417 / 5120) : ℝ) = ((5120 / 6417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36514873 / 125000000) ≤ -Real.log (3823 / 5120) ∧
    -Real.log (3823 / 5120) ≤ (58423797 / 200000000) := by
  have h := checkLog_sound (w := (1297 / 8943)) (n := 12)
    (lo := (36514873 / 125000000)) (hi := (58423797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3823) = 1/(3823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58423797 / 200000000) (-36514873 / 125000000) (Real.log (3823 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (112781249 / 500000000) ≤ -Real.log (10240 / 12831) ∧
    -Real.log (10240 / 12831) ≤ (225562499 / 1000000000) := by
  have h := checkLog_sound (w := (2591 / 23071)) (n := 12)
    (lo := (112781249 / 500000000)) (hi := (225562499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12831 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12831 / 10240) = 1/(10240 / 12831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (112781249 / 500000000) (225562499 / 1000000000) (Real.log (12831 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12831 / 10240) = -Real.log (10240 / 12831) := by
    rw [show ((12831 / 10240) : ℝ) = ((10240 / 12831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291726699 / 1000000000) ≤ -Real.log (7649 / 10240) ∧
    -Real.log (7649 / 10240) ≤ (2917267 / 10000000) := by
  have h := checkLog_sound (w := (2591 / 17889)) (n := 12)
    (lo := (291726699 / 1000000000)) (hi := (2917267 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7649) = 1/(7649 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2917267 / 10000000) (-291726699 / 1000000000) (Real.log (7649 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20494121 / 50000000) ≤ -Real.log (2560 / 3857) ∧
    -Real.log (2560 / 3857) ≤ (409882421 / 1000000000) := by
  have h := checkLog_sound (w := (1297 / 6417)) (n := 12)
    (lo := (20494121 / 50000000)) (hi := (409882421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3857 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3857 / 2560) = 1/(2560 / 3857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20494121 / 50000000) (409882421 / 1000000000) (Real.log (3857 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3857 / 2560) = -Real.log (2560 / 3857) := by
    rw [show ((3857 / 2560) : ℝ) = ((2560 / 3857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (353258707 / 500000000) ≤ -Real.log (1263 / 2560) ∧
    -Real.log (1263 / 2560) ≤ (88314677 / 125000000) := by
  have h := checkLog_sound (w := (17 / 2543)) (n := 12)
    (lo := (6685117 / 500000000)) (hi := (2674047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1263) = 1/(1263 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-88314677 / 125000000) (-353258707 / 500000000) (Real.log (1263 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (409493441 / 1000000000) ≤ -Real.log (5120 / 7711) ∧
    -Real.log (5120 / 7711) ≤ (204746721 / 500000000) := by
  have h := checkLog_sound (w := (2591 / 12831)) (n := 12)
    (lo := (409493441 / 1000000000)) (hi := (204746721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7711 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7711 / 5120) = 1/(5120 / 7711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (409493441 / 1000000000) (204746721 / 500000000) (Real.log (7711 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7711 / 5120) = -Real.log (5120 / 7711) := by
    rw [show ((7711 / 5120) : ℝ) = ((5120 / 7711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70533047 / 100000000) ≤ -Real.log (2529 / 5120) ∧
    -Real.log (2529 / 5120) ≤ (88166309 / 125000000) := by
  have h := checkLog_sound (w := (31 / 5089)) (n := 12)
    (lo := (1218329 / 100000000)) (hi := (12183291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2529) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2529) = 1/(2529 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88166309 / 125000000) (-70533047 / 100000000) (Real.log (2529 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15452299 / 50000000) ≤ -Real.log (8000 / 10897) ∧
    -Real.log (8000 / 10897) ≤ (309045981 / 1000000000) := by
  have h := checkLog_sound (w := (2897 / 18897)) (n := 12)
    (lo := (15452299 / 50000000)) (hi := (309045981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10897 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10897 / 8000) = 1/(8000 / 10897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15452299 / 50000000) (309045981 / 1000000000) (Real.log (10897 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (10897 / 8000) = -Real.log (8000 / 10897) := by
    rw [show ((10897 / 8000) : ℝ) = ((8000 / 10897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (449612939 / 1000000000) ≤ -Real.log (5103 / 8000) ∧
    -Real.log (5103 / 8000) ≤ (22480647 / 50000000) := by
  have h := checkLog_sound (w := (2897 / 13103)) (n := 12)
    (lo := (449612939 / 1000000000)) (hi := (22480647 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5103) = 1/(5103 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-22480647 / 50000000) (-449612939 / 1000000000) (Real.log (5103 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (309362347 / 1000000000) ≤ -Real.log (250000 / 340639) ∧
    -Real.log (250000 / 340639) ≤ (77340587 / 250000000) := by
  have h := checkLog_sound (w := (90639 / 590639)) (n := 12)
    (lo := (309362347 / 1000000000)) (hi := (77340587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340639 / 250000) = 1/(250000 / 340639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (309362347 / 1000000000) (77340587 / 250000000) (Real.log (340639 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (340639 / 250000) = -Real.log (250000 / 340639) := by
    rw [show ((340639 / 250000) : ℝ) = ((250000 / 340639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28143053 / 62500000) ≤ -Real.log (159361 / 250000) ∧
    -Real.log (159361 / 250000) ≤ (450288849 / 1000000000) := by
  have h := checkLog_sound (w := (90639 / 409361)) (n := 12)
    (lo := (28143053 / 62500000)) (hi := (450288849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159361) = 1/(159361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-450288849 / 1000000000) (-28143053 / 62500000) (Real.log (159361 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (117812269 / 500000000) ≤ -Real.log (1000000 / 1265699) ∧
    -Real.log (1000000 / 1265699) ≤ (235624539 / 1000000000) := by
  have h := checkLog_sound (w := (265699 / 2265699)) (n := 12)
    (lo := (117812269 / 500000000)) (hi := (235624539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265699 / 1000000) = 1/(1000000 / 1265699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (117812269 / 500000000) (235624539 / 1000000000) (Real.log (1265699 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1265699 / 1000000) = -Real.log (1000000 / 1265699) := by
    rw [show ((1265699 / 1000000) : ℝ) = ((1000000 / 1265699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77209063 / 250000000) ≤ -Real.log (734301 / 1000000) ∧
    -Real.log (734301 / 1000000) ≤ (308836253 / 1000000000) := by
  have h := checkLog_sound (w := (265699 / 1734301)) (n := 12)
    (lo := (77209063 / 250000000)) (hi := (308836253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734301) = 1/(734301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-308836253 / 1000000000) (-77209063 / 250000000) (Real.log (734301 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (117946959 / 500000000) ≤ -Real.log (25000 / 31651) ∧
    -Real.log (25000 / 31651) ≤ (235893919 / 1000000000) := by
  have h := checkLog_sound (w := (6651 / 56651)) (n := 12)
    (lo := (117946959 / 500000000)) (hi := (235893919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31651 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31651 / 25000) = 1/(25000 / 31651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (117946959 / 500000000) (235893919 / 1000000000) (Real.log (31651 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (31651 / 25000) = -Real.log (25000 / 31651) := by
    rw [show ((31651 / 25000) : ℝ) = ((25000 / 31651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (309300747 / 1000000000) ≤ -Real.log (18349 / 25000) ∧
    -Real.log (18349 / 25000) ≤ (77325187 / 250000000) := by
  have h := checkLog_sound (w := (6651 / 43349)) (n := 12)
    (lo := (309300747 / 1000000000)) (hi := (77325187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18349) = 1/(18349 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77325187 / 250000000) (-309300747 / 1000000000) (Real.log (18349 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (758658919 / 1000000000) ≤ -Real.log (31250000000 / 66731579463) ∧
    -Real.log (31250000000 / 66731579463) ≤ (758658921 / 1000000000) := by
  have h := checkLog_sound (w := (4231579463 / 129231579463)) (n := 12)
    (lo := (65511739 / 1000000000)) (hi := (3275587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66731579463 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66731579463 / 62500000000) = 1/(31250000000 / 66731579463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (758658919 / 1000000000) (758658921 / 1000000000) (Real.log (66731579463 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (66731579463 / 31250000000) = -Real.log (31250000000 / 66731579463) := by
    rw [show ((66731579463 / 31250000000) : ℝ) = ((31250000000 / 66731579463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (189912799 / 250000000) ≤ -Real.log (500000000000 / 1068765256243) ∧
    -Real.log (500000000000 / 1068765256243) ≤ (379825599 / 500000000) := by
  have h := checkLog_sound (w := (68765256243 / 2068765256243)) (n := 12)
    (lo := (4156501 / 62500000)) (hi := (66504017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068765256243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068765256243 / 1000000000000) = 1/(500000000000 / 1068765256243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (189912799 / 250000000) (379825599 / 500000000) (Real.log (1068765256243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1068765256243 / 500000000000) = -Real.log (500000000000 / 1068765256243) := by
    rw [show ((1068765256243 / 500000000000) : ℝ) = ((500000000000 / 1068765256243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (544460791 / 1000000000) ≤ -Real.log (250000000000 / 430919677353) ∧
    -Real.log (250000000000 / 430919677353) ≤ (68057599 / 125000000) := by
  have h := checkLog_sound (w := (180919677353 / 680919677353)) (n := 12)
    (lo := (544460791 / 1000000000)) (hi := (68057599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430919677353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430919677353 / 250000000000) = 1/(250000000000 / 430919677353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (544460791 / 1000000000) (68057599 / 125000000) (Real.log (430919677353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (430919677353 / 250000000000) = -Real.log (250000000000 / 430919677353) := by
    rw [show ((430919677353 / 250000000000) : ℝ) = ((250000000000 / 430919677353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (272597333 / 500000000) ≤ -Real.log (500000000000 / 862472069323) ∧
    -Real.log (500000000000 / 862472069323) ≤ (545194667 / 1000000000) := by
  have h := checkLog_sound (w := (362472069323 / 1362472069323)) (n := 12)
    (lo := (272597333 / 500000000)) (hi := (545194667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862472069323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862472069323 / 500000000000) = 1/(500000000000 / 862472069323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (272597333 / 500000000) (545194667 / 1000000000) (Real.log (862472069323 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (862472069323 / 500000000000) = -Real.log (500000000000 / 862472069323) := by
    rw [show ((862472069323 / 500000000000) : ℝ) = ((500000000000 / 862472069323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0292
