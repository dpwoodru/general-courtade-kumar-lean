import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0293
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

theorem reflection_log_1_neg : (112781249 / 500000000) ≤ -Real.log (10240 / 12831) ∧
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


theorem reflection_log_1 : Bounds (112781249 / 500000000) (225562499 / 1000000000) (Real.log (12831 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12831 / 10240) = -Real.log (10240 / 12831) := by
    rw [show ((12831 / 10240) : ℝ) = ((10240 / 12831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291726699 / 1000000000) ≤ -Real.log (7649 / 10240) ∧
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


theorem reflection_log_2 : Bounds (-2917267 / 10000000) (-291726699 / 1000000000) (Real.log (7649 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (112664331 / 500000000) ≤ -Real.log (2560 / 3207) ∧
    -Real.log (2560 / 3207) ≤ (225328663 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 5767)) (n := 12)
    (lo := (112664331 / 500000000)) (hi := (225328663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3207 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3207 / 2560) = 1/(2560 / 3207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (112664331 / 500000000) (225328663 / 1000000000) (Real.log (3207 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3207 / 2560) = -Real.log (2560 / 3207) := by
    rw [show ((3207 / 2560) : ℝ) = ((2560 / 3207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36416821 / 125000000) ≤ -Real.log (1913 / 2560) ∧
    -Real.log (1913 / 2560) ≤ (291334569 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 4473)) (n := 12)
    (lo := (36416821 / 125000000)) (hi := (291334569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1913) = 1/(1913 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-291334569 / 1000000000) (-36416821 / 125000000) (Real.log (1913 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (409493441 / 1000000000) ≤ -Real.log (5120 / 7711) ∧
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


theorem reflection_log_5 : Bounds (409493441 / 1000000000) (204746721 / 500000000) (Real.log (7711 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7711 / 5120) = -Real.log (5120 / 7711) := by
    rw [show ((7711 / 5120) : ℝ) = ((5120 / 7711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70533047 / 100000000) ≤ -Real.log (2529 / 5120) ∧
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


theorem reflection_log_6 : Bounds (-88166309 / 125000000) (-70533047 / 100000000) (Real.log (2529 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (409104311 / 1000000000) ≤ -Real.log (1280 / 1927) ∧
    -Real.log (1280 / 1927) ≤ (51138039 / 125000000) := by
  have h := checkLog_sound (w := (647 / 3207)) (n := 12)
    (lo := (409104311 / 1000000000)) (hi := (51138039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927 / 1280) = 1/(1280 / 1927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (409104311 / 1000000000) (51138039 / 125000000) (Real.log (1927 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1927 / 1280) = -Real.log (1280 / 1927) := by
    rw [show ((1927 / 1280) : ℝ) = ((1280 / 1927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (352072467 / 500000000) ≤ -Real.log (633 / 1280) ∧
    -Real.log (633 / 1280) ≤ (88018117 / 125000000) := by
  have h := checkLog_sound (w := (7 / 1273)) (n := 12)
    (lo := (5498877 / 500000000)) (hi := (2199551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 633) = 1/(633 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88018117 / 125000000) (-352072467 / 500000000) (Real.log (633 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38591189 / 125000000) ≤ -Real.log (500000 / 680847) ∧
    -Real.log (500000 / 680847) ≤ (308729513 / 1000000000) := by
  have h := checkLog_sound (w := (180847 / 1180847)) (n := 12)
    (lo := (38591189 / 125000000)) (hi := (308729513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680847 / 500000) = 1/(500000 / 680847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38591189 / 125000000) (308729513 / 1000000000) (Real.log (680847 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (680847 / 500000) = -Real.log (500000 / 680847) := by
    rw [show ((680847 / 500000) : ℝ) = ((500000 / 680847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (224468743 / 500000000) ≤ -Real.log (319153 / 500000) ∧
    -Real.log (319153 / 500000) ≤ (448937487 / 1000000000) := by
  have h := checkLog_sound (w := (180847 / 819153)) (n := 12)
    (lo := (224468743 / 500000000)) (hi := (448937487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319153) = 1/(319153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-448937487 / 1000000000) (-224468743 / 500000000) (Real.log (319153 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154523357 / 500000000) ≤ -Real.log (500000 / 681063) ∧
    -Real.log (500000 / 681063) ≤ (61809343 / 200000000) := by
  have h := checkLog_sound (w := (181063 / 1181063)) (n := 12)
    (lo := (154523357 / 500000000)) (hi := (61809343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681063 / 500000) = 1/(500000 / 681063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154523357 / 500000000) (61809343 / 200000000) (Real.log (681063 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (681063 / 500000) = -Real.log (500000 / 681063) := by
    rw [show ((681063 / 500000) : ℝ) = ((500000 / 681063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (449614507 / 1000000000) ≤ -Real.log (318937 / 500000) ∧
    -Real.log (318937 / 500000) ≤ (112403627 / 250000000) := by
  have h := checkLog_sound (w := (181063 / 818937)) (n := 12)
    (lo := (449614507 / 1000000000)) (hi := (112403627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 318937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 318937) = 1/(318937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-112403627 / 250000000) (-449614507 / 1000000000) (Real.log (318937 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (117678333 / 500000000) ≤ -Real.log (12500 / 15817) ∧
    -Real.log (12500 / 15817) ≤ (235356667 / 1000000000) := by
  have h := checkLog_sound (w := (3317 / 28317)) (n := 12)
    (lo := (117678333 / 500000000)) (hi := (235356667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15817 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15817 / 12500) = 1/(12500 / 15817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (117678333 / 500000000) (235356667 / 1000000000) (Real.log (15817 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (15817 / 12500) = -Real.log (12500 / 15817) := by
    rw [show ((15817 / 12500) : ℝ) = ((12500 / 15817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61674939 / 200000000) ≤ -Real.log (9183 / 12500) ∧
    -Real.log (9183 / 12500) ≤ (38546837 / 125000000) := by
  have h := checkLog_sound (w := (3317 / 21683)) (n := 12)
    (lo := (61674939 / 200000000)) (hi := (38546837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9183) = 1/(9183 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38546837 / 125000000) (-61674939 / 200000000) (Real.log (9183 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14726583 / 62500000) ≤ -Real.log (10000 / 12657) ∧
    -Real.log (10000 / 12657) ≤ (235625329 / 1000000000) := by
  have h := checkLog_sound (w := (2657 / 22657)) (n := 12)
    (lo := (14726583 / 62500000)) (hi := (235625329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10000) = 1/(10000 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14726583 / 62500000) (235625329 / 1000000000) (Real.log (12657 / 10000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (12657 / 10000) = -Real.log (10000 / 12657) := by
    rw [show ((12657 / 10000) : ℝ) = ((10000 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (154418807 / 500000000) ≤ -Real.log (7343 / 10000) ∧
    -Real.log (7343 / 10000) ≤ (61767523 / 200000000) := by
  have h := checkLog_sound (w := (2657 / 17343)) (n := 12)
    (lo := (154418807 / 500000000)) (hi := (61767523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7343) = 1/(7343 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-61767523 / 200000000) (-154418807 / 500000000) (Real.log (7343 / 10000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (757666999 / 1000000000) ≤ -Real.log (500000000000 / 1066646718031) ∧
    -Real.log (500000000000 / 1066646718031) ≤ (757667001 / 1000000000) := by
  have h := checkLog_sound (w := (66646718031 / 2066646718031)) (n := 12)
    (lo := (64519819 / 1000000000)) (hi := (3225991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066646718031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066646718031 / 1000000000000) = 1/(500000000000 / 1066646718031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (757666999 / 1000000000) (757667001 / 1000000000) (Real.log (1066646718031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1066646718031 / 500000000000) = -Real.log (500000000000 / 1066646718031) := by
    rw [show ((1066646718031 / 500000000000) : ℝ) = ((500000000000 / 1066646718031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (758661221 / 1000000000) ≤ -Real.log (500000000000 / 1067707729113) ∧
    -Real.log (500000000000 / 1067707729113) ≤ (758661223 / 1000000000) := by
  have h := checkLog_sound (w := (67707729113 / 2067707729113)) (n := 12)
    (lo := (65514041 / 1000000000)) (hi := (32757021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067707729113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067707729113 / 1000000000000) = 1/(500000000000 / 1067707729113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (758661221 / 1000000000) (758661223 / 1000000000) (Real.log (1067707729113 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1067707729113 / 500000000000) = -Real.log (500000000000 / 1067707729113) := by
    rw [show ((1067707729113 / 500000000000) : ℝ) = ((500000000000 / 1067707729113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (271865681 / 500000000) ≤ -Real.log (250000000000 / 430605466623) ∧
    -Real.log (250000000000 / 430605466623) ≤ (543731363 / 1000000000) := by
  have h := checkLog_sound (w := (180605466623 / 680605466623)) (n := 12)
    (lo := (271865681 / 500000000)) (hi := (543731363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430605466623 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430605466623 / 250000000000) = 1/(250000000000 / 430605466623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (271865681 / 500000000) (543731363 / 1000000000) (Real.log (430605466623 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (430605466623 / 250000000000) = -Real.log (250000000000 / 430605466623) := by
    rw [show ((430605466623 / 250000000000) : ℝ) = ((250000000000 / 430605466623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (544462943 / 1000000000) ≤ -Real.log (100000000000 / 172368241863) ∧
    -Real.log (100000000000 / 172368241863) ≤ (17014467 / 31250000) := by
  have h := checkLog_sound (w := (72368241863 / 272368241863)) (n := 12)
    (lo := (544462943 / 1000000000)) (hi := (17014467 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172368241863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172368241863 / 100000000000) = 1/(100000000000 / 172368241863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (544462943 / 1000000000) (17014467 / 31250000) (Real.log (172368241863 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (172368241863 / 100000000000) = -Real.log (100000000000 / 172368241863) := by
    rw [show ((172368241863 / 100000000000) : ℝ) = ((100000000000 / 172368241863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0293
