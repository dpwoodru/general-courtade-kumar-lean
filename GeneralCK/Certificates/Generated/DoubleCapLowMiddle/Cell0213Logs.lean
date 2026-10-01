import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0213
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

theorem reflection_log_1_neg : (274241307 / 500000000) ≤ -Real.log (1600 / 2769) ∧
    -Real.log (1600 / 2769) ≤ (109696523 / 200000000) := by
  have h := checkLog_sound (w := (1169 / 4369)) (n := 12)
    (lo := (274241307 / 500000000)) (hi := (109696523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2769 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2769 / 1600) = 1/(1600 / 2769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (274241307 / 500000000) (109696523 / 200000000) (Real.log (2769 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2769 / 1600) = -Real.log (1600 / 2769) := by
    rw [show ((2769 / 1600) : ℝ) = ((1600 / 2769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1311650817 / 1000000000) ≤ -Real.log (431 / 1600) ∧
    -Real.log (431 / 1600) ≤ (1311650819 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 431) = 1/(431 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1311650819 / 1000000000) (-1311650817 / 1000000000) (Real.log (431 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272522937 / 500000000) ≤ -Real.log (3200 / 5519) ∧
    -Real.log (3200 / 5519) ≤ (4360367 / 8000000) := by
  have h := checkLog_sound (w := (2319 / 8719)) (n := 12)
    (lo := (272522937 / 500000000)) (hi := (4360367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5519 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5519 / 3200) = 1/(3200 / 5519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272522937 / 500000000) (4360367 / 8000000) (Real.log (5519 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5519 / 3200) = -Real.log (3200 / 5519) := by
    rw [show ((5519 / 3200) : ℝ) = ((3200 / 5519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (644924231 / 500000000) ≤ -Real.log (881 / 3200) ∧
    -Real.log (881 / 3200) ≤ (80615529 / 62500000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 881) = 1/(881 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80615529 / 62500000) (-644924231 / 500000000) (Real.log (881 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (379292233 / 1000000000) ≤ -Real.log (800 / 1169) ∧
    -Real.log (800 / 1169) ≤ (189646117 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1969)) (n := 12)
    (lo := (379292233 / 1000000000)) (hi := (189646117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 800) = 1/(800 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (379292233 / 1000000000) (189646117 / 500000000) (Real.log (1169 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1169 / 800) = -Real.log (800 / 1169) := by
    rw [show ((1169 / 800) : ℝ) = ((800 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (618503637 / 1000000000) ≤ -Real.log (431 / 800) ∧
    -Real.log (431 / 800) ≤ (309251819 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 431) = 1/(431 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-309251819 / 500000000) (-618503637 / 1000000000) (Real.log (431 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (371132429 / 1000000000) ≤ -Real.log (1600 / 2319) ∧
    -Real.log (1600 / 2319) ≤ (37113243 / 100000000) := by
  have h := checkLog_sound (w := (719 / 3919)) (n := 12)
    (lo := (371132429 / 1000000000)) (hi := (37113243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2319 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2319 / 1600) = 1/(1600 / 2319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (371132429 / 1000000000) (37113243 / 100000000) (Real.log (2319 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2319 / 1600) = -Real.log (1600 / 2319) := by
    rw [show ((2319 / 1600) : ℝ) = ((1600 / 2319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298350641 / 500000000) ≤ -Real.log (881 / 1600) ∧
    -Real.log (881 / 1600) ≤ (596701283 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 881) = 1/(881 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-596701283 / 1000000000) (-298350641 / 500000000) (Real.log (881 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75341867 / 125000000) ≤ -Real.log (1000000 / 1827109) ∧
    -Real.log (1000000 / 1827109) ≤ (602734937 / 1000000000) := by
  have h := checkLog_sound (w := (827109 / 2827109)) (n := 12)
    (lo := (75341867 / 125000000)) (hi := (602734937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827109 / 1000000) = 1/(1000000 / 1827109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75341867 / 125000000) (602734937 / 1000000000) (Real.log (1827109 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1827109 / 1000000) = -Real.log (1000000 / 1827109) := by
    rw [show ((1827109 / 1000000) : ℝ) = ((1000000 / 1827109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1755093939 / 1000000000) ≤ -Real.log (172891 / 1000000) ∧
    -Real.log (172891 / 1000000) ≤ (877546971 / 500000000) := by
  have h := checkLog_sound (w := (77109 / 422891)) (n := 12)
    (lo := (368799579 / 1000000000)) (hi := (18439979 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172891) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 172891) = 1/(172891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-877546971 / 500000000) (-1755093939 / 1000000000) (Real.log (172891 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302042123 / 500000000) ≤ -Real.log (125000 / 228697) ∧
    -Real.log (125000 / 228697) ≤ (604084247 / 1000000000) := by
  have h := checkLog_sound (w := (103697 / 353697)) (n := 12)
    (lo := (302042123 / 500000000)) (hi := (604084247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228697 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228697 / 125000) = 1/(125000 / 228697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302042123 / 500000000) (604084247 / 1000000000) (Real.log (228697 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (228697 / 125000) = -Real.log (125000 / 228697) := by
    rw [show ((228697 / 125000) : ℝ) = ((125000 / 228697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (442366457 / 250000000) ≤ -Real.log (21303 / 125000) ∧
    -Real.log (21303 / 125000) ≤ (1769465831 / 1000000000) := by
  have h := checkLog_sound (w := (9947 / 52553)) (n := 12)
    (lo := (95792867 / 250000000)) (hi := (383171469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 21303) = 1/(21303 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1769465831 / 1000000000) (-442366457 / 250000000) (Real.log (21303 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (146971387 / 250000000) ≤ -Real.log (500000 / 900089) ∧
    -Real.log (500000 / 900089) ≤ (587885549 / 1000000000) := by
  have h := checkLog_sound (w := (400089 / 1400089)) (n := 12)
    (lo := (146971387 / 250000000)) (hi := (587885549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900089 / 500000) = 1/(500000 / 900089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (146971387 / 250000000) (587885549 / 1000000000) (Real.log (900089 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (900089 / 500000) = -Real.log (500000 / 900089) := by
    rw [show ((900089 / 500000) : ℝ) = ((500000 / 900089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1610328307 / 1000000000) ≤ -Real.log (99911 / 500000) ∧
    -Real.log (99911 / 500000) ≤ (161032831 / 100000000) := by
  have h := checkLog_sound (w := (25089 / 224911)) (n := 12)
    (lo := (224033947 / 1000000000)) (hi := (56008487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99911) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 99911) = 1/(99911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-161032831 / 100000000) (-1610328307 / 1000000000) (Real.log (99911 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (295020117 / 500000000) ≤ -Real.log (1000000 / 1804061) ∧
    -Real.log (1000000 / 1804061) ≤ (118008047 / 200000000) := by
  have h := checkLog_sound (w := (804061 / 2804061)) (n := 12)
    (lo := (295020117 / 500000000)) (hi := (118008047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1804061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1804061 / 1000000) = 1/(1000000 / 1804061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (295020117 / 500000000) (118008047 / 200000000) (Real.log (1804061 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1804061 / 1000000) = -Real.log (1000000 / 1804061) := by
    rw [show ((1804061 / 1000000) : ℝ) = ((1000000 / 1804061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1629951891 / 1000000000) ≤ -Real.log (195939 / 1000000) ∧
    -Real.log (195939 / 1000000) ≤ (814975947 / 500000000) := by
  have h := checkLog_sound (w := (54061 / 445939)) (n := 12)
    (lo := (243657531 / 1000000000)) (hi := (60914383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195939) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 195939) = 1/(195939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-814975947 / 500000000) (-1629951891 / 1000000000) (Real.log (195939 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18862631 / 8000000) ≤ -Real.log (500000000000 / 5283991069517) ∧
    -Real.log (500000000000 / 5283991069517) ≤ (2357828879 / 1000000000) := by
  have h := checkLog_sound (w := (1283991069517 / 9283991069517)) (n := 12)
    (lo := (55677467 / 200000000)) (hi := (34798417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5283991069517 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5283991069517 / 4000000000000) = 1/(500000000000 / 5283991069517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18862631 / 8000000) (2357828879 / 1000000000) (Real.log (5283991069517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5283991069517 / 500000000000) = -Real.log (500000000000 / 5283991069517) := by
    rw [show ((5283991069517 / 500000000000) : ℝ) = ((500000000000 / 5283991069517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2373550073 / 1000000000) ≤ -Real.log (250000000000 / 2683859080881) ∧
    -Real.log (250000000000 / 2683859080881) ≤ (2373550077 / 1000000000) := by
  have h := checkLog_sound (w := (683859080881 / 4683859080881)) (n := 12)
    (lo := (294108533 / 1000000000)) (hi := (147054267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2683859080881 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2683859080881 / 2000000000000) = 1/(250000000000 / 2683859080881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2373550073 / 1000000000) (2373550077 / 1000000000) (Real.log (2683859080881 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2683859080881 / 250000000000) = -Real.log (250000000000 / 2683859080881) := by
    rw [show ((2683859080881 / 250000000000) : ℝ) = ((250000000000 / 2683859080881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (439642771 / 200000000) ≤ -Real.log (500000000000 / 4504453964027) ∧
    -Real.log (500000000000 / 4504453964027) ≤ (2198213859 / 1000000000) := by
  have h := checkLog_sound (w := (504453964027 / 8504453964027)) (n := 12)
    (lo := (23754463 / 200000000)) (hi := (29693079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4504453964027 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4504453964027 / 4000000000000) = 1/(500000000000 / 4504453964027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (439642771 / 200000000) (2198213859 / 1000000000) (Real.log (4504453964027 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4504453964027 / 500000000000) = -Real.log (500000000000 / 4504453964027) := by
    rw [show ((4504453964027 / 500000000000) : ℝ) = ((500000000000 / 4504453964027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (17759937 / 8000000) ≤ -Real.log (250000000000 / 2301814595359) ∧
    -Real.log (250000000000 / 2301814595359) ≤ (2219992129 / 1000000000) := by
  have h := checkLog_sound (w := (301814595359 / 4301814595359)) (n := 12)
    (lo := (28110117 / 200000000)) (hi := (70275293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2301814595359 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2301814595359 / 2000000000000) = 1/(250000000000 / 2301814595359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (17759937 / 8000000) (2219992129 / 1000000000) (Real.log (2301814595359 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2301814595359 / 250000000000) = -Real.log (250000000000 / 2301814595359) := by
    rw [show ((2301814595359 / 250000000000) : ℝ) = ((250000000000 / 2301814595359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0213
