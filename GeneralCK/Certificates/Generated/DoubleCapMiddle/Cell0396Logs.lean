import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0396
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

theorem reflection_log_1_neg : (201185477 / 1000000000) ≤ -Real.log (5120 / 6261) ∧
    -Real.log (5120 / 6261) ≤ (100592739 / 500000000) := by
  have h := checkLog_sound (w := (1141 / 11381)) (n := 12)
    (lo := (201185477 / 1000000000)) (hi := (100592739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6261 / 5120) = 1/(5120 / 6261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201185477 / 1000000000) (100592739 / 500000000) (Real.log (6261 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6261 / 5120) = -Real.log (5120 / 6261) := by
    rw [show ((6261 / 5120) : ℝ) = ((5120 / 6261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252123907 / 1000000000) ≤ -Real.log (3979 / 5120) ∧
    -Real.log (3979 / 5120) ≤ (63030977 / 250000000) := by
  have h := checkLog_sound (w := (1141 / 9099)) (n := 12)
    (lo := (252123907 / 1000000000)) (hi := (63030977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3979) = 1/(3979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) (Real.log (3979 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20094587 / 100000000) ≤ -Real.log (10240 / 12519) ∧
    -Real.log (10240 / 12519) ≤ (200945871 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 22759)) (n := 12)
    (lo := (20094587 / 100000000)) (hi := (200945871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12519 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12519 / 10240) = 1/(10240 / 12519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20094587 / 100000000) (200945871 / 1000000000) (Real.log (12519 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12519 / 10240) = -Real.log (10240 / 12519) := by
    rw [show ((12519 / 10240) : ℝ) = ((10240 / 12519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251746999 / 1000000000) ≤ -Real.log (7961 / 10240) ∧
    -Real.log (7961 / 10240) ≤ (251747 / 1000000) := by
  have h := checkLog_sound (w := (2279 / 18201)) (n := 12)
    (lo := (251746999 / 1000000000)) (hi := (251747 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7961) = 1/(7961 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-251747 / 1000000) (-251746999 / 1000000000) (Real.log (7961 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184297897 / 500000000) ≤ -Real.log (2560 / 3701) ∧
    -Real.log (2560 / 3701) ≤ (73719159 / 200000000) := by
  have h := checkLog_sound (w := (1141 / 6261)) (n := 12)
    (lo := (184297897 / 500000000)) (hi := (73719159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3701 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3701 / 2560) = 1/(2560 / 3701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184297897 / 500000000) (73719159 / 200000000) (Real.log (3701 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3701 / 2560) = -Real.log (2560 / 3701) := by
    rw [show ((3701 / 2560) : ℝ) = ((2560 / 3701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29502743 / 50000000) ≤ -Real.log (1419 / 2560) ∧
    -Real.log (1419 / 2560) ≤ (590054861 / 1000000000) := by
  have h := checkLog_sound (w := (1141 / 3979)) (n := 12)
    (lo := (29502743 / 50000000)) (hi := (590054861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1419) = 1/(1419 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) (Real.log (1419 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23011901 / 62500000) ≤ -Real.log (5120 / 7399) ∧
    -Real.log (5120 / 7399) ≤ (368190417 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 12519)) (n := 12)
    (lo := (23011901 / 62500000)) (hi := (368190417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7399 / 5120) = 1/(5120 / 7399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23011901 / 62500000) (368190417 / 1000000000) (Real.log (7399 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7399 / 5120) = -Real.log (5120 / 7399) := by
    rw [show ((7399 / 5120) : ℝ) = ((5120 / 7399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9203099 / 15625000) ≤ -Real.log (2841 / 5120) ∧
    -Real.log (2841 / 5120) ≤ (588998337 / 1000000000) := by
  have h := checkLog_sound (w := (2279 / 7961)) (n := 12)
    (lo := (9203099 / 15625000)) (hi := (588998337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2841) = 1/(2841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-588998337 / 1000000000) (-9203099 / 15625000) (Real.log (2841 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137899119 / 500000000) ≤ -Real.log (500000 / 658791) ∧
    -Real.log (500000 / 658791) ≤ (275798239 / 1000000000) := by
  have h := checkLog_sound (w := (158791 / 1158791)) (n := 12)
    (lo := (137899119 / 500000000)) (hi := (275798239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658791 / 500000) = 1/(500000 / 658791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137899119 / 500000000) (275798239 / 1000000000) (Real.log (658791 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (658791 / 500000) = -Real.log (500000 / 658791) := by
    rw [show ((658791 / 500000) : ℝ) = ((500000 / 658791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76422581 / 200000000) ≤ -Real.log (341209 / 500000) ∧
    -Real.log (341209 / 500000) ≤ (191056453 / 500000000) := by
  have h := checkLog_sound (w := (158791 / 841209)) (n := 12)
    (lo := (76422581 / 200000000)) (hi := (191056453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341209) = 1/(341209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191056453 / 500000000) (-76422581 / 200000000) (Real.log (341209 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (276123023 / 1000000000) ≤ -Real.log (100000 / 131801) ∧
    -Real.log (100000 / 131801) ≤ (17257689 / 62500000) := by
  have h := checkLog_sound (w := (31801 / 231801)) (n := 12)
    (lo := (276123023 / 1000000000)) (hi := (17257689 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131801 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131801 / 100000) = 1/(100000 / 131801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (276123023 / 1000000000) (17257689 / 62500000) (Real.log (131801 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (131801 / 100000) = -Real.log (100000 / 131801) := by
    rw [show ((131801 / 100000) : ℝ) = ((100000 / 131801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95685071 / 250000000) ≤ -Real.log (68199 / 100000) ∧
    -Real.log (68199 / 100000) ≤ (76548057 / 200000000) := by
  have h := checkLog_sound (w := (31801 / 168199)) (n := 12)
    (lo := (95685071 / 250000000)) (hi := (76548057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68199) = 1/(68199 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76548057 / 200000000) (-95685071 / 250000000) (Real.log (68199 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10391911 / 50000000) ≤ -Real.log (500000 / 615507) ∧
    -Real.log (500000 / 615507) ≤ (207838221 / 1000000000) := by
  have h := checkLog_sound (w := (115507 / 1115507)) (n := 12)
    (lo := (10391911 / 50000000)) (hi := (207838221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615507 / 500000) = 1/(500000 / 615507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10391911 / 50000000) (207838221 / 1000000000) (Real.log (615507 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615507 / 500000) = -Real.log (500000 / 615507) := by
    rw [show ((615507 / 500000) : ℝ) = ((500000 / 615507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (52536503 / 200000000) ≤ -Real.log (384493 / 500000) ∧
    -Real.log (384493 / 500000) ≤ (65670629 / 250000000) := by
  have h := checkLog_sound (w := (115507 / 884493)) (n := 12)
    (lo := (52536503 / 200000000)) (hi := (65670629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384493) = 1/(384493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-65670629 / 250000000) (-52536503 / 200000000) (Real.log (384493 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208105443 / 1000000000) ≤ -Real.log (1000000 / 1231343) ∧
    -Real.log (1000000 / 1231343) ≤ (52026361 / 250000000) := by
  have h := checkLog_sound (w := (231343 / 2231343)) (n := 12)
    (lo := (208105443 / 1000000000)) (hi := (52026361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231343 / 1000000) = 1/(1000000 / 1231343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208105443 / 1000000000) (52026361 / 250000000) (Real.log (1231343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231343 / 1000000) = -Real.log (1000000 / 1231343) := by
    rw [show ((1231343 / 1000000) : ℝ) = ((1000000 / 1231343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (131555221 / 500000000) ≤ -Real.log (768657 / 1000000) ∧
    -Real.log (768657 / 1000000) ≤ (263110443 / 1000000000) := by
  have h := checkLog_sound (w := (231343 / 1768657)) (n := 12)
    (lo := (131555221 / 500000000)) (hi := (263110443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768657) = 1/(768657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-263110443 / 1000000000) (-131555221 / 500000000) (Real.log (768657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (82238893 / 125000000) ≤ -Real.log (500000000000 / 965377525211) ∧
    -Real.log (500000000000 / 965377525211) ≤ (131582229 / 200000000) := by
  have h := checkLog_sound (w := (465377525211 / 1465377525211)) (n := 12)
    (lo := (82238893 / 125000000)) (hi := (131582229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965377525211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965377525211 / 500000000000) = 1/(500000000000 / 965377525211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (82238893 / 125000000) (131582229 / 200000000) (Real.log (965377525211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (965377525211 / 500000000000) = -Real.log (500000000000 / 965377525211) := by
    rw [show ((965377525211 / 500000000000) : ℝ) = ((500000000000 / 965377525211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (658863307 / 1000000000) ≤ -Real.log (500000000000 / 966297159783) ∧
    -Real.log (500000000000 / 966297159783) ≤ (164715827 / 250000000) := by
  have h := checkLog_sound (w := (466297159783 / 1466297159783)) (n := 12)
    (lo := (658863307 / 1000000000)) (hi := (164715827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966297159783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966297159783 / 500000000000) = 1/(500000000000 / 966297159783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (658863307 / 1000000000) (164715827 / 250000000) (Real.log (966297159783 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (966297159783 / 500000000000) = -Real.log (500000000000 / 966297159783) := by
    rw [show ((966297159783 / 500000000000) : ℝ) = ((500000000000 / 966297159783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (94104147 / 200000000) ≤ -Real.log (125000000000 / 200103447917) ∧
    -Real.log (125000000000 / 200103447917) ≤ (14703773 / 31250000) := by
  have h := checkLog_sound (w := (75103447917 / 325103447917)) (n := 12)
    (lo := (94104147 / 200000000)) (hi := (14703773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200103447917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200103447917 / 125000000000) = 1/(125000000000 / 200103447917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (94104147 / 200000000) (14703773 / 31250000) (Real.log (200103447917 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (200103447917 / 125000000000) = -Real.log (125000000000 / 200103447917) := by
    rw [show ((200103447917 / 125000000000) : ℝ) = ((125000000000 / 200103447917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (235607943 / 500000000) ≤ -Real.log (500000000000 / 800970393817) ∧
    -Real.log (500000000000 / 800970393817) ≤ (471215887 / 1000000000) := by
  have h := checkLog_sound (w := (300970393817 / 1300970393817)) (n := 12)
    (lo := (235607943 / 500000000)) (hi := (471215887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800970393817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800970393817 / 500000000000) = 1/(500000000000 / 800970393817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (235607943 / 500000000) (471215887 / 1000000000) (Real.log (800970393817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (800970393817 / 500000000000) = -Real.log (500000000000 / 800970393817) := by
    rw [show ((800970393817 / 500000000000) : ℝ) = ((500000000000 / 800970393817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0396
