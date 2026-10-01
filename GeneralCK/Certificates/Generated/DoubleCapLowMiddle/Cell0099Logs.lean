import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0099
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

theorem reflection_log_1_neg : (335799151 / 500000000) ≤ -Real.log (51200 / 100217) ∧
    -Real.log (51200 / 100217) ≤ (671598303 / 1000000000) := by
  have h := checkLog_sound (w := (49017 / 151417)) (n := 12)
    (lo := (335799151 / 500000000)) (hi := (671598303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100217 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100217 / 51200) = 1/(51200 / 100217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335799151 / 500000000) (671598303 / 1000000000) (Real.log (100217 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100217 / 51200) = -Real.log (51200 / 100217) := by
    rw [show ((100217 / 51200) : ℝ) = ((51200 / 100217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (788759863 / 250000000) ≤ -Real.log (2183 / 51200) ∧
    -Real.log (2183 / 51200) ≤ (3155039457 / 1000000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2183) = 1/(2183 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3155039457 / 1000000000) (-788759863 / 250000000) (Real.log (2183 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83926087 / 125000000) ≤ -Real.log (25600 / 50099) ∧
    -Real.log (25600 / 50099) ≤ (671408697 / 1000000000) := by
  have h := checkLog_sound (w := (24499 / 75699)) (n := 12)
    (lo := (83926087 / 125000000)) (hi := (671408697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50099 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50099 / 25600) = 1/(25600 / 50099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83926087 / 125000000) (671408697 / 1000000000) (Real.log (50099 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50099 / 25600) = -Real.log (25600 / 50099) := by
    rw [show ((50099 / 25600) : ℝ) = ((25600 / 50099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3146373491 / 1000000000) ≤ -Real.log (1101 / 25600) ∧
    -Real.log (1101 / 25600) ≤ (393296687 / 125000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1101) = 1/(1101 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393296687 / 125000000) (-3146373491 / 1000000000) (Real.log (1101 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25982993 / 40000000) ≤ -Real.log (25600 / 49017) ∧
    -Real.log (25600 / 49017) ≤ (324787413 / 500000000) := by
  have h := checkLog_sound (w := (23417 / 74617)) (n := 12)
    (lo := (25982993 / 40000000)) (hi := (324787413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49017 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49017 / 25600) = 1/(25600 / 49017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25982993 / 40000000) (324787413 / 500000000) (Real.log (49017 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49017 / 25600) = -Real.log (25600 / 49017) := by
    rw [show ((49017 / 25600) : ℝ) = ((25600 / 49017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153868267 / 62500000) ≤ -Real.log (2183 / 25600) ∧
    -Real.log (2183 / 25600) ≤ (615473069 / 250000000) := by
  have h := checkLog_sound (w := (1017 / 5383)) (n := 12)
    (lo := (95612683 / 250000000)) (hi := (382450733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2183) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2183) = 1/(2183 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-615473069 / 250000000) (-153868267 / 62500000) (Real.log (2183 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (649187129 / 1000000000) ≤ -Real.log (12800 / 24499) ∧
    -Real.log (12800 / 24499) ≤ (64918713 / 100000000) := by
  have h := checkLog_sound (w := (11699 / 37299)) (n := 12)
    (lo := (649187129 / 1000000000)) (hi := (64918713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24499 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24499 / 12800) = 1/(12800 / 24499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (649187129 / 1000000000) (64918713 / 100000000) (Real.log (24499 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24499 / 12800) = -Real.log (12800 / 24499) := by
    rw [show ((24499 / 12800) : ℝ) = ((12800 / 24499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2453226311 / 1000000000) ≤ -Real.log (1101 / 12800) ∧
    -Real.log (1101 / 12800) ≤ (490645263 / 200000000) := by
  have h := checkLog_sound (w := (499 / 2701)) (n := 12)
    (lo := (373784771 / 1000000000)) (hi := (93446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1101) = 1/(1101 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-490645263 / 200000000) (-2453226311 / 1000000000) (Real.log (1101 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135070559 / 200000000) ≤ -Real.log (500000 / 982363) ∧
    -Real.log (500000 / 982363) ≤ (168838199 / 250000000) := by
  have h := checkLog_sound (w := (482363 / 1482363)) (n := 12)
    (lo := (135070559 / 200000000)) (hi := (168838199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982363 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982363 / 500000) = 1/(500000 / 982363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135070559 / 200000000) (168838199 / 250000000) (Real.log (982363 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (982363 / 500000) = -Real.log (500000 / 982363) := by
    rw [show ((982363 / 500000) : ℝ) = ((500000 / 982363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (418076141 / 125000000) ≤ -Real.log (17637 / 500000) ∧
    -Real.log (17637 / 500000) ≤ (3344609133 / 1000000000) := by
  have h := checkLog_sound (w := (13613 / 48887)) (n := 12)
    (lo := (71502551 / 125000000)) (hi := (572020409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17637) = 1/(17637 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3344609133 / 1000000000) (-418076141 / 125000000) (Real.log (17637 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (675498861 / 1000000000) ≤ -Real.log (1000000 / 1965013) ∧
    -Real.log (1000000 / 1965013) ≤ (337749431 / 500000000) := by
  have h := checkLog_sound (w := (965013 / 2965013)) (n := 12)
    (lo := (675498861 / 1000000000)) (hi := (337749431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965013 / 1000000) = 1/(1000000 / 1965013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (675498861 / 1000000000) (337749431 / 500000000) (Real.log (1965013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1965013 / 1000000) = -Real.log (1000000 / 1965013) := by
    rw [show ((1965013 / 1000000) : ℝ) = ((1000000 / 1965013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (419097339 / 125000000) ≤ -Real.log (34987 / 1000000) ∧
    -Real.log (34987 / 1000000) ≤ (3352778717 / 1000000000) := by
  have h := checkLog_sound (w := (27513 / 97487)) (n := 12)
    (lo := (72523749 / 125000000)) (hi := (580189993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34987) = 1/(34987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3352778717 / 1000000000) (-419097339 / 125000000) (Real.log (34987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67517871 / 100000000) ≤ -Real.log (31250 / 61387) ∧
    -Real.log (31250 / 61387) ≤ (675178711 / 1000000000) := by
  have h := checkLog_sound (w := (30137 / 92637)) (n := 12)
    (lo := (67517871 / 100000000)) (hi := (675178711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61387 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61387 / 31250) = 1/(31250 / 61387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67517871 / 100000000) (675178711 / 1000000000) (Real.log (61387 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61387 / 31250) = -Real.log (31250 / 61387) := by
    rw [show ((61387 / 31250) : ℝ) = ((31250 / 61387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3334960301 / 1000000000) ≤ -Real.log (1113 / 31250) ∧
    -Real.log (1113 / 31250) ≤ (1667480153 / 500000000) := by
  have h := checkLog_sound (w := (6721 / 24529)) (n := 12)
    (lo := (562371581 / 1000000000)) (hi := (281185791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8904) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8904) = 1/(1113 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1667480153 / 500000000) (-3334960301 / 1000000000) (Real.log (1113 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675328873 / 1000000000) ≤ -Real.log (1000000 / 1964679) ∧
    -Real.log (1000000 / 1964679) ≤ (337664437 / 500000000) := by
  have h := checkLog_sound (w := (964679 / 2964679)) (n := 12)
    (lo := (675328873 / 1000000000)) (hi := (337664437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964679 / 1000000) = 1/(1000000 / 1964679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675328873 / 1000000000) (337664437 / 500000000) (Real.log (1964679 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1964679 / 1000000) = -Real.log (1000000 / 1964679) := by
    rw [show ((1964679 / 1000000) : ℝ) = ((1000000 / 1964679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (835819397 / 250000000) ≤ -Real.log (35321 / 1000000) ∧
    -Real.log (35321 / 1000000) ≤ (3343277593 / 1000000000) := by
  have h := checkLog_sound (w := (27179 / 97821)) (n := 12)
    (lo := (142672217 / 250000000)) (hi := (570688869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35321) = 1/(35321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3343277593 / 1000000000) (-835819397 / 250000000) (Real.log (35321 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2009980961 / 500000000) ≤ -Real.log (500000000000 / 27849492544083) ∧
    -Real.log (500000000000 / 27849492544083) ≤ (502495241 / 125000000) := by
  have h := checkLog_sound (w := (11849492544083 / 43849492544083)) (n := 12)
    (lo := (277113011 / 500000000)) (hi := (554226023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27849492544083 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27849492544083 / 16000000000000) = 1/(500000000000 / 27849492544083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2009980961 / 500000000) (502495241 / 125000000) (Real.log (27849492544083 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27849492544083 / 500000000000) = -Real.log (500000000000 / 27849492544083) := by
    rw [show ((27849492544083 / 500000000000) : ℝ) = ((500000000000 / 27849492544083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4028277573 / 1000000000) ≤ -Real.log (500000000000 / 28082044759483) ∧
    -Real.log (500000000000 / 28082044759483) ≤ (4028277579 / 1000000000) := by
  have h := checkLog_sound (w := (12082044759483 / 44082044759483)) (n := 12)
    (lo := (562541673 / 1000000000)) (hi := (281270837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28082044759483 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28082044759483 / 16000000000000) = 1/(500000000000 / 28082044759483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4028277573 / 1000000000) (4028277579 / 1000000000) (Real.log (28082044759483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28082044759483 / 500000000000) = -Real.log (500000000000 / 28082044759483) := by
    rw [show ((28082044759483 / 500000000000) : ℝ) = ((500000000000 / 28082044759483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4010139011 / 1000000000) ≤ -Real.log (250000000000 / 13788634321653) ∧
    -Real.log (250000000000 / 13788634321653) ≤ (4010139017 / 1000000000) := by
  have h := checkLog_sound (w := (5788634321653 / 21788634321653)) (n := 12)
    (lo := (544403111 / 1000000000)) (hi := (68050389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13788634321653 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13788634321653 / 8000000000000) = 1/(250000000000 / 13788634321653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4010139011 / 1000000000) (4010139017 / 1000000000) (Real.log (13788634321653 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13788634321653 / 250000000000) = -Real.log (250000000000 / 13788634321653) := by
    rw [show ((13788634321653 / 250000000000) : ℝ) = ((250000000000 / 13788634321653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4018606461 / 1000000000) ≤ -Real.log (250000000000 / 13905884601229) ∧
    -Real.log (250000000000 / 13905884601229) ≤ (4018606467 / 1000000000) := by
  have h := checkLog_sound (w := (5905884601229 / 21905884601229)) (n := 12)
    (lo := (552870561 / 1000000000)) (hi := (276435281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13905884601229 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13905884601229 / 8000000000000) = 1/(250000000000 / 13905884601229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4018606461 / 1000000000) (4018606467 / 1000000000) (Real.log (13905884601229 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13905884601229 / 250000000000) = -Real.log (250000000000 / 13905884601229) := by
    rw [show ((13905884601229 / 250000000000) : ℝ) = ((250000000000 / 13905884601229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0099
