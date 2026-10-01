import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056
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

theorem reflection_log_1_neg : (678494453 / 1000000000) ≤ -Real.log (102400 / 201821) ∧
    -Real.log (102400 / 201821) ≤ (339247227 / 500000000) := by
  have h := checkLog_sound (w := (99421 / 304221)) (n := 12)
    (lo := (678494453 / 1000000000)) (hi := (339247227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201821 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201821 / 102400) = 1/(102400 / 201821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678494453 / 1000000000) (339247227 / 500000000) (Real.log (201821 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201821 / 102400) = -Real.log (102400 / 201821) := by
    rw [show ((201821 / 102400) : ℝ) = ((102400 / 201821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (884324759 / 250000000) ≤ -Real.log (2979 / 102400) ∧
    -Real.log (2979 / 102400) ≤ (1768649521 / 500000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2979) = 1/(2979 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1768649521 / 500000000) (-884324759 / 250000000) (Real.log (2979 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339200153 / 500000000) ≤ -Real.log (51200 / 100901) ∧
    -Real.log (51200 / 100901) ≤ (678400307 / 1000000000) := by
  have h := checkLog_sound (w := (49701 / 152101)) (n := 12)
    (lo := (339200153 / 500000000)) (hi := (678400307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100901 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100901 / 51200) = 1/(51200 / 100901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339200153 / 500000000) (678400307 / 1000000000) (Real.log (100901 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100901 / 51200) = -Real.log (51200 / 100901) := by
    rw [show ((100901 / 51200) : ℝ) = ((51200 / 100901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (353094131 / 100000000) ≤ -Real.log (1499 / 51200) ∧
    -Real.log (1499 / 51200) ≤ (882735329 / 250000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1499) = 1/(1499 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-882735329 / 250000000) (-353094131 / 100000000) (Real.log (1499 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331811913 / 500000000) ≤ -Real.log (51200 / 99421) ∧
    -Real.log (51200 / 99421) ≤ (663623827 / 1000000000) := by
  have h := checkLog_sound (w := (48221 / 150621)) (n := 12)
    (lo := (331811913 / 500000000)) (hi := (663623827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99421 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99421 / 51200) = 1/(51200 / 99421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (331811913 / 500000000) (663623827 / 1000000000) (Real.log (99421 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99421 / 51200) = -Real.log (51200 / 99421) := by
    rw [show ((99421 / 51200) : ℝ) = ((51200 / 99421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (177759491 / 62500000) ≤ -Real.log (2979 / 51200) ∧
    -Real.log (2979 / 51200) ≤ (2844151861 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2979) = 1/(2979 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2844151861 / 1000000000) (-177759491 / 62500000) (Real.log (2979 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331716351 / 500000000) ≤ -Real.log (25600 / 49701) ∧
    -Real.log (25600 / 49701) ≤ (663432703 / 1000000000) := by
  have h := checkLog_sound (w := (24101 / 75301)) (n := 12)
    (lo := (331716351 / 500000000)) (hi := (663432703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49701 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49701 / 25600) = 1/(25600 / 49701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331716351 / 500000000) (663432703 / 1000000000) (Real.log (49701 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49701 / 25600) = -Real.log (25600 / 49701) := by
    rw [show ((49701 / 25600) : ℝ) = ((25600 / 49701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (283779413 / 100000000) ≤ -Real.log (1499 / 25600) ∧
    -Real.log (1499 / 25600) ≤ (567558827 / 200000000) := by
  have h := checkLog_sound (w := (101 / 3099)) (n := 12)
    (lo := (6520541 / 100000000)) (hi := (65205411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1499) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1499) = 1/(1499 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-567558827 / 200000000) (-283779413 / 100000000) (Real.log (1499 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340409753 / 500000000) ≤ -Real.log (125000 / 246937) ∧
    -Real.log (125000 / 246937) ≤ (680819507 / 1000000000) := by
  have h := checkLog_sound (w := (121937 / 371937)) (n := 12)
    (lo := (340409753 / 500000000)) (hi := (680819507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246937 / 125000) = 1/(125000 / 246937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340409753 / 500000000) (680819507 / 1000000000) (Real.log (246937 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (246937 / 125000) = -Real.log (125000 / 246937) := by
    rw [show ((246937 / 125000) : ℝ) = ((125000 / 246937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1854459453 / 500000000) ≤ -Real.log (3063 / 125000) ∧
    -Real.log (3063 / 125000) ≤ (28975929 / 7812500) := by
  have h := checkLog_sound (w := (3373 / 27877)) (n := 12)
    (lo := (121591503 / 500000000)) (hi := (243183007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12252) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12252) = 1/(3063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28975929 / 7812500) (-1854459453 / 500000000) (Real.log (3063 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680894927 / 1000000000) ≤ -Real.log (200000 / 395129) ∧
    -Real.log (200000 / 395129) ≤ (42555933 / 62500000) := by
  have h := checkLog_sound (w := (195129 / 595129)) (n := 12)
    (lo := (680894927 / 1000000000)) (hi := (42555933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395129 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395129 / 200000) = 1/(200000 / 395129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680894927 / 1000000000) (42555933 / 62500000) (Real.log (395129 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (395129 / 200000) = -Real.log (200000 / 395129) := by
    rw [show ((395129 / 200000) : ℝ) = ((200000 / 395129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (928754527 / 250000000) ≤ -Real.log (4871 / 200000) ∧
    -Real.log (4871 / 200000) ≤ (1857509057 / 500000000) := by
  have h := checkLog_sound (w := (1379 / 11121)) (n := 12)
    (lo := (7790069 / 31250000)) (hi := (249282209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4871) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4871) = 1/(4871 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1857509057 / 500000000) (-928754527 / 250000000) (Real.log (4871 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68074661 / 100000000) ≤ -Real.log (125000 / 246919) ∧
    -Real.log (125000 / 246919) ≤ (680746611 / 1000000000) := by
  have h := checkLog_sound (w := (121919 / 371919)) (n := 12)
    (lo := (68074661 / 100000000)) (hi := (680746611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246919 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246919 / 125000) = 1/(125000 / 246919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68074661 / 100000000) (680746611 / 1000000000) (Real.log (246919 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246919 / 125000) = -Real.log (125000 / 246919) := by
    rw [show ((246919 / 125000) : ℝ) = ((125000 / 246919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1851529757 / 500000000) ≤ -Real.log (3081 / 125000) ∧
    -Real.log (3081 / 125000) ≤ (11572061 / 3125000) := by
  have h := checkLog_sound (w := (3301 / 27949)) (n := 12)
    (lo := (118661807 / 500000000)) (hi := (47464723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12324) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12324) = 1/(3081 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11572061 / 3125000) (-1851529757 / 500000000) (Real.log (3081 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680823049 / 1000000000) ≤ -Real.log (1000000 / 1975503) ∧
    -Real.log (1000000 / 1975503) ≤ (13616461 / 20000000) := by
  have h := checkLog_sound (w := (975503 / 2975503)) (n := 12)
    (lo := (680823049 / 1000000000)) (hi := (13616461 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975503 / 1000000) = 1/(1000000 / 1975503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680823049 / 1000000000) (13616461 / 20000000) (Real.log (1975503 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975503 / 1000000) = -Real.log (1000000 / 1975503) := by
    rw [show ((1975503 / 1000000) : ℝ) = ((1000000 / 1975503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (741840923 / 200000000) ≤ -Real.log (24497 / 1000000) ∧
    -Real.log (24497 / 1000000) ≤ (3709204621 / 1000000000) := by
  have h := checkLog_sound (w := (6753 / 55747)) (n := 12)
    (lo := (48693743 / 200000000)) (hi := (60867179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24497) = 1/(24497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3709204621 / 1000000000) (-741840923 / 200000000) (Real.log (24497 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1097434603 / 250000000) ≤ -Real.log (50000000000 / 4030966372837) ∧
    -Real.log (50000000000 / 4030966372837) ≤ (4389738419 / 1000000000) := by
  have h := checkLog_sound (w := (830966372837 / 7230966372837)) (n := 12)
    (lo := (57713833 / 250000000)) (hi := (230855333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4030966372837 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4030966372837 / 3200000000000) = 1/(50000000000 / 4030966372837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1097434603 / 250000000) (4389738419 / 1000000000) (Real.log (4030966372837 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4030966372837 / 50000000000) = -Real.log (50000000000 / 4030966372837) := by
    rw [show ((4030966372837 / 50000000000) : ℝ) = ((50000000000 / 4030966372837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (879182607 / 200000000) ≤ -Real.log (50000000000 / 4055933073291) ∧
    -Real.log (50000000000 / 4055933073291) ≤ (2197956521 / 500000000) := by
  have h := checkLog_sound (w := (855933073291 / 7255933073291)) (n := 12)
    (lo := (47405991 / 200000000)) (hi := (59257489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4055933073291 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4055933073291 / 3200000000000) = 1/(50000000000 / 4055933073291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (879182607 / 200000000) (2197956521 / 500000000) (Real.log (4055933073291 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4055933073291 / 50000000000) = -Real.log (50000000000 / 4055933073291) := by
    rw [show ((4055933073291 / 50000000000) : ℝ) = ((50000000000 / 4055933073291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1095951531 / 250000000) ≤ -Real.log (62500000000 / 5008905387861) ∧
    -Real.log (62500000000 / 5008905387861) ≤ (4383806131 / 1000000000) := by
  have h := checkLog_sound (w := (1008905387861 / 9008905387861)) (n := 12)
    (lo := (56230761 / 250000000)) (hi := (44984609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5008905387861 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5008905387861 / 4000000000000) = 1/(62500000000 / 5008905387861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1095951531 / 250000000) (4383806131 / 1000000000) (Real.log (5008905387861 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5008905387861 / 62500000000) = -Real.log (62500000000 / 5008905387861) := by
    rw [show ((5008905387861 / 62500000000) : ℝ) = ((62500000000 / 5008905387861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274376729 / 62500000) ≤ -Real.log (125000000000 / 10080331265053) ∧
    -Real.log (125000000000 / 10080331265053) ≤ (4390027671 / 1000000000) := by
  have h := checkLog_sound (w := (2080331265053 / 18080331265053)) (n := 12)
    (lo := (28893073 / 125000000)) (hi := (46228917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10080331265053 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10080331265053 / 8000000000000) = 1/(125000000000 / 10080331265053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274376729 / 62500000) (4390027671 / 1000000000) (Real.log (10080331265053 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10080331265053 / 125000000000) = -Real.log (125000000000 / 10080331265053) := by
    rw [show ((10080331265053 / 125000000000) : ℝ) = ((125000000000 / 10080331265053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056
