import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0075
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

theorem reflection_log_1_neg : (169034527 / 250000000) ≤ -Real.log (51200 / 100673) ∧
    -Real.log (51200 / 100673) ≤ (676138109 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 151873)) (n := 12)
    (lo := (169034527 / 250000000)) (hi := (676138109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100673 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100673 / 51200) = 1/(51200 / 100673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169034527 / 250000000) (676138109 / 1000000000) (Real.log (100673 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100673 / 51200) = -Real.log (51200 / 100673) := by
    rw [show ((100673 / 51200) : ℝ) = ((51200 / 100673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338935373 / 100000000) ≤ -Real.log (1727 / 51200) ∧
    -Real.log (1727 / 51200) ≤ (677870747 / 200000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1727) = 1/(1727 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-677870747 / 200000000) (-338935373 / 100000000) (Real.log (1727 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8449367 / 12500000) ≤ -Real.log (25600 / 50327) ∧
    -Real.log (25600 / 50327) ≤ (675949361 / 1000000000) := by
  have h := checkLog_sound (w := (24727 / 75927)) (n := 12)
    (lo := (8449367 / 12500000)) (hi := (675949361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50327 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50327 / 25600) = 1/(25600 / 50327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8449367 / 12500000) (675949361 / 1000000000) (Real.log (50327 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50327 / 25600) = -Real.log (25600 / 50327) := by
    rw [show ((50327 / 25600) : ℝ) = ((25600 / 50327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (422301509 / 125000000) ≤ -Real.log (873 / 25600) ∧
    -Real.log (873 / 25600) ≤ (3378412077 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 873) = 1/(873 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3378412077 / 1000000000) (-422301509 / 125000000) (Real.log (873 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (329417357 / 500000000) ≤ -Real.log (25600 / 49473) ∧
    -Real.log (25600 / 49473) ≤ (131766943 / 200000000) := by
  have h := checkLog_sound (w := (23873 / 75073)) (n := 12)
    (lo := (329417357 / 500000000)) (hi := (131766943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49473 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49473 / 25600) = 1/(25600 / 49473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (329417357 / 500000000) (131766943 / 200000000) (Real.log (49473 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49473 / 25600) = -Real.log (25600 / 49473) := by
    rw [show ((49473 / 25600) : ℝ) = ((25600 / 49473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53924131 / 20000000) ≤ -Real.log (1727 / 25600) ∧
    -Real.log (1727 / 25600) ≤ (1348103277 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4927)) (n := 12)
    (lo := (61676501 / 100000000)) (hi := (616765011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1727) = 1/(1727 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1348103277 / 500000000) (-53924131 / 20000000) (Real.log (1727 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (658450593 / 1000000000) ≤ -Real.log (12800 / 24727) ∧
    -Real.log (12800 / 24727) ≤ (329225297 / 500000000) := by
  have h := checkLog_sound (w := (11927 / 37527)) (n := 12)
    (lo := (658450593 / 1000000000)) (hi := (329225297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24727 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24727 / 12800) = 1/(12800 / 24727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (658450593 / 1000000000) (329225297 / 500000000) (Real.log (24727 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24727 / 12800) = -Real.log (12800 / 24727) := by
    rw [show ((24727 / 12800) : ℝ) = ((12800 / 24727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (671316223 / 250000000) ≤ -Real.log (873 / 12800) ∧
    -Real.log (873 / 12800) ≤ (5244658 / 1953125) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 873) = 1/(873 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5244658 / 1953125) (-671316223 / 250000000) (Real.log (873 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339440703 / 500000000) ≤ -Real.log (1000000 / 1971671) ∧
    -Real.log (1000000 / 1971671) ≤ (678881407 / 1000000000) := by
  have h := checkLog_sound (w := (971671 / 2971671)) (n := 12)
    (lo := (339440703 / 500000000)) (hi := (678881407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971671 / 1000000) = 1/(1000000 / 1971671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339440703 / 500000000) (678881407 / 1000000000) (Real.log (1971671 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971671 / 1000000) = -Real.log (1000000 / 1971671) := by
    rw [show ((1971671 / 1000000) : ℝ) = ((1000000 / 1971671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3563869261 / 1000000000) ≤ -Real.log (28329 / 1000000) ∧
    -Real.log (28329 / 1000000) ≤ (3563869267 / 1000000000) := by
  have h := checkLog_sound (w := (2921 / 59579)) (n := 12)
    (lo := (98133361 / 1000000000)) (hi := (49066681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28329) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28329) = 1/(28329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3563869267 / 1000000000) (-3563869261 / 1000000000) (Real.log (28329 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (679030507 / 1000000000) ≤ -Real.log (200000 / 394393) ∧
    -Real.log (200000 / 394393) ≤ (169757627 / 250000000) := by
  have h := checkLog_sound (w := (194393 / 594393)) (n := 12)
    (lo := (679030507 / 1000000000)) (hi := (169757627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394393 / 200000) = 1/(200000 / 394393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (679030507 / 1000000000) (169757627 / 250000000) (Real.log (394393 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394393 / 200000) = -Real.log (200000 / 394393) := by
    rw [show ((394393 / 200000) : ℝ) = ((200000 / 394393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1787150773 / 500000000) ≤ -Real.log (5607 / 200000) ∧
    -Real.log (5607 / 200000) ≤ (223393847 / 62500000) := by
  have h := checkLog_sound (w := (643 / 11857)) (n := 12)
    (lo := (54282823 / 500000000)) (hi := (108565647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5607) = 1/(5607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223393847 / 62500000) (-1787150773 / 500000000) (Real.log (5607 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13575579 / 20000000) ≤ -Real.log (1000000 / 1971469) ∧
    -Real.log (1000000 / 1971469) ≤ (678778951 / 1000000000) := by
  have h := checkLog_sound (w := (971469 / 2971469)) (n := 12)
    (lo := (13575579 / 20000000)) (hi := (678778951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971469 / 1000000) = 1/(1000000 / 1971469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13575579 / 20000000) (678778951 / 1000000000) (Real.log (1971469 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1971469 / 1000000) = -Real.log (1000000 / 1971469) := by
    rw [show ((1971469 / 1000000) : ℝ) = ((1000000 / 1971469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (177838203 / 50000000) ≤ -Real.log (28531 / 1000000) ∧
    -Real.log (28531 / 1000000) ≤ (1778382033 / 500000000) := by
  have h := checkLog_sound (w := (2719 / 59781)) (n := 12)
    (lo := (284463 / 3125000)) (hi := (91028161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28531) = 1/(28531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1778382033 / 500000000) (-177838203 / 50000000) (Real.log (28531 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135786019 / 200000000) ≤ -Real.log (1000000 / 1971767) ∧
    -Real.log (1000000 / 1971767) ≤ (42433131 / 62500000) := by
  have h := checkLog_sound (w := (971767 / 2971767)) (n := 12)
    (lo := (135786019 / 200000000)) (hi := (42433131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971767 / 1000000) = 1/(1000000 / 1971767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135786019 / 200000000) (42433131 / 62500000) (Real.log (1971767 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1971767 / 1000000) = -Real.log (1000000 / 1971767) := by
    rw [show ((1971767 / 1000000) : ℝ) = ((1000000 / 1971767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3567263769 / 1000000000) ≤ -Real.log (28233 / 1000000) ∧
    -Real.log (28233 / 1000000) ≤ (142690551 / 40000000) := by
  have h := checkLog_sound (w := (3017 / 59483)) (n := 12)
    (lo := (101527869 / 1000000000)) (hi := (10152787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28233) = 1/(28233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142690551 / 40000000) (-3567263769 / 1000000000) (Real.log (28233 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4242750667 / 1000000000) ≤ -Real.log (4000000000 / 278396131173) ∧
    -Real.log (4000000000 / 278396131173) ≤ (2121375337 / 500000000) := by
  have h := checkLog_sound (w := (22396131173 / 534396131173)) (n := 12)
    (lo := (83867587 / 1000000000)) (hi := (20966897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278396131173 / 256000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(278396131173 / 256000000000) = 1/(4000000000 / 278396131173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4242750667 / 1000000000) (2121375337 / 500000000) (Real.log (278396131173 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (278396131173 / 4000000000) = -Real.log (4000000000 / 278396131173) := by
    rw [show ((278396131173 / 4000000000) : ℝ) = ((4000000000 / 278396131173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4253332053 / 1000000000) ≤ -Real.log (500000000000 / 35169698591047) ∧
    -Real.log (500000000000 / 35169698591047) ≤ (212666603 / 50000000) := by
  have h := checkLog_sound (w := (3169698591047 / 67169698591047)) (n := 12)
    (lo := (94448973 / 1000000000)) (hi := (47224487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35169698591047 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35169698591047 / 32000000000000) = 1/(500000000000 / 35169698591047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4253332053 / 1000000000) (212666603 / 50000000) (Real.log (35169698591047 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35169698591047 / 500000000000) = -Real.log (500000000000 / 35169698591047) := by
    rw [show ((35169698591047 / 500000000000) : ℝ) = ((500000000000 / 35169698591047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (423554301 / 100000000) ≤ -Real.log (20000000000 / 1381983807087) ∧
    -Real.log (20000000000 / 1381983807087) ≤ (4235543017 / 1000000000) := by
  have h := checkLog_sound (w := (101983807087 / 2661983807087)) (n := 12)
    (lo := (7665993 / 100000000)) (hi := (76659931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381983807087 / 1280000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1381983807087 / 1280000000000) = 1/(20000000000 / 1381983807087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (423554301 / 100000000) (4235543017 / 1000000000) (Real.log (1381983807087 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1381983807087 / 20000000000) = -Real.log (20000000000 / 1381983807087) := by
    rw [show ((1381983807087 / 20000000000) : ℝ) = ((20000000000 / 1381983807087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (530774233 / 125000000) ≤ -Real.log (250000000000 / 17459772252329) ∧
    -Real.log (250000000000 / 17459772252329) ≤ (4246193871 / 1000000000) := by
  have h := checkLog_sound (w := (1459772252329 / 33459772252329)) (n := 12)
    (lo := (1364231 / 15625000)) (hi := (17462157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17459772252329 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17459772252329 / 16000000000000) = 1/(250000000000 / 17459772252329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (530774233 / 125000000) (4246193871 / 1000000000) (Real.log (17459772252329 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17459772252329 / 250000000000) = -Real.log (250000000000 / 17459772252329) := by
    rw [show ((17459772252329 / 250000000000) : ℝ) = ((250000000000 / 17459772252329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0075
