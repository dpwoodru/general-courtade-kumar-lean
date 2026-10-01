import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057
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

theorem reflection_log_1_neg : (339200153 / 500000000) ≤ -Real.log (51200 / 100901) ∧
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


theorem reflection_log_1 : Bounds (339200153 / 500000000) (678400307 / 1000000000) (Real.log (100901 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100901 / 51200) = -Real.log (51200 / 100901) := by
    rw [show ((100901 / 51200) : ℝ) = ((51200 / 100901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (353094131 / 100000000) ≤ -Real.log (1499 / 51200) ∧
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


theorem reflection_log_2 : Bounds (-882735329 / 250000000) (-353094131 / 100000000) (Real.log (1499 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678306149 / 1000000000) ≤ -Real.log (102400 / 201783) ∧
    -Real.log (102400 / 201783) ≤ (13566123 / 20000000) := by
  have h := checkLog_sound (w := (99383 / 304183)) (n := 12)
    (lo := (678306149 / 1000000000)) (hi := (13566123 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201783 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201783 / 102400) = 1/(102400 / 201783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678306149 / 1000000000) (13566123 / 20000000) (Real.log (201783 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201783 / 102400) = -Real.log (102400 / 201783) := by
    rw [show ((201783 / 102400) : ℝ) = ((102400 / 201783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3524623749 / 1000000000) ≤ -Real.log (3017 / 102400) ∧
    -Real.log (3017 / 102400) ≤ (704924751 / 200000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3017) = 1/(3017 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-704924751 / 200000000) (-3524623749 / 1000000000) (Real.log (3017 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331716351 / 500000000) ≤ -Real.log (25600 / 49701) ∧
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


theorem reflection_log_5 : Bounds (331716351 / 500000000) (663432703 / 1000000000) (Real.log (49701 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49701 / 25600) = -Real.log (25600 / 49701) := by
    rw [show ((49701 / 25600) : ℝ) = ((25600 / 49701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283779413 / 100000000) ≤ -Real.log (1499 / 25600) ∧
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


theorem reflection_log_6 : Bounds (-567558827 / 200000000) (-283779413 / 100000000) (Real.log (1499 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33162077 / 50000000) ≤ -Real.log (51200 / 99383) ∧
    -Real.log (51200 / 99383) ≤ (663241541 / 1000000000) := by
  have h := checkLog_sound (w := (48183 / 150583)) (n := 12)
    (lo := (33162077 / 50000000)) (hi := (663241541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99383 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99383 / 51200) = 1/(51200 / 99383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33162077 / 50000000) (663241541 / 1000000000) (Real.log (99383 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99383 / 51200) = -Real.log (51200 / 99383) := by
    rw [show ((99383 / 51200) : ℝ) = ((51200 / 99383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2831476569 / 1000000000) ≤ -Real.log (3017 / 51200) ∧
    -Real.log (3017 / 51200) ≤ (1415738287 / 500000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3017) = 1/(3017 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1415738287 / 500000000) (-2831476569 / 1000000000) (Real.log (3017 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136148917 / 200000000) ≤ -Real.log (250000 / 493837) ∧
    -Real.log (250000 / 493837) ≤ (340372293 / 500000000) := by
  have h := checkLog_sound (w := (243837 / 743837)) (n := 12)
    (lo := (136148917 / 200000000)) (hi := (340372293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493837 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493837 / 250000) = 1/(250000 / 493837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136148917 / 200000000) (340372293 / 500000000) (Real.log (493837 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493837 / 250000) = -Real.log (250000 / 493837) := by
    rw [show ((493837 / 250000) : ℝ) = ((250000 / 493837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3702897243 / 1000000000) ≤ -Real.log (6163 / 250000) ∧
    -Real.log (6163 / 250000) ≤ (3702897249 / 1000000000) := by
  have h := checkLog_sound (w := (3299 / 27951)) (n := 12)
    (lo := (237161343 / 1000000000)) (hi := (1852823 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12326) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12326) = 1/(6163 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3702897249 / 1000000000) (-3702897243 / 1000000000) (Real.log (6163 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170205003 / 250000000) ≤ -Real.log (1000000 / 1975497) ∧
    -Real.log (1000000 / 1975497) ≤ (680820013 / 1000000000) := by
  have h := checkLog_sound (w := (975497 / 2975497)) (n := 12)
    (lo := (170205003 / 250000000)) (hi := (680820013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975497 / 1000000) = 1/(1000000 / 1975497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170205003 / 250000000) (680820013 / 1000000000) (Real.log (1975497 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975497 / 1000000) = -Real.log (1000000 / 1975497) := by
    rw [show ((1975497 / 1000000) : ℝ) = ((1000000 / 1975497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3708959717 / 1000000000) ≤ -Real.log (24503 / 1000000) ∧
    -Real.log (24503 / 1000000) ≤ (3708959723 / 1000000000) := by
  have h := checkLog_sound (w := (6747 / 55753)) (n := 12)
    (lo := (243223817 / 1000000000)) (hi := (121611909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24503) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24503) = 1/(24503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3708959723 / 1000000000) (-3708959717 / 1000000000) (Real.log (24503 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680670671 / 1000000000) ≤ -Real.log (500000 / 987601) ∧
    -Real.log (500000 / 987601) ≤ (42541917 / 62500000) := by
  have h := checkLog_sound (w := (487601 / 1487601)) (n := 12)
    (lo := (680670671 / 1000000000)) (hi := (42541917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987601 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987601 / 500000) = 1/(500000 / 987601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680670671 / 1000000000) (42541917 / 62500000) (Real.log (987601 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987601 / 500000) = -Real.log (500000 / 987601) := by
    rw [show ((987601 / 500000) : ℝ) = ((500000 / 987601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3696992271 / 1000000000) ≤ -Real.log (12399 / 500000) ∧
    -Real.log (12399 / 500000) ≤ (3696992277 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 14012)) (n := 12)
    (lo := (231256371 / 1000000000)) (hi := (57814093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12399) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12399) = 1/(12399 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3696992277 / 1000000000) (-3696992271 / 1000000000) (Real.log (12399 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170186779 / 250000000) ≤ -Real.log (1000000 / 1975353) ∧
    -Real.log (1000000 / 1975353) ≤ (680747117 / 1000000000) := by
  have h := checkLog_sound (w := (975353 / 2975353)) (n := 12)
    (lo := (170186779 / 250000000)) (hi := (680747117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975353 / 1000000) = 1/(1000000 / 1975353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170186779 / 250000000) (680747117 / 1000000000) (Real.log (1975353 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975353 / 1000000) = -Real.log (1000000 / 1975353) := by
    rw [show ((1975353 / 1000000) : ℝ) = ((1000000 / 1975353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1851550043 / 500000000) ≤ -Real.log (24647 / 1000000) ∧
    -Real.log (24647 / 1000000) ≤ (925775023 / 250000000) := by
  have h := checkLog_sound (w := (6603 / 55897)) (n := 12)
    (lo := (118682093 / 500000000)) (hi := (237364187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24647) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24647) = 1/(24647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-925775023 / 250000000) (-1851550043 / 500000000) (Real.log (24647 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4383641827 / 1000000000) ≤ -Real.log (125000000000 / 10016165017037) ∧
    -Real.log (125000000000 / 10016165017037) ≤ (2191820917 / 500000000) := by
  have h := checkLog_sound (w := (2016165017037 / 18016165017037)) (n := 12)
    (lo := (224758747 / 1000000000)) (hi := (56189687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10016165017037 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10016165017037 / 8000000000000) = 1/(125000000000 / 10016165017037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4383641827 / 1000000000) (2191820917 / 500000000) (Real.log (10016165017037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10016165017037 / 125000000000) = -Real.log (125000000000 / 10016165017037) := by
    rw [show ((10016165017037 / 125000000000) : ℝ) = ((125000000000 / 10016165017037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (274361233 / 62500000) ≤ -Real.log (500000000000 / 40311329224993) ∧
    -Real.log (500000000000 / 40311329224993) ≤ (877955947 / 200000000) := by
  have h := checkLog_sound (w := (8311329224993 / 72311329224993)) (n := 12)
    (lo := (28862081 / 125000000)) (hi := (230896649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40311329224993 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40311329224993 / 32000000000000) = 1/(500000000000 / 40311329224993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (274361233 / 62500000) (877955947 / 200000000) (Real.log (40311329224993 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40311329224993 / 500000000000) = -Real.log (500000000000 / 40311329224993) := by
    rw [show ((40311329224993 / 500000000000) : ℝ) = ((500000000000 / 40311329224993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2188831471 / 500000000) ≤ -Real.log (100000000000 / 7965166545689) ∧
    -Real.log (100000000000 / 7965166545689) ≤ (4377662949 / 1000000000) := by
  have h := checkLog_sound (w := (1565166545689 / 14365166545689)) (n := 12)
    (lo := (109389931 / 500000000)) (hi := (218779863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7965166545689 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7965166545689 / 6400000000000) = 1/(100000000000 / 7965166545689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2188831471 / 500000000) (4377662949 / 1000000000) (Real.log (7965166545689 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7965166545689 / 100000000000) = -Real.log (100000000000 / 7965166545689) := by
    rw [show ((7965166545689 / 100000000000) : ℝ) = ((100000000000 / 7965166545689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2191923601 / 500000000) ≤ -Real.log (6250000000 / 500911114943) ∧
    -Real.log (6250000000 / 500911114943) ≤ (4383847209 / 1000000000) := by
  have h := checkLog_sound (w := (100911114943 / 900911114943)) (n := 12)
    (lo := (112482061 / 500000000)) (hi := (224964123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500911114943 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(500911114943 / 400000000000) = 1/(6250000000 / 500911114943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2191923601 / 500000000) (4383847209 / 1000000000) (Real.log (500911114943 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (500911114943 / 6250000000) = -Real.log (6250000000 / 500911114943) := by
    rw [show ((500911114943 / 6250000000) : ℝ) = ((6250000000 / 500911114943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057
