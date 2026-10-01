import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0146
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

theorem reflection_log_1_neg : (656122491 / 1000000000) ≤ -Real.log (25600 / 49339) ∧
    -Real.log (25600 / 49339) ≤ (164030623 / 250000000) := by
  have h := checkLog_sound (w := (23739 / 74939)) (n := 12)
    (lo := (656122491 / 1000000000)) (hi := (164030623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49339 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49339 / 25600) = 1/(25600 / 49339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (656122491 / 1000000000) (164030623 / 250000000) (Real.log (49339 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49339 / 25600) = -Real.log (25600 / 49339) := by
    rw [show ((49339 / 25600) : ℝ) = ((25600 / 49339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (655369593 / 250000000) ≤ -Real.log (1861 / 25600) ∧
    -Real.log (1861 / 25600) ≤ (327684797 / 125000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1861) = 1/(1861 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-327684797 / 125000000) (-655369593 / 250000000) (Real.log (1861 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (327868663 / 500000000) ≤ -Real.log (640 / 1233) ∧
    -Real.log (640 / 1233) ≤ (655737327 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 1873)) (n := 12)
    (lo := (327868663 / 500000000)) (hi := (655737327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 640) = 1/(640 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (327868663 / 500000000) (655737327 / 1000000000) (Real.log (1233 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1233 / 640) = -Real.log (640 / 1233) := by
    rw [show ((1233 / 640) : ℝ) = ((640 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (652830143 / 250000000) ≤ -Real.log (47 / 640) ∧
    -Real.log (47 / 640) ≤ (10200471 / 3906250) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 47) = 1/(47 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10200471 / 3906250) (-652830143 / 250000000) (Real.log (47 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (308837047 / 500000000) ≤ -Real.log (12800 / 23739) ∧
    -Real.log (12800 / 23739) ≤ (123534819 / 200000000) := by
  have h := checkLog_sound (w := (10939 / 36539)) (n := 12)
    (lo := (308837047 / 500000000)) (hi := (123534819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23739 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23739 / 12800) = 1/(12800 / 23739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (308837047 / 500000000) (123534819 / 200000000) (Real.log (23739 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23739 / 12800) = -Real.log (12800 / 23739) := by
    rw [show ((23739 / 12800) : ℝ) = ((12800 / 23739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (241041399 / 125000000) ≤ -Real.log (1861 / 12800) ∧
    -Real.log (1861 / 12800) ≤ (385666239 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1861) = 1/(1861 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-385666239 / 200000000) (-241041399 / 125000000) (Real.log (1861 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (616873403 / 1000000000) ≤ -Real.log (320 / 593) ∧
    -Real.log (320 / 593) ≤ (154218351 / 250000000) := by
  have h := checkLog_sound (w := (273 / 913)) (n := 12)
    (lo := (616873403 / 1000000000)) (hi := (154218351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 320) = 1/(320 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (616873403 / 1000000000) (154218351 / 250000000) (Real.log (593 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593 / 320) = -Real.log (320 / 593) := by
    rw [show ((593 / 320) : ℝ) = ((320 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119885837 / 62500000) ≤ -Real.log (47 / 320) ∧
    -Real.log (47 / 320) ≤ (383634679 / 200000000) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 47) = 1/(47 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-383634679 / 200000000) (-119885837 / 62500000) (Real.log (47 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (663726093 / 1000000000) ≤ -Real.log (200000 / 388403) ∧
    -Real.log (200000 / 388403) ≤ (331863047 / 500000000) := by
  have h := checkLog_sound (w := (188403 / 588403)) (n := 12)
    (lo := (663726093 / 1000000000)) (hi := (331863047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388403 / 200000) = 1/(200000 / 388403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (663726093 / 1000000000) (331863047 / 500000000) (Real.log (388403 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (388403 / 200000) = -Real.log (200000 / 388403) := by
    rw [show ((388403 / 200000) : ℝ) = ((200000 / 388403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (71189273 / 25000000) ≤ -Real.log (11597 / 200000) ∧
    -Real.log (11597 / 200000) ≤ (113902837 / 40000000) := by
  have h := checkLog_sound (w := (903 / 24097)) (n := 12)
    (lo := (374911 / 5000000)) (hi := (74982201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11597) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11597) = 1/(11597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-113902837 / 40000000) (-71189273 / 25000000) (Real.log (11597 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664003087 / 1000000000) ≤ -Real.log (1000000 / 1942553) ∧
    -Real.log (1000000 / 1942553) ≤ (41500193 / 62500000) := by
  have h := checkLog_sound (w := (942553 / 2942553)) (n := 12)
    (lo := (664003087 / 1000000000)) (hi := (41500193 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1942553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1942553 / 1000000) = 1/(1000000 / 1942553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664003087 / 1000000000) (41500193 / 62500000) (Real.log (1942553 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1942553 / 1000000) = -Real.log (1000000 / 1942553) := by
    rw [show ((1942553 / 1000000) : ℝ) = ((1000000 / 1942553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2856892493 / 1000000000) ≤ -Real.log (57447 / 1000000) ∧
    -Real.log (57447 / 1000000) ≤ (1428446249 / 500000000) := by
  have h := checkLog_sound (w := (5053 / 119947)) (n := 12)
    (lo := (84303773 / 1000000000)) (hi := (42151887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 57447) = 1/(57447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1428446249 / 500000000) (-2856892493 / 1000000000) (Real.log (57447 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331565329 / 500000000) ≤ -Real.log (1000000 / 1940859) ∧
    -Real.log (1000000 / 1940859) ≤ (663130659 / 1000000000) := by
  have h := checkLog_sound (w := (940859 / 2940859)) (n := 12)
    (lo := (331565329 / 500000000)) (hi := (663130659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1940859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1940859 / 1000000) = 1/(1000000 / 1940859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331565329 / 500000000) (663130659 / 1000000000) (Real.log (1940859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1940859 / 1000000) = -Real.log (1000000 / 1940859) := by
    rw [show ((1940859 / 1000000) : ℝ) = ((1000000 / 1940859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2827830853 / 1000000000) ≤ -Real.log (59141 / 1000000) ∧
    -Real.log (59141 / 1000000) ≤ (1413915429 / 500000000) := by
  have h := checkLog_sound (w := (3359 / 121641)) (n := 12)
    (lo := (55242133 / 1000000000)) (hi := (27621067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59141) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 59141) = 1/(59141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1413915429 / 500000000) (-2827830853 / 1000000000) (Real.log (59141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (663421209 / 1000000000) ≤ -Real.log (1000000 / 1941423) ∧
    -Real.log (1000000 / 1941423) ≤ (66342121 / 100000000) := by
  have h := checkLog_sound (w := (941423 / 2941423)) (n := 12)
    (lo := (663421209 / 1000000000)) (hi := (66342121 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1941423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1941423 / 1000000) = 1/(1000000 / 1941423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (663421209 / 1000000000) (66342121 / 100000000) (Real.log (1941423 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1941423 / 1000000) = -Real.log (1000000 / 1941423) := by
    rw [show ((1941423 / 1000000) : ℝ) = ((1000000 / 1941423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (709353287 / 250000000) ≤ -Real.log (58577 / 1000000) ∧
    -Real.log (58577 / 1000000) ≤ (2837413153 / 1000000000) := by
  have h := checkLog_sound (w := (3923 / 121077)) (n := 12)
    (lo := (16206107 / 250000000)) (hi := (64824429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58577) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 58577) = 1/(58577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2837413153 / 1000000000) (-709353287 / 250000000) (Real.log (58577 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3511297013 / 1000000000) ≤ -Real.log (250000000000 / 8372919720617) ∧
    -Real.log (250000000000 / 8372919720617) ≤ (3511297019 / 1000000000) := by
  have h := checkLog_sound (w := (372919720617 / 16372919720617)) (n := 12)
    (lo := (45561113 / 1000000000)) (hi := (22780557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8372919720617 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8372919720617 / 8000000000000) = 1/(250000000000 / 8372919720617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3511297013 / 1000000000) (3511297019 / 1000000000) (Real.log (8372919720617 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8372919720617 / 250000000000) = -Real.log (250000000000 / 8372919720617) := by
    rw [show ((8372919720617 / 250000000000) : ℝ) = ((250000000000 / 8372919720617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3520895579 / 1000000000) ≤ -Real.log (50000000000 / 1690734938291) ∧
    -Real.log (50000000000 / 1690734938291) ≤ (704179117 / 200000000) := by
  have h := checkLog_sound (w := (90734938291 / 3290734938291)) (n := 12)
    (lo := (55159679 / 1000000000)) (hi := (86187 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1690734938291 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1690734938291 / 1600000000000) = 1/(50000000000 / 1690734938291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3520895579 / 1000000000) (704179117 / 200000000) (Real.log (1690734938291 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1690734938291 / 50000000000) = -Real.log (50000000000 / 1690734938291) := by
    rw [show ((1690734938291 / 50000000000) : ℝ) = ((50000000000 / 1690734938291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3490961511 / 1000000000) ≤ -Real.log (500000000000 / 16408743511269) ∧
    -Real.log (500000000000 / 16408743511269) ≤ (3490961517 / 1000000000) := by
  have h := checkLog_sound (w := (408743511269 / 32408743511269)) (n := 12)
    (lo := (25225611 / 1000000000)) (hi := (6306403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16408743511269 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16408743511269 / 16000000000000) = 1/(500000000000 / 16408743511269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3490961511 / 1000000000) (3490961517 / 1000000000) (Real.log (16408743511269 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16408743511269 / 500000000000) = -Real.log (500000000000 / 16408743511269) := by
    rw [show ((16408743511269 / 500000000000) : ℝ) = ((500000000000 / 16408743511269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3500834357 / 1000000000) ≤ -Real.log (500000000000 / 16571546852861) ∧
    -Real.log (500000000000 / 16571546852861) ≤ (3500834363 / 1000000000) := by
  have h := checkLog_sound (w := (571546852861 / 32571546852861)) (n := 12)
    (lo := (35098457 / 1000000000)) (hi := (17549229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16571546852861 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16571546852861 / 16000000000000) = 1/(500000000000 / 16571546852861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3500834357 / 1000000000) (3500834363 / 1000000000) (Real.log (16571546852861 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16571546852861 / 500000000000) = -Real.log (500000000000 / 16571546852861) := by
    rw [show ((16571546852861 / 500000000000) : ℝ) = ((500000000000 / 16571546852861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0146
