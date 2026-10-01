import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0048
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

theorem reflection_log_1_neg : (188066421 / 500000000) ≤ -Real.log (2560 / 3729) ∧
    -Real.log (2560 / 3729) ≤ (376132843 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 6289)) (n := 12)
    (lo := (188066421 / 500000000)) (hi := (376132843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3729 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3729 / 2560) = 1/(2560 / 3729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (188066421 / 500000000) (376132843 / 1000000000) (Real.log (3729 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3729 / 2560) = -Real.log (2560 / 3729) := by
    rw [show ((3729 / 2560) : ℝ) = ((2560 / 3729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121996869 / 200000000) ≤ -Real.log (1391 / 2560) ∧
    -Real.log (1391 / 2560) ≤ (304992173 / 500000000) := by
  have h := checkLog_sound (w := (1169 / 3951)) (n := 12)
    (lo := (121996869 / 200000000)) (hi := (304992173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1391) = 1/(1391 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-304992173 / 500000000) (-121996869 / 200000000) (Real.log (1391 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (375328013 / 1000000000) ≤ -Real.log (1280 / 1863) ∧
    -Real.log (1280 / 1863) ≤ (187664007 / 500000000) := by
  have h := checkLog_sound (w := (583 / 3143)) (n := 12)
    (lo := (375328013 / 1000000000)) (hi := (187664007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1280) = 1/(1280 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (375328013 / 1000000000) (187664007 / 500000000) (Real.log (1863 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1863 / 1280) = -Real.log (1280 / 1863) := by
    rw [show ((1863 / 1280) : ℝ) = ((1280 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303914973 / 500000000) ≤ -Real.log (697 / 1280) ∧
    -Real.log (697 / 1280) ≤ (607829947 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 1977)) (n := 12)
    (lo := (303914973 / 500000000)) (hi := (607829947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 697) = 1/(697 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-607829947 / 1000000000) (-303914973 / 500000000) (Real.log (697 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6488197 / 10000000) ≤ -Real.log (1280 / 2449) ∧
    -Real.log (1280 / 2449) ≤ (648819701 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 3729)) (n := 12)
    (lo := (6488197 / 10000000)) (hi := (648819701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 1280) = 1/(1280 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6488197 / 10000000) (648819701 / 1000000000) (Real.log (2449 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2449 / 1280) = -Real.log (1280 / 2449) := by
    rw [show ((2449 / 1280) : ℝ) = ((1280 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2445085153 / 1000000000) ≤ -Real.log (111 / 1280) ∧
    -Real.log (111 / 1280) ≤ (2445085157 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 111) = 1/(111 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2445085157 / 1000000000) (-2445085153 / 1000000000) (Real.log (111 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (647593959 / 1000000000) ≤ -Real.log (640 / 1223) ∧
    -Real.log (640 / 1223) ≤ (16189849 / 25000000) := by
  have h := checkLog_sound (w := (583 / 1863)) (n := 12)
    (lo := (647593959 / 1000000000)) (hi := (16189849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 640) = 1/(640 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (647593959 / 1000000000) (16189849 / 25000000) (Real.log (1223 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1223 / 640) = -Real.log (640 / 1223) := by
    rw [show ((1223 / 640) : ℝ) = ((640 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1209208453 / 500000000) ≤ -Real.log (57 / 640) ∧
    -Real.log (57 / 640) ≤ (241841691 / 100000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 57) = 1/(57 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241841691 / 100000000) (-1209208453 / 500000000) (Real.log (57 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (520262357 / 1000000000) ≤ -Real.log (1000000 / 1682469) ∧
    -Real.log (1000000 / 1682469) ≤ (260131179 / 500000000) := by
  have h := checkLog_sound (w := (682469 / 2682469)) (n := 12)
    (lo := (520262357 / 1000000000)) (hi := (260131179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1682469 / 1000000) = 1/(1000000 / 1682469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (520262357 / 1000000000) (260131179 / 500000000) (Real.log (1682469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1682469 / 1000000) = -Real.log (1000000 / 1682469) := by
    rw [show ((1682469 / 1000000) : ℝ) = ((1000000 / 1682469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1147179827 / 1000000000) ≤ -Real.log (317531 / 1000000) ∧
    -Real.log (317531 / 1000000) ≤ (1147179829 / 1000000000) := by
  have h := checkLog_sound (w := (182469 / 817531)) (n := 12)
    (lo := (454032647 / 1000000000)) (hi := (56754081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 317531) = 1/(317531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1147179829 / 1000000000) (-1147179827 / 1000000000) (Real.log (317531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (521545361 / 1000000000) ≤ -Real.log (1000000 / 1684629) ∧
    -Real.log (1000000 / 1684629) ≤ (260772681 / 500000000) := by
  have h := checkLog_sound (w := (684629 / 2684629)) (n := 12)
    (lo := (521545361 / 1000000000)) (hi := (260772681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1684629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1684629 / 1000000) = 1/(1000000 / 1684629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (521545361 / 1000000000) (260772681 / 500000000) (Real.log (1684629 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1684629 / 1000000) = -Real.log (1000000 / 1684629) := by
    rw [show ((1684629 / 1000000) : ℝ) = ((1000000 / 1684629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (577002777 / 500000000) ≤ -Real.log (315371 / 1000000) ∧
    -Real.log (315371 / 1000000) ≤ (288501389 / 250000000) := by
  have h := checkLog_sound (w := (184629 / 815371)) (n := 12)
    (lo := (230429187 / 500000000)) (hi := (3686867 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 315371) = 1/(315371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-288501389 / 250000000) (-577002777 / 500000000) (Real.log (315371 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (88035777 / 200000000) ≤ -Real.log (200000 / 310597) ∧
    -Real.log (200000 / 310597) ≤ (220089443 / 500000000) := by
  have h := checkLog_sound (w := (110597 / 510597)) (n := 12)
    (lo := (88035777 / 200000000)) (hi := (220089443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310597 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310597 / 200000) = 1/(200000 / 310597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (88035777 / 200000000) (220089443 / 500000000) (Real.log (310597 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (310597 / 200000) = -Real.log (200000 / 310597) := by
    rw [show ((310597 / 200000) : ℝ) = ((200000 / 310597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (805163127 / 1000000000) ≤ -Real.log (89403 / 200000) ∧
    -Real.log (89403 / 200000) ≤ (805163129 / 1000000000) := by
  have h := checkLog_sound (w := (10597 / 189403)) (n := 12)
    (lo := (112015947 / 1000000000)) (hi := (28003987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89403) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89403) = 1/(89403 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-805163129 / 1000000000) (-805163127 / 1000000000) (Real.log (89403 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13800813 / 31250000) ≤ -Real.log (500000 / 777617) ∧
    -Real.log (500000 / 777617) ≤ (441626017 / 1000000000) := by
  have h := checkLog_sound (w := (277617 / 1277617)) (n := 12)
    (lo := (13800813 / 31250000)) (hi := (441626017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777617 / 500000) = 1/(500000 / 777617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13800813 / 31250000) (441626017 / 1000000000) (Real.log (777617 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (777617 / 500000) = -Real.log (500000 / 777617) := by
    rw [show ((777617 / 500000) : ℝ) = ((500000 / 777617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (810206977 / 1000000000) ≤ -Real.log (222383 / 500000) ∧
    -Real.log (222383 / 500000) ≤ (810206979 / 1000000000) := by
  have h := checkLog_sound (w := (27617 / 472383)) (n := 12)
    (lo := (117059797 / 1000000000)) (hi := (58529899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222383) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 222383) = 1/(222383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-810206979 / 1000000000) (-810206977 / 1000000000) (Real.log (222383 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1667442183 / 1000000000) ≤ -Real.log (25000000000 / 132464940431) ∧
    -Real.log (25000000000 / 132464940431) ≤ (833721093 / 500000000) := by
  have h := checkLog_sound (w := (32464940431 / 232464940431)) (n := 12)
    (lo := (281147823 / 1000000000)) (hi := (17571739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132464940431 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(132464940431 / 100000000000) = 1/(25000000000 / 132464940431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1667442183 / 1000000000) (833721093 / 500000000) (Real.log (132464940431 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132464940431 / 25000000000) = -Real.log (25000000000 / 132464940431) := by
    rw [show ((132464940431 / 25000000000) : ℝ) = ((25000000000 / 132464940431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (335110183 / 200000000) ≤ -Real.log (100000000000 / 534173719207) ∧
    -Real.log (100000000000 / 534173719207) ≤ (837775459 / 500000000) := by
  have h := checkLog_sound (w := (134173719207 / 934173719207)) (n := 12)
    (lo := (57851311 / 200000000)) (hi := (72314139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((534173719207 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(534173719207 / 400000000000) = 1/(100000000000 / 534173719207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (335110183 / 200000000) (837775459 / 500000000) (Real.log (534173719207 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (534173719207 / 100000000000) = -Real.log (100000000000 / 534173719207) := by
    rw [show ((534173719207 / 100000000000) : ℝ) = ((100000000000 / 534173719207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (311335503 / 250000000) ≤ -Real.log (10000000000 / 34741227923) ∧
    -Real.log (10000000000 / 34741227923) ≤ (622671007 / 500000000) := by
  have h := checkLog_sound (w := (14741227923 / 54741227923)) (n := 12)
    (lo := (34512177 / 62500000)) (hi := (552194833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34741227923 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34741227923 / 20000000000) = 1/(10000000000 / 34741227923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (311335503 / 250000000) (622671007 / 500000000) (Real.log (34741227923 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34741227923 / 10000000000) = -Real.log (10000000000 / 34741227923) := by
    rw [show ((34741227923 / 10000000000) : ℝ) = ((10000000000 / 34741227923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1251832993 / 1000000000) ≤ -Real.log (500000000000 / 1748373301917) ∧
    -Real.log (500000000000 / 1748373301917) ≤ (250366599 / 200000000) := by
  have h := checkLog_sound (w := (748373301917 / 2748373301917)) (n := 12)
    (lo := (558685813 / 1000000000)) (hi := (279342907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1748373301917 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1748373301917 / 1000000000000) = 1/(500000000000 / 1748373301917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1251832993 / 1000000000) (250366599 / 200000000) (Real.log (1748373301917 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1748373301917 / 500000000000) = -Real.log (500000000000 / 1748373301917) := by
    rw [show ((1748373301917 / 500000000000) : ℝ) = ((500000000000 / 1748373301917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0048
