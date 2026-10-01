import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14400_neg : (215451079 / 500000000) ≤ -Real.log (200000 / 307729) ∧
    -Real.log (200000 / 307729) ≤ (430902159 / 1000000000) := by
  have h := checkLog_sound (w := (107729 / 507729)) (n := 12)
    (lo := (215451079 / 500000000)) (hi := (430902159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307729 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307729 / 200000) = 1/(200000 / 307729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14400 : Bounds (215451079 / 500000000) (430902159 / 1000000000) (Real.log (307729 / 200000)) := by
  have h := reflection_log_14400_neg
  have he : Real.log (307729 / 200000) = -Real.log (200000 / 307729) := by
    rw [show ((307729 / 200000) : ℝ) = ((200000 / 307729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14401_neg : (386793733 / 500000000) ≤ -Real.log (92271 / 200000) ∧
    -Real.log (92271 / 200000) ≤ (193396867 / 250000000) := by
  have h := checkLog_sound (w := (7729 / 192271)) (n := 12)
    (lo := (40220143 / 500000000)) (hi := (80440287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92271) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 92271) = 1/(92271 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14401 : Bounds (-193396867 / 250000000) (-386793733 / 500000000) (Real.log (92271 / 200000)) := by
  have h := reflection_log_14401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14402_neg : (43313799 / 100000000) ≤ -Real.log (1000000 / 1542089) ∧
    -Real.log (1000000 / 1542089) ≤ (433137991 / 1000000000) := by
  have h := checkLog_sound (w := (542089 / 2542089)) (n := 12)
    (lo := (43313799 / 100000000)) (hi := (433137991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1542089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1542089 / 1000000) = 1/(1000000 / 1542089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14402 : Bounds (43313799 / 100000000) (433137991 / 1000000000) (Real.log (1542089 / 1000000)) := by
  have h := reflection_log_14402_neg
  have he : Real.log (1542089 / 1000000) = -Real.log (1000000 / 1542089) := by
    rw [show ((1542089 / 1000000) : ℝ) = ((1000000 / 1542089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14403_neg : (195270109 / 250000000) ≤ -Real.log (457911 / 1000000) ∧
    -Real.log (457911 / 1000000) ≤ (390540219 / 500000000) := by
  have h := checkLog_sound (w := (42089 / 957911)) (n := 12)
    (lo := (10991657 / 125000000)) (hi := (87933257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 457911) = 1/(457911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14403 : Bounds (-390540219 / 500000000) (-195270109 / 250000000) (Real.log (457911 / 1000000)) := by
  have h := reflection_log_14403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14404_neg : (173971223 / 500000000) ≤ -Real.log (706139516079 / 1000000000000) ∧
    -Real.log (706139516079 / 1000000000000) ≤ (347942447 / 1000000000) := by
  have h := checkLog_sound (w := (293860483921 / 1706139516079)) (n := 12)
    (lo := (173971223 / 500000000)) (hi := (347942447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 706139516079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 706139516079) = 1/(706139516079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14404 : Bounds (-347942447 / 1000000000) (-173971223 / 500000000) (Real.log (706139516079 / 1000000000000)) := by
  have h := reflection_log_14404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14405_neg : (85671327 / 250000000) ≤ -Real.log (28394462559 / 40000000000) ∧
    -Real.log (28394462559 / 40000000000) ≤ (342685309 / 1000000000) := by
  have h := checkLog_sound (w := (11605537441 / 68394462559)) (n := 12)
    (lo := (85671327 / 250000000)) (hi := (342685309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28394462559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28394462559) = 1/(28394462559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14405 : Bounds (-342685309 / 1000000000) (-85671327 / 250000000) (Real.log (28394462559 / 40000000000)) := by
  have h := reflection_log_14405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14406_neg : (9635917 / 8000000) ≤ -Real.log (500000000000 / 1667528259149) ∧
    -Real.log (500000000000 / 1667528259149) ≤ (1204489627 / 1000000000) := by
  have h := checkLog_sound (w := (667528259149 / 2667528259149)) (n := 12)
    (lo := (102268489 / 200000000)) (hi := (255671223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667528259149 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1667528259149 / 1000000000000) = 1/(500000000000 / 1667528259149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14406 : Bounds (9635917 / 8000000) (1204489627 / 1000000000) (Real.log (1667528259149 / 500000000000)) := by
  have h := reflection_log_14406_neg
  have he : Real.log (1667528259149 / 500000000000) = -Real.log (500000000000 / 1667528259149) := by
    rw [show ((1667528259149 / 500000000000) : ℝ) = ((500000000000 / 1667528259149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14407_neg : (1214218427 / 1000000000) ≤ -Real.log (500000000000 / 1683830482343) ∧
    -Real.log (500000000000 / 1683830482343) ≤ (1214218429 / 1000000000) := by
  have h := checkLog_sound (w := (683830482343 / 2683830482343)) (n := 12)
    (lo := (521071247 / 1000000000)) (hi := (32566953 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683830482343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1683830482343 / 1000000000000) = 1/(500000000000 / 1683830482343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14407 : Bounds (1214218427 / 1000000000) (1214218429 / 1000000000) (Real.log (1683830482343 / 500000000000)) := by
  have h := reflection_log_14407_neg
  have he : Real.log (1683830482343 / 500000000000) = -Real.log (500000000000 / 1683830482343) := by
    rw [show ((1683830482343 / 500000000000) : ℝ) = ((500000000000 / 1683830482343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14408_neg : (2903110781 / 1000000000) ≤ -Real.log (62500000000 / 1139423076923) ∧
    -Real.log (62500000000 / 1139423076923) ≤ (1451555393 / 500000000) := by
  have h := checkLog_sound (w := (139423076923 / 2139423076923)) (n := 12)
    (lo := (130522061 / 1000000000)) (hi := (65261031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139423076923 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1139423076923 / 1000000000000) = 1/(62500000000 / 1139423076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14408 : Bounds (2903110781 / 1000000000) (1451555393 / 500000000) (Real.log (1139423076923 / 62500000000)) := by
  have h := reflection_log_14408_neg
  have he : Real.log (1139423076923 / 62500000000) = -Real.log (62500000000 / 1139423076923) := by
    rw [show ((1139423076923 / 62500000000) : ℝ) = ((62500000000 / 1139423076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14409_neg : (2933962191 / 1000000000) ≤ -Real.log (50000000000 / 940099009901) ∧
    -Real.log (50000000000 / 940099009901) ≤ (733490549 / 250000000) := by
  have h := checkLog_sound (w := (140099009901 / 1740099009901)) (n := 12)
    (lo := (161373471 / 1000000000)) (hi := (5042921 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940099009901 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(940099009901 / 800000000000) = 1/(50000000000 / 940099009901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14409 : Bounds (2933962191 / 1000000000) (733490549 / 250000000) (Real.log (940099009901 / 50000000000)) := by
  have h := reflection_log_14409_neg
  have he : Real.log (940099009901 / 50000000000) = -Real.log (50000000000 / 940099009901) := by
    rw [show ((940099009901 / 50000000000) : ℝ) = ((50000000000 / 940099009901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14410_neg : (160726491 / 250000000) ≤ -Real.log (500 / 951) ∧
    -Real.log (500 / 951) ≤ (128581193 / 200000000) := by
  have h := checkLog_sound (w := (451 / 1451)) (n := 12)
    (lo := (160726491 / 250000000)) (hi := (128581193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 500) = 1/(500 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14410 : Bounds (160726491 / 250000000) (128581193 / 200000000) (Real.log (951 / 500)) := by
  have h := reflection_log_14410_neg
  have he : Real.log (951 / 500) = -Real.log (500 / 951) := by
    rw [show ((951 / 500) : ℝ) = ((500 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14411_neg : (1161393899 / 500000000) ≤ -Real.log (49 / 500) ∧
    -Real.log (49 / 500) ≤ (1161393901 / 500000000) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 98) = 1/(49 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14411 : Bounds (-1161393901 / 500000000) (-1161393899 / 500000000) (Real.log (49 / 500)) := by
  have h := reflection_log_14411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14412_neg : (901593 / 1000000000) ≤ -Real.log (500000 / 500451) ∧
    -Real.log (500000 / 500451) ≤ (450797 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1000451)) (n := 12)
    (lo := (901593 / 1000000000)) (hi := (450797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500451 / 500000) = 1/(500000 / 500451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14412 : Bounds (901593 / 1000000000) (450797 / 500000000) (Real.log (500451 / 500000)) := by
  have h := reflection_log_14412_neg
  have he : Real.log (500451 / 500000) = -Real.log (500000 / 500451) := by
    rw [show ((500451 / 500000) : ℝ) = ((500000 / 500451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14413_neg : (902407 / 1000000000) ≤ -Real.log (499549 / 500000) ∧
    -Real.log (499549 / 500000) ≤ (112801 / 125000000) := by
  have h := checkLog_sound (w := (451 / 999549)) (n := 12)
    (lo := (902407 / 1000000000)) (hi := (112801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499549) = 1/(499549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14413 : Bounds (-112801 / 125000000) (-902407 / 1000000000) (Real.log (499549 / 500000)) := by
  have h := reflection_log_14413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14414_neg : (17308033 / 40000000) ≤ -Real.log (200000 / 308283) ∧
    -Real.log (200000 / 308283) ≤ (216350413 / 500000000) := by
  have h := checkLog_sound (w := (108283 / 508283)) (n := 12)
    (lo := (17308033 / 40000000)) (hi := (216350413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308283 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308283 / 200000) = 1/(200000 / 308283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14414 : Bounds (17308033 / 40000000) (216350413 / 500000000) (Real.log (308283 / 200000)) := by
  have h := reflection_log_14414_neg
  have he : Real.log (308283 / 200000) = -Real.log (200000 / 308283) := by
    rw [show ((308283 / 200000) : ℝ) = ((200000 / 308283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14415_neg : (48725601 / 62500000) ≤ -Real.log (91717 / 200000) ∧
    -Real.log (91717 / 200000) ≤ (389804809 / 500000000) := by
  have h := checkLog_sound (w := (8283 / 191717)) (n := 12)
    (lo := (21615609 / 250000000)) (hi := (86462437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91717) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91717) = 1/(91717 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14415 : Bounds (-389804809 / 500000000) (-48725601 / 62500000) (Real.log (91717 / 200000)) := by
  have h := reflection_log_14415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14416_neg : (43494559 / 100000000) ≤ -Real.log (1000000 / 1544879) ∧
    -Real.log (1000000 / 1544879) ≤ (434945591 / 1000000000) := by
  have h := checkLog_sound (w := (544879 / 2544879)) (n := 12)
    (lo := (43494559 / 100000000)) (hi := (434945591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1544879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1544879 / 1000000) = 1/(1000000 / 1544879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14416 : Bounds (43494559 / 100000000) (434945591 / 1000000000) (Real.log (1544879 / 1000000)) := by
  have h := reflection_log_14416_neg
  have he : Real.log (1544879 / 1000000) = -Real.log (1000000 / 1544879) := by
    rw [show ((1544879 / 1000000) : ℝ) = ((1000000 / 1544879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14417_neg : (19679799 / 25000000) ≤ -Real.log (455121 / 1000000) ∧
    -Real.log (455121 / 1000000) ≤ (393595981 / 500000000) := by
  have h := checkLog_sound (w := (44879 / 955121)) (n := 12)
    (lo := (4702239 / 50000000)) (hi := (94044781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455121) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 455121) = 1/(455121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14417 : Bounds (-393595981 / 500000000) (-19679799 / 25000000) (Real.log (455121 / 1000000)) := by
  have h := reflection_log_14417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14418_neg : (352246371 / 1000000000) ≤ -Real.log (703106875359 / 1000000000000) ∧
    -Real.log (703106875359 / 1000000000000) ≤ (88061593 / 250000000) := by
  have h := checkLog_sound (w := (296893124641 / 1703106875359)) (n := 12)
    (lo := (352246371 / 1000000000)) (hi := (88061593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 703106875359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 703106875359) = 1/(703106875359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14418 : Bounds (-88061593 / 250000000) (-352246371 / 1000000000) (Real.log (703106875359 / 1000000000000)) := by
  have h := reflection_log_14418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14419_neg : (346908791 / 1000000000) ≤ -Real.log (28274791911 / 40000000000) ∧
    -Real.log (28274791911 / 40000000000) ≤ (43363599 / 125000000) := by
  have h := checkLog_sound (w := (11725208089 / 68274791911)) (n := 12)
    (lo := (346908791 / 1000000000)) (hi := (43363599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28274791911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28274791911) = 1/(28274791911 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14419 : Bounds (-43363599 / 125000000) (-346908791 / 1000000000) (Real.log (28274791911 / 40000000000)) := by
  have h := reflection_log_14419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14420_neg : (606155221 / 500000000) ≤ -Real.log (125000000000 / 420155205687) ∧
    -Real.log (125000000000 / 420155205687) ≤ (303077611 / 250000000) := by
  have h := checkLog_sound (w := (170155205687 / 670155205687)) (n := 12)
    (lo := (259581631 / 500000000)) (hi := (519163263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420155205687 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(420155205687 / 250000000000) = 1/(125000000000 / 420155205687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14420 : Bounds (606155221 / 500000000) (303077611 / 250000000) (Real.log (420155205687 / 125000000000)) := by
  have h := reflection_log_14420_neg
  have he : Real.log (420155205687 / 125000000000) = -Real.log (125000000000 / 420155205687) := by
    rw [show ((420155205687 / 125000000000) : ℝ) = ((125000000000 / 420155205687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14421_neg : (24442751 / 20000000) ≤ -Real.log (500000000000 / 1697217882717) ∧
    -Real.log (500000000000 / 1697217882717) ≤ (76383597 / 62500000) := by
  have h := checkLog_sound (w := (697217882717 / 2697217882717)) (n := 12)
    (lo := (52899037 / 100000000)) (hi := (528990371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697217882717 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1697217882717 / 1000000000000) = 1/(500000000000 / 1697217882717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14421 : Bounds (24442751 / 20000000) (76383597 / 62500000) (Real.log (1697217882717 / 500000000000)) := by
  have h := reflection_log_14421_neg
  have he : Real.log (1697217882717 / 500000000000) = -Real.log (500000000000 / 1697217882717) := by
    rw [show ((1697217882717 / 500000000000) : ℝ) = ((500000000000 / 1697217882717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14422_neg : (2933962191 / 1000000000) ≤ -Real.log (500000000000 / 9400990099009) ∧
    -Real.log (500000000000 / 9400990099009) ≤ (733490549 / 250000000) := by
  have h := checkLog_sound (w := (1400990099009 / 17400990099009)) (n := 12)
    (lo := (161373471 / 1000000000)) (hi := (5042921 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9400990099009 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9400990099009 / 8000000000000) = 1/(500000000000 / 9400990099009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14422 : Bounds (2933962191 / 1000000000) (733490549 / 250000000) (Real.log (9400990099009 / 500000000000)) := by
  have h := reflection_log_14422_neg
  have he : Real.log (9400990099009 / 500000000000) = -Real.log (500000000000 / 9400990099009) := by
    rw [show ((9400990099009 / 500000000000) : ℝ) = ((500000000000 / 9400990099009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14423_neg : (1482846881 / 500000000) ≤ -Real.log (250000000000 / 4852040816327) ∧
    -Real.log (250000000000 / 4852040816327) ≤ (2965693767 / 1000000000) := by
  have h := checkLog_sound (w := (852040816327 / 8852040816327)) (n := 12)
    (lo := (96552521 / 500000000)) (hi := (193105043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4852040816327 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4852040816327 / 4000000000000) = 1/(250000000000 / 4852040816327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14423 : Bounds (1482846881 / 500000000) (2965693767 / 1000000000) (Real.log (4852040816327 / 250000000000)) := by
  have h := reflection_log_14423_neg
  have he : Real.log (4852040816327 / 250000000000) = -Real.log (250000000000 / 4852040816327) := by
    rw [show ((4852040816327 / 250000000000) : ℝ) = ((250000000000 / 4852040816327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14424_neg : (80560251 / 125000000) ≤ -Real.log (200 / 381) ∧
    -Real.log (200 / 381) ≤ (644482009 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 581)) (n := 12)
    (lo := (80560251 / 125000000)) (hi := (644482009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 200) = 1/(200 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14424 : Bounds (80560251 / 125000000) (644482009 / 1000000000) (Real.log (381 / 200)) := by
  have h := reflection_log_14424_neg
  have he : Real.log (381 / 200) = -Real.log (200 / 381) := by
    rw [show ((381 / 200) : ℝ) = ((200 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14425_neg : (470775677 / 200000000) ≤ -Real.log (19 / 200) ∧
    -Real.log (19 / 200) ≤ (2353878389 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 19) = 1/(19 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14425 : Bounds (-2353878389 / 1000000000) (-470775677 / 200000000) (Real.log (19 / 200)) := by
  have h := reflection_log_14425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14426_neg : (90459 / 100000000) ≤ -Real.log (200000 / 200181) ∧
    -Real.log (200000 / 200181) ≤ (904591 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 400181)) (n := 12)
    (lo := (90459 / 100000000)) (hi := (904591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200181 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200181 / 200000) = 1/(200000 / 200181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14426 : Bounds (90459 / 100000000) (904591 / 1000000000) (Real.log (200181 / 200000)) := by
  have h := reflection_log_14426_neg
  have he : Real.log (200181 / 200000) = -Real.log (200000 / 200181) := by
    rw [show ((200181 / 200000) : ℝ) = ((200000 / 200181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14427_neg : (905409 / 1000000000) ≤ -Real.log (199819 / 200000) ∧
    -Real.log (199819 / 200000) ≤ (90541 / 100000000) := by
  have h := checkLog_sound (w := (181 / 399819)) (n := 12)
    (lo := (905409 / 1000000000)) (hi := (90541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199819) = 1/(199819 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14427 : Bounds (-90541 / 100000000) (-905409 / 1000000000) (Real.log (199819 / 200000)) := by
  have h := reflection_log_14427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14428_neg : (217254607 / 500000000) ≤ -Real.log (200000 / 308841) ∧
    -Real.log (200000 / 308841) ≤ (86901843 / 200000000) := by
  have h := checkLog_sound (w := (108841 / 508841)) (n := 12)
    (lo := (217254607 / 500000000)) (hi := (86901843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308841 / 200000) = 1/(200000 / 308841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14428 : Bounds (217254607 / 500000000) (86901843 / 200000000) (Real.log (308841 / 200000)) := by
  have h := reflection_log_14428_neg
  have he : Real.log (308841 / 200000) = -Real.log (200000 / 308841) := by
    rw [show ((308841 / 200000) : ℝ) = ((200000 / 308841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14429_neg : (785712131 / 1000000000) ≤ -Real.log (91159 / 200000) ∧
    -Real.log (91159 / 200000) ≤ (785712133 / 1000000000) := by
  have h := checkLog_sound (w := (8841 / 191159)) (n := 12)
    (lo := (92564951 / 1000000000)) (hi := (11570619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91159) = 1/(91159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14429 : Bounds (-785712133 / 1000000000) (-785712131 / 1000000000) (Real.log (91159 / 200000)) := by
  have h := reflection_log_14429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14430_neg : (218382071 / 500000000) ≤ -Real.log (1000000 / 1547691) ∧
    -Real.log (1000000 / 1547691) ≤ (436764143 / 1000000000) := by
  have h := checkLog_sound (w := (547691 / 2547691)) (n := 12)
    (lo := (218382071 / 500000000)) (hi := (436764143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547691 / 1000000) = 1/(1000000 / 1547691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14430 : Bounds (218382071 / 500000000) (436764143 / 1000000000) (Real.log (1547691 / 1000000)) := by
  have h := reflection_log_14430_neg
  have he : Real.log (1547691 / 1000000) = -Real.log (1000000 / 1547691) := by
    rw [show ((1547691 / 1000000) : ℝ) = ((1000000 / 1547691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14431_neg : (793389703 / 1000000000) ≤ -Real.log (452309 / 1000000) ∧
    -Real.log (452309 / 1000000) ≤ (158677941 / 200000000) := by
  have h := checkLog_sound (w := (47691 / 952309)) (n := 12)
    (lo := (100242523 / 1000000000)) (hi := (25060631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 452309) = 1/(452309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14431 : Bounds (-158677941 / 200000000) (-793389703 / 1000000000) (Real.log (452309 / 1000000)) := by
  have h := reflection_log_14431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14432_neg : (356625561 / 1000000000) ≤ -Real.log (700034568519 / 1000000000000) ∧
    -Real.log (700034568519 / 1000000000000) ≤ (178312781 / 500000000) := by
  have h := checkLog_sound (w := (299965431481 / 1700034568519)) (n := 12)
    (lo := (356625561 / 1000000000)) (hi := (178312781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 700034568519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 700034568519) = 1/(700034568519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14432 : Bounds (-178312781 / 500000000) (-356625561 / 1000000000) (Real.log (700034568519 / 1000000000000)) := by
  have h := reflection_log_14432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14433_neg : (351202917 / 1000000000) ≤ -Real.log (28153636719 / 40000000000) ∧
    -Real.log (28153636719 / 40000000000) ≤ (175601459 / 500000000) := by
  have h := checkLog_sound (w := (11846363281 / 68153636719)) (n := 12)
    (lo := (351202917 / 1000000000)) (hi := (175601459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28153636719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28153636719) = 1/(28153636719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14433 : Bounds (-175601459 / 500000000) (-351202917 / 1000000000) (Real.log (28153636719 / 40000000000)) := by
  have h := reflection_log_14433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14434_neg : (610110673 / 500000000) ≤ -Real.log (31250000000 / 105873048739) ∧
    -Real.log (31250000000 / 105873048739) ≤ (305055337 / 250000000) := by
  have h := checkLog_sound (w := (43373048739 / 168373048739)) (n := 12)
    (lo := (263537083 / 500000000)) (hi := (527074167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105873048739 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105873048739 / 62500000000) = 1/(31250000000 / 105873048739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14434 : Bounds (610110673 / 500000000) (305055337 / 250000000) (Real.log (105873048739 / 31250000000)) := by
  have h := reflection_log_14434_neg
  have he : Real.log (105873048739 / 31250000000) = -Real.log (31250000000 / 105873048739) := by
    rw [show ((105873048739 / 31250000000) : ℝ) = ((31250000000 / 105873048739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14435_neg : (615076923 / 500000000) ≤ -Real.log (125000000000 / 427719490437) ∧
    -Real.log (125000000000 / 427719490437) ≤ (153769231 / 125000000) := by
  have h := checkLog_sound (w := (177719490437 / 677719490437)) (n := 12)
    (lo := (268503333 / 500000000)) (hi := (537006667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427719490437 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(427719490437 / 250000000000) = 1/(125000000000 / 427719490437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14435 : Bounds (615076923 / 500000000) (153769231 / 125000000) (Real.log (427719490437 / 125000000000)) := by
  have h := reflection_log_14435_neg
  have he : Real.log (427719490437 / 125000000000) = -Real.log (125000000000 / 427719490437) := by
    rw [show ((427719490437 / 125000000000) : ℝ) = ((125000000000 / 427719490437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14436_neg : (1482846881 / 500000000) ≤ -Real.log (500000000000 / 9704081632653) ∧
    -Real.log (500000000000 / 9704081632653) ≤ (2965693767 / 1000000000) := by
  have h := checkLog_sound (w := (1704081632653 / 17704081632653)) (n := 12)
    (lo := (96552521 / 500000000)) (hi := (193105043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9704081632653 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9704081632653 / 8000000000000) = 1/(500000000000 / 9704081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14436 : Bounds (1482846881 / 500000000) (2965693767 / 1000000000) (Real.log (9704081632653 / 500000000000)) := by
  have h := reflection_log_14436_neg
  have he : Real.log (9704081632653 / 500000000000) = -Real.log (500000000000 / 9704081632653) := by
    rw [show ((9704081632653 / 500000000000) : ℝ) = ((500000000000 / 9704081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14437_neg : (2998360393 / 1000000000) ≤ -Real.log (250000000000 / 5013157894737) ∧
    -Real.log (250000000000 / 5013157894737) ≤ (1499180199 / 500000000) := by
  have h := checkLog_sound (w := (1013157894737 / 9013157894737)) (n := 12)
    (lo := (225771673 / 1000000000)) (hi := (112885837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5013157894737 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5013157894737 / 4000000000000) = 1/(250000000000 / 5013157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14437 : Bounds (2998360393 / 1000000000) (1499180199 / 500000000) (Real.log (5013157894737 / 250000000000)) := by
  have h := reflection_log_14437_neg
  have he : Real.log (5013157894737 / 250000000000) = -Real.log (250000000000 / 5013157894737) := by
    rw [show ((5013157894737 / 250000000000) : ℝ) = ((250000000000 / 5013157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14438_neg : (646055573 / 1000000000) ≤ -Real.log (250 / 477) ∧
    -Real.log (250 / 477) ≤ (323027787 / 500000000) := by
  have h := checkLog_sound (w := (227 / 727)) (n := 12)
    (lo := (646055573 / 1000000000)) (hi := (323027787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 250) = 1/(250 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14438 : Bounds (646055573 / 1000000000) (323027787 / 500000000) (Real.log (477 / 250)) := by
  have h := reflection_log_14438_neg
  have he : Real.log (477 / 250) = -Real.log (250 / 477) := by
    rw [show ((477 / 250) : ℝ) = ((250 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14439_neg : (23859667 / 10000000) ≤ -Real.log (23 / 250) ∧
    -Real.log (23 / 250) ≤ (149122919 / 62500000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 92) = 1/(23 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14439 : Bounds (-149122919 / 62500000) (-23859667 / 10000000) (Real.log (23 / 250)) := by
  have h := reflection_log_14439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14440_neg : (226897 / 250000000) ≤ -Real.log (250000 / 250227) ∧
    -Real.log (250000 / 250227) ≤ (907589 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 500227)) (n := 12)
    (lo := (226897 / 250000000)) (hi := (907589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250227 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250227 / 250000) = 1/(250000 / 250227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14440 : Bounds (226897 / 250000000) (907589 / 1000000000) (Real.log (250227 / 250000)) := by
  have h := reflection_log_14440_neg
  have he : Real.log (250227 / 250000) = -Real.log (250000 / 250227) := by
    rw [show ((250227 / 250000) : ℝ) = ((250000 / 250227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14441_neg : (227103 / 250000000) ≤ -Real.log (249773 / 250000) ∧
    -Real.log (249773 / 250000) ≤ (908413 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 499773)) (n := 12)
    (lo := (227103 / 250000000)) (hi := (908413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249773) = 1/(249773 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14441 : Bounds (-908413 / 1000000000) (-227103 / 250000000) (Real.log (249773 / 250000)) := by
  have h := reflection_log_14441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14442_neg : (5454107 / 12500000) ≤ -Real.log (1000000 / 1547017) ∧
    -Real.log (1000000 / 1547017) ≤ (436328561 / 1000000000) := by
  have h := checkLog_sound (w := (547017 / 2547017)) (n := 12)
    (lo := (5454107 / 12500000)) (hi := (436328561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547017 / 1000000) = 1/(1000000 / 1547017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14442 : Bounds (5454107 / 12500000) (436328561 / 1000000000) (Real.log (1547017 / 1000000)) := by
  have h := reflection_log_14442_neg
  have he : Real.log (1547017 / 1000000) = -Real.log (1000000 / 1547017) := by
    rw [show ((1547017 / 1000000) : ℝ) = ((1000000 / 1547017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14443_neg : (791900681 / 1000000000) ≤ -Real.log (452983 / 1000000) ∧
    -Real.log (452983 / 1000000) ≤ (791900683 / 1000000000) := by
  have h := checkLog_sound (w := (47017 / 952983)) (n := 12)
    (lo := (98753501 / 1000000000)) (hi := (49376751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 452983) = 1/(452983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14443 : Bounds (-791900683 / 1000000000) (-791900681 / 1000000000) (Real.log (452983 / 1000000)) := by
  have h := reflection_log_14443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14444_neg : (219296469 / 500000000) ≤ -Real.log (250000 / 387631) ∧
    -Real.log (250000 / 387631) ≤ (438592939 / 1000000000) := by
  have h := checkLog_sound (w := (137631 / 637631)) (n := 12)
    (lo := (219296469 / 500000000)) (hi := (438592939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387631 / 250000) = 1/(250000 / 387631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14444 : Bounds (219296469 / 500000000) (438592939 / 1000000000) (Real.log (387631 / 250000)) := by
  have h := reflection_log_14444_neg
  have he : Real.log (387631 / 250000) = -Real.log (250000 / 387631) := by
    rw [show ((387631 / 250000) : ℝ) = ((250000 / 387631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14445_neg : (399836409 / 500000000) ≤ -Real.log (112369 / 250000) ∧
    -Real.log (112369 / 250000) ≤ (39983641 / 50000000) := by
  have h := checkLog_sound (w := (12631 / 237369)) (n := 12)
    (lo := (53262819 / 500000000)) (hi := (106525639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112369) = 1/(112369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14445 : Bounds (-39983641 / 50000000) (-399836409 / 500000000) (Real.log (112369 / 250000)) := by
  have h := reflection_log_14445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14446_neg : (9026997 / 25000000) ≤ -Real.log (43557707839 / 62500000000) ∧
    -Real.log (43557707839 / 62500000000) ≤ (361079881 / 1000000000) := by
  have h := checkLog_sound (w := (18942292161 / 106057707839)) (n := 12)
    (lo := (9026997 / 25000000)) (hi := (361079881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 43557707839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 43557707839) = 1/(43557707839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14446 : Bounds (-361079881 / 1000000000) (-9026997 / 25000000) (Real.log (43557707839 / 62500000000)) := by
  have h := reflection_log_14446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14447_neg : (355572121 / 1000000000) ≤ -Real.log (700772401711 / 1000000000000) ∧
    -Real.log (700772401711 / 1000000000000) ≤ (177786061 / 500000000) := by
  have h := checkLog_sound (w := (299227598289 / 1700772401711)) (n := 12)
    (lo := (355572121 / 1000000000)) (hi := (177786061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 700772401711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 700772401711) = 1/(700772401711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14447 : Bounds (-177786061 / 500000000) (-355572121 / 1000000000) (Real.log (700772401711 / 1000000000000)) := by
  have h := reflection_log_14447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14448_neg : (1228229241 / 1000000000) ≤ -Real.log (500000000000 / 1707588364243) ∧
    -Real.log (500000000000 / 1707588364243) ≤ (1228229243 / 1000000000) := by
  have h := checkLog_sound (w := (707588364243 / 2707588364243)) (n := 12)
    (lo := (535082061 / 1000000000)) (hi := (267541031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707588364243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1707588364243 / 1000000000000) = 1/(500000000000 / 1707588364243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14448 : Bounds (1228229241 / 1000000000) (1228229243 / 1000000000) (Real.log (1707588364243 / 500000000000)) := by
  have h := reflection_log_14448_neg
  have he : Real.log (1707588364243 / 500000000000) = -Real.log (500000000000 / 1707588364243) := by
    rw [show ((1707588364243 / 500000000000) : ℝ) = ((500000000000 / 1707588364243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14449_neg : (309566439 / 250000000) ≤ -Real.log (125000000000 / 431203223309) ∧
    -Real.log (125000000000 / 431203223309) ≤ (619132879 / 500000000) := by
  have h := checkLog_sound (w := (181203223309 / 681203223309)) (n := 12)
    (lo := (34069911 / 62500000)) (hi := (545118577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431203223309 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(431203223309 / 250000000000) = 1/(125000000000 / 431203223309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14449 : Bounds (309566439 / 250000000) (619132879 / 500000000) (Real.log (431203223309 / 125000000000)) := by
  have h := reflection_log_14449_neg
  have he : Real.log (431203223309 / 125000000000) = -Real.log (125000000000 / 431203223309) := by
    rw [show ((431203223309 / 125000000000) : ℝ) = ((125000000000 / 431203223309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14450_neg : (2998360393 / 1000000000) ≤ -Real.log (500000000000 / 10026315789473) ∧
    -Real.log (500000000000 / 10026315789473) ≤ (1499180199 / 500000000) := by
  have h := checkLog_sound (w := (2026315789473 / 18026315789473)) (n := 12)
    (lo := (225771673 / 1000000000)) (hi := (112885837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10026315789473 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10026315789473 / 8000000000000) = 1/(500000000000 / 10026315789473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14450 : Bounds (2998360393 / 1000000000) (1499180199 / 500000000) (Real.log (10026315789473 / 500000000000)) := by
  have h := reflection_log_14450_neg
  have he : Real.log (10026315789473 / 500000000000) = -Real.log (500000000000 / 10026315789473) := by
    rw [show ((10026315789473 / 500000000000) : ℝ) = ((500000000000 / 10026315789473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14451_neg : (11843837 / 3906250) ≤ -Real.log (31250000000 / 648097826087) ∧
    -Real.log (31250000000 / 648097826087) ≤ (3032022277 / 1000000000) := by
  have h := checkLog_sound (w := (148097826087 / 1148097826087)) (n := 12)
    (lo := (16214597 / 62500000)) (hi := (259433553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648097826087 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(648097826087 / 500000000000) = 1/(31250000000 / 648097826087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14451 : Bounds (11843837 / 3906250) (3032022277 / 1000000000) (Real.log (648097826087 / 31250000000)) := by
  have h := reflection_log_14451_neg
  have he : Real.log (648097826087 / 31250000000) = -Real.log (31250000000 / 648097826087) := by
    rw [show ((648097826087 / 31250000000) : ℝ) = ((31250000000 / 648097826087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14452_neg : (129525333 / 200000000) ≤ -Real.log (1000 / 1911) ∧
    -Real.log (1000 / 1911) ≤ (323813333 / 500000000) := by
  have h := checkLog_sound (w := (911 / 2911)) (n := 12)
    (lo := (129525333 / 200000000)) (hi := (323813333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1000) = 1/(1000 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14452 : Bounds (129525333 / 200000000) (323813333 / 500000000) (Real.log (1911 / 1000)) := by
  have h := reflection_log_14452_neg
  have he : Real.log (1911 / 1000) = -Real.log (1000 / 1911) := by
    rw [show ((1911 / 1000) : ℝ) = ((1000 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14453_neg : (2419118907 / 1000000000) ≤ -Real.log (89 / 1000) ∧
    -Real.log (89 / 1000) ≤ (2419118911 / 1000000000) := by
  have h := checkLog_sound (w := (18 / 107)) (n := 12)
    (lo := (339677367 / 1000000000)) (hi := (42459671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 89) = 1/(89 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14453 : Bounds (-2419118911 / 1000000000) (-2419118907 / 1000000000) (Real.log (89 / 1000)) := by
  have h := reflection_log_14453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14454_neg : (182117 / 200000000) ≤ -Real.log (1000000 / 1000911) ∧
    -Real.log (1000000 / 1000911) ≤ (455293 / 500000000) := by
  have h := checkLog_sound (w := (911 / 2000911)) (n := 12)
    (lo := (182117 / 200000000)) (hi := (455293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000911 / 1000000) = 1/(1000000 / 1000911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14454 : Bounds (182117 / 200000000) (455293 / 500000000) (Real.log (1000911 / 1000000)) := by
  have h := reflection_log_14454_neg
  have he : Real.log (1000911 / 1000000) = -Real.log (1000000 / 1000911) := by
    rw [show ((1000911 / 1000000) : ℝ) = ((1000000 / 1000911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14455_neg : (182283 / 200000000) ≤ -Real.log (999089 / 1000000) ∧
    -Real.log (999089 / 1000000) ≤ (113927 / 125000000) := by
  have h := checkLog_sound (w := (911 / 1999089)) (n := 12)
    (lo := (182283 / 200000000)) (hi := (113927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999089) = 1/(999089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14455 : Bounds (-113927 / 125000000) (-182283 / 200000000) (Real.log (999089 / 1000000)) := by
  have h := reflection_log_14455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14456_neg : (219079721 / 500000000) ≤ -Real.log (250000 / 387463) ∧
    -Real.log (250000 / 387463) ≤ (438159443 / 1000000000) := by
  have h := checkLog_sound (w := (137463 / 637463)) (n := 12)
    (lo := (219079721 / 500000000)) (hi := (438159443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387463 / 250000) = 1/(250000 / 387463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14456 : Bounds (219079721 / 500000000) (438159443 / 1000000000) (Real.log (387463 / 250000)) := by
  have h := reflection_log_14456_neg
  have he : Real.log (387463 / 250000) = -Real.log (250000 / 387463) := by
    rw [show ((387463 / 250000) : ℝ) = ((250000 / 387463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14457_neg : (39908943 / 50000000) ≤ -Real.log (112537 / 250000) ∧
    -Real.log (112537 / 250000) ≤ (399089431 / 500000000) := by
  have h := checkLog_sound (w := (12463 / 237537)) (n := 12)
    (lo := (41028 / 390625)) (hi := (105031681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112537) = 1/(112537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14457 : Bounds (-399089431 / 500000000) (-39908943 / 50000000) (Real.log (112537 / 250000)) := by
  have h := reflection_log_14457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14458_neg : (88086769 / 200000000) ≤ -Real.log (1000000 / 1553381) ∧
    -Real.log (1000000 / 1553381) ≤ (220216923 / 500000000) := by
  have h := checkLog_sound (w := (553381 / 2553381)) (n := 12)
    (lo := (88086769 / 200000000)) (hi := (220216923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1553381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1553381 / 1000000) = 1/(1000000 / 1553381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14458 : Bounds (88086769 / 200000000) (220216923 / 500000000) (Real.log (1553381 / 1000000)) := by
  have h := reflection_log_14458_neg
  have he : Real.log (1553381 / 1000000) = -Real.log (1000000 / 1553381) := by
    rw [show ((1553381 / 1000000) : ℝ) = ((1000000 / 1553381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14459_neg : (201512349 / 250000000) ≤ -Real.log (446619 / 1000000) ∧
    -Real.log (446619 / 1000000) ≤ (403024699 / 500000000) := by
  have h := checkLog_sound (w := (53381 / 946619)) (n := 12)
    (lo := (14112777 / 125000000)) (hi := (112902217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 446619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 446619) = 1/(446619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14459 : Bounds (-403024699 / 500000000) (-201512349 / 250000000) (Real.log (446619 / 1000000)) := by
  have h := reflection_log_14459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14460_neg : (365615551 / 1000000000) ≤ -Real.log (693769468839 / 1000000000000) ∧
    -Real.log (693769468839 / 1000000000000) ≤ (5712743 / 15625000) := by
  have h := checkLog_sound (w := (306230531161 / 1693769468839)) (n := 12)
    (lo := (365615551 / 1000000000)) (hi := (5712743 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 693769468839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 693769468839) = 1/(693769468839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14460 : Bounds (-5712743 / 15625000) (-365615551 / 1000000000) (Real.log (693769468839 / 1000000000000)) := by
  have h := reflection_log_14460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14461_neg : (180009709 / 500000000) ≤ -Real.log (43603923631 / 62500000000) ∧
    -Real.log (43603923631 / 62500000000) ≤ (360019419 / 1000000000) := by
  have h := checkLog_sound (w := (18896076369 / 106103923631)) (n := 12)
    (lo := (180009709 / 500000000)) (hi := (360019419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 43603923631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 43603923631) = 1/(43603923631 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14461 : Bounds (-360019419 / 1000000000) (-180009709 / 500000000) (Real.log (43603923631 / 62500000000)) := by
  have h := reflection_log_14461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14462_neg : (1236338303 / 1000000000) ≤ -Real.log (250000000000 / 860745799159) ∧
    -Real.log (250000000000 / 860745799159) ≤ (247267661 / 200000000) := by
  have h := checkLog_sound (w := (360745799159 / 1360745799159)) (n := 12)
    (lo := (543191123 / 1000000000)) (hi := (135797781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((860745799159 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(860745799159 / 500000000000) = 1/(250000000000 / 860745799159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14462 : Bounds (1236338303 / 1000000000) (247267661 / 200000000) (Real.log (860745799159 / 250000000000)) := by
  have h := reflection_log_14462_neg
  have he : Real.log (860745799159 / 250000000000) = -Real.log (250000000000 / 860745799159) := by
    rw [show ((860745799159 / 250000000000) : ℝ) = ((250000000000 / 860745799159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14463_neg : (1246483241 / 1000000000) ≤ -Real.log (250000000000 / 869522456501) ∧
    -Real.log (250000000000 / 869522456501) ≤ (1246483243 / 1000000000) := by
  have h := checkLog_sound (w := (369522456501 / 1369522456501)) (n := 12)
    (lo := (553336061 / 1000000000)) (hi := (276668031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869522456501 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(869522456501 / 500000000000) = 1/(250000000000 / 869522456501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14463 : Bounds (1246483241 / 1000000000) (1246483243 / 1000000000) (Real.log (869522456501 / 250000000000)) := by
  have h := reflection_log_14463_neg
  have he : Real.log (869522456501 / 250000000000) = -Real.log (250000000000 / 869522456501) := by
    rw [show ((869522456501 / 250000000000) : ℝ) = ((250000000000 / 869522456501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
