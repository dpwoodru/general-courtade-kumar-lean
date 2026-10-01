import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell253
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (20977177 / 62500000) ≤ -Real.log (2560 / 3581) ∧
    -Real.log (2560 / 3581) ≤ (335634833 / 1000000000) := by
  have h := checkLog_sound (w := (1021 / 6141)) (n := 12)
    (lo := (20977177 / 62500000)) (hi := (335634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3581 / 2560) = 1/(2560 / 3581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20977177 / 62500000) (335634833 / 1000000000) (Real.log (3581 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3581 / 2560) = -Real.log (2560 / 3581) := by
    rw [show ((3581 / 2560) : ℝ) = ((2560 / 3581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (508874403 / 1000000000) ≤ -Real.log (1539 / 2560) ∧
    -Real.log (1539 / 2560) ≤ (127218601 / 250000000) := by
  have h := checkLog_sound (w := (1021 / 4099)) (n := 12)
    (lo := (508874403 / 1000000000)) (hi := (127218601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1539) = 1/(1539 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127218601 / 250000000) (-508874403 / 1000000000) (Real.log (1539 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335215867 / 1000000000) ≤ -Real.log (5120 / 7159) ∧
    -Real.log (5120 / 7159) ≤ (83803967 / 250000000) := by
  have h := checkLog_sound (w := (2039 / 12279)) (n := 12)
    (lo := (335215867 / 1000000000)) (hi := (83803967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7159 / 5120) = 1/(5120 / 7159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335215867 / 1000000000) (83803967 / 250000000) (Real.log (7159 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7159 / 5120) = -Real.log (5120 / 7159) := by
    rw [show ((7159 / 5120) : ℝ) = ((5120 / 7159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (507900219 / 1000000000) ≤ -Real.log (3081 / 5120) ∧
    -Real.log (3081 / 5120) ≤ (25395011 / 50000000) := by
  have h := checkLog_sound (w := (2039 / 8201)) (n := 12)
    (lo := (507900219 / 1000000000)) (hi := (25395011 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3081) = 1/(3081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-25395011 / 50000000) (-507900219 / 1000000000) (Real.log (3081 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49932791 / 200000000) ≤ -Real.log (500000 / 641797) ∧
    -Real.log (500000 / 641797) ≤ (62415989 / 250000000) := by
  have h := checkLog_sound (w := (141797 / 1141797)) (n := 12)
    (lo := (49932791 / 200000000)) (hi := (62415989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641797 / 500000) = 1/(500000 / 641797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49932791 / 200000000) (62415989 / 250000000) (Real.log (641797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (641797 / 500000) = -Real.log (500000 / 641797) := by
    rw [show ((641797 / 500000) : ℝ) = ((500000 / 641797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (333508233 / 1000000000) ≤ -Real.log (358203 / 500000) ∧
    -Real.log (358203 / 500000) ≤ (166754117 / 500000000) := by
  have h := checkLog_sound (w := (141797 / 858203)) (n := 12)
    (lo := (333508233 / 1000000000)) (hi := (166754117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358203) = 1/(358203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166754117 / 500000000) (-333508233 / 1000000000) (Real.log (358203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (249994223 / 1000000000) ≤ -Real.log (500000 / 642009) ∧
    -Real.log (500000 / 642009) ≤ (15624639 / 62500000) := by
  have h := checkLog_sound (w := (142009 / 1142009)) (n := 12)
    (lo := (249994223 / 1000000000)) (hi := (15624639 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642009 / 500000) = 1/(500000 / 642009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (249994223 / 1000000000) (15624639 / 62500000) (Real.log (642009 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642009 / 500000) = -Real.log (500000 / 642009) := by
    rw [show ((642009 / 500000) : ℝ) = ((500000 / 642009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (83525063 / 250000000) ≤ -Real.log (357991 / 500000) ∧
    -Real.log (357991 / 500000) ≤ (334100253 / 1000000000) := by
  have h := checkLog_sound (w := (142009 / 857991)) (n := 12)
    (lo := (83525063 / 250000000)) (hi := (334100253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357991) = 1/(357991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334100253 / 1000000000) (-83525063 / 250000000) (Real.log (357991 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186561721 / 1000000000) ≤ -Real.log (1000000 / 1205099) ∧
    -Real.log (1000000 / 1205099) ≤ (93280861 / 500000000) := by
  have h := checkLog_sound (w := (205099 / 2205099)) (n := 12)
    (lo := (186561721 / 1000000000)) (hi := (93280861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205099 / 1000000) = 1/(1000000 / 1205099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186561721 / 1000000000) (93280861 / 500000000) (Real.log (1205099 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1205099 / 1000000) = -Real.log (1000000 / 1205099) := by
    rw [show ((1205099 / 1000000) : ℝ) = ((1000000 / 1205099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2295377 / 10000000) ≤ -Real.log (794901 / 1000000) ∧
    -Real.log (794901 / 1000000) ≤ (229537701 / 1000000000) := by
  have h := checkLog_sound (w := (205099 / 1794901)) (n := 12)
    (lo := (2295377 / 10000000)) (hi := (229537701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794901) = 1/(794901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-229537701 / 1000000000) (-2295377 / 10000000) (Real.log (794901 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186828053 / 1000000000) ≤ -Real.log (50000 / 60271) ∧
    -Real.log (50000 / 60271) ≤ (93414027 / 500000000) := by
  have h := checkLog_sound (w := (10271 / 110271)) (n := 12)
    (lo := (186828053 / 1000000000)) (hi := (93414027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60271 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60271 / 50000) = 1/(50000 / 60271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186828053 / 1000000000) (93414027 / 500000000) (Real.log (60271 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60271 / 50000) = -Real.log (50000 / 60271) := by
    rw [show ((60271 / 50000) : ℝ) = ((50000 / 60271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45988321 / 200000000) ≤ -Real.log (39729 / 50000) ∧
    -Real.log (39729 / 50000) ≤ (114970803 / 500000000) := by
  have h := checkLog_sound (w := (10271 / 89729)) (n := 12)
    (lo := (45988321 / 200000000)) (hi := (114970803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39729) = 1/(39729 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114970803 / 500000000) (-45988321 / 200000000) (Real.log (39729 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (421558043 / 500000000) ≤ -Real.log (250000000000 / 580899058747) ∧
    -Real.log (250000000000 / 580899058747) ≤ (105389511 / 125000000) := by
  have h := checkLog_sound (w := (80899058747 / 1080899058747)) (n := 12)
    (lo := (74984453 / 500000000)) (hi := (149968907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580899058747 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(580899058747 / 500000000000) = 1/(250000000000 / 580899058747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (421558043 / 500000000) (105389511 / 125000000) (Real.log (580899058747 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (580899058747 / 250000000000) = -Real.log (250000000000 / 580899058747) := by
    rw [show ((580899058747 / 250000000000) : ℝ) = ((250000000000 / 580899058747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (168901847 / 200000000) ≤ -Real.log (500000000000 / 1163417803769) ∧
    -Real.log (500000000000 / 1163417803769) ≤ (844509237 / 1000000000) := by
  have h := checkLog_sound (w := (163417803769 / 2163417803769)) (n := 12)
    (lo := (30272411 / 200000000)) (hi := (18920257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163417803769 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1163417803769 / 1000000000000) = 1/(500000000000 / 1163417803769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (168901847 / 200000000) (844509237 / 1000000000) (Real.log (1163417803769 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1163417803769 / 500000000000) = -Real.log (500000000000 / 1163417803769) := by
    rw [show ((1163417803769 / 500000000000) : ℝ) = ((500000000000 / 1163417803769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (583172189 / 1000000000) ≤ -Real.log (62500000000 / 111982067431) ∧
    -Real.log (62500000000 / 111982067431) ≤ (58317219 / 100000000) := by
  have h := checkLog_sound (w := (49482067431 / 174482067431)) (n := 12)
    (lo := (583172189 / 1000000000)) (hi := (58317219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111982067431 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111982067431 / 62500000000) = 1/(62500000000 / 111982067431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (583172189 / 1000000000) (58317219 / 100000000) (Real.log (111982067431 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (111982067431 / 62500000000) = -Real.log (62500000000 / 111982067431) := by
    rw [show ((111982067431 / 62500000000) : ℝ) = ((62500000000 / 111982067431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23363779 / 40000000) ≤ -Real.log (12500000000 / 22417078921) ∧
    -Real.log (12500000000 / 22417078921) ≤ (146023619 / 250000000) := by
  have h := checkLog_sound (w := (9917078921 / 34917078921)) (n := 12)
    (lo := (23363779 / 40000000)) (hi := (146023619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22417078921 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22417078921 / 12500000000) = 1/(12500000000 / 22417078921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23363779 / 40000000) (146023619 / 250000000) (Real.log (22417078921 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (22417078921 / 12500000000) = -Real.log (12500000000 / 22417078921) := by
    rw [show ((22417078921 / 12500000000) : ℝ) = ((12500000000 / 22417078921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (416099421 / 1000000000) ≤ -Real.log (250000000000 / 379009147051) ∧
    -Real.log (250000000000 / 379009147051) ≤ (208049711 / 500000000) := by
  have h := checkLog_sound (w := (129009147051 / 629009147051)) (n := 12)
    (lo := (416099421 / 1000000000)) (hi := (208049711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379009147051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379009147051 / 250000000000) = 1/(250000000000 / 379009147051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (416099421 / 1000000000) (208049711 / 500000000) (Real.log (379009147051 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379009147051 / 250000000000) = -Real.log (250000000000 / 379009147051) := by
    rw [show ((379009147051 / 250000000000) : ℝ) = ((250000000000 / 379009147051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (416769659 / 1000000000) ≤ -Real.log (250000000000 / 379263258577) ∧
    -Real.log (250000000000 / 379263258577) ≤ (20838483 / 50000000) := by
  have h := checkLog_sound (w := (129263258577 / 629263258577)) (n := 12)
    (lo := (416769659 / 1000000000)) (hi := (20838483 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379263258577 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379263258577 / 250000000000) = 1/(250000000000 / 379263258577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (416769659 / 1000000000) (20838483 / 50000000) (Real.log (379263258577 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (379263258577 / 250000000000) = -Real.log (250000000000 / 379263258577) := by
    rw [show ((379263258577 / 250000000000) : ℝ) = ((250000000000 / 379263258577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43113551 / 1000000000) ≤ -Real.log (2394506559 / 2500000000) ∧
    -Real.log (2394506559 / 2500000000) ≤ (2694597 / 62500000) := by
  have h := checkLog_sound (w := (105493441 / 4894506559)) (n := 12)
    (lo := (43113551 / 1000000000)) (hi := (2694597 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2394506559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2394506559) = 1/(2394506559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2694597 / 62500000) (-43113551 / 1000000000) (Real.log (2394506559 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42975979 / 1000000000) ≤ -Real.log (957934400199 / 1000000000000) ∧
    -Real.log (957934400199 / 1000000000000) ≤ (2148799 / 50000000) := by
  have h := checkLog_sound (w := (42065599801 / 1957934400199)) (n := 12)
    (lo := (42975979 / 1000000000)) (hi := (2148799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957934400199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957934400199) = 1/(957934400199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2148799 / 50000000) (-42975979 / 1000000000) (Real.log (957934400199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell253
