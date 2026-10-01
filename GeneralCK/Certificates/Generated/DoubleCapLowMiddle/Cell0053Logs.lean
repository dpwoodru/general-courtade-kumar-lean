import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053
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

theorem reflection_log_1_neg : (678776841 / 1000000000) ≤ -Real.log (51200 / 100939) ∧
    -Real.log (51200 / 100939) ≤ (339388421 / 500000000) := by
  have h := checkLog_sound (w := (49739 / 152139)) (n := 12)
    (lo := (678776841 / 1000000000)) (hi := (339388421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100939 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100939 / 51200) = 1/(51200 / 100939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678776841 / 1000000000) (339388421 / 500000000) (Real.log (100939 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100939 / 51200) = -Real.log (51200 / 100939) := by
    rw [show ((100939 / 51200) : ℝ) = ((51200 / 100939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (889154599 / 250000000) ≤ -Real.log (1461 / 51200) ∧
    -Real.log (1461 / 51200) ≤ (1778309201 / 500000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1461) = 1/(1461 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1778309201 / 500000000) (-889154599 / 250000000) (Real.log (1461 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678682721 / 1000000000) ≤ -Real.log (102400 / 201859) ∧
    -Real.log (102400 / 201859) ≤ (339341361 / 500000000) := by
  have h := checkLog_sound (w := (99459 / 304259)) (n := 12)
    (lo := (678682721 / 1000000000)) (hi := (339341361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201859 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201859 / 102400) = 1/(102400 / 201859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678682721 / 1000000000) (339341361 / 500000000) (Real.log (201859 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201859 / 102400) = -Real.log (102400 / 201859) := by
    rw [show ((201859 / 102400) : ℝ) = ((102400 / 201859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71002741 / 20000000) ≤ -Real.log (2941 / 102400) ∧
    -Real.log (2941 / 102400) ≤ (110941783 / 31250000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2941) = 1/(2941 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-110941783 / 31250000) (-71002741 / 20000000) (Real.log (2941 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332098491 / 500000000) ≤ -Real.log (25600 / 49739) ∧
    -Real.log (25600 / 49739) ≤ (664196983 / 1000000000) := by
  have h := checkLog_sound (w := (24139 / 75339)) (n := 12)
    (lo := (332098491 / 500000000)) (hi := (664196983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49739 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49739 / 25600) = 1/(25600 / 49739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332098491 / 500000000) (664196983 / 1000000000) (Real.log (49739 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49739 / 25600) = -Real.log (25600 / 49739) := by
    rw [show ((49739 / 25600) : ℝ) = ((25600 / 49739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (178966951 / 62500000) ≤ -Real.log (1461 / 25600) ∧
    -Real.log (1461 / 25600) ≤ (2863471221 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1461) = 1/(1461 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2863471221 / 1000000000) (-178966951 / 62500000) (Real.log (1461 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332002983 / 500000000) ≤ -Real.log (51200 / 99459) ∧
    -Real.log (51200 / 99459) ≤ (664005967 / 1000000000) := by
  have h := checkLog_sound (w := (48259 / 150659)) (n := 12)
    (lo := (332002983 / 500000000)) (hi := (664005967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99459 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99459 / 51200) = 1/(51200 / 99459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332002983 / 500000000) (664005967 / 1000000000) (Real.log (99459 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99459 / 51200) = -Real.log (51200 / 99459) := by
    rw [show ((99459 / 51200) : ℝ) = ((51200 / 99459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285698987 / 100000000) ≤ -Real.log (2941 / 51200) ∧
    -Real.log (2941 / 51200) ≤ (22855919 / 8000000) := by
  have h := checkLog_sound (w := (259 / 6141)) (n := 12)
    (lo := (1688023 / 20000000)) (hi := (84401151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2941) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2941) = 1/(2941 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-22855919 / 8000000) (-285698987 / 100000000) (Real.log (2941 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340522117 / 500000000) ≤ -Real.log (50000 / 98797) ∧
    -Real.log (50000 / 98797) ≤ (136208847 / 200000000) := by
  have h := checkLog_sound (w := (48797 / 148797)) (n := 12)
    (lo := (340522117 / 500000000)) (hi := (136208847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98797 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98797 / 50000) = 1/(50000 / 98797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340522117 / 500000000) (136208847 / 200000000) (Real.log (98797 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98797 / 50000) = -Real.log (50000 / 98797) := by
    rw [show ((98797 / 50000) : ℝ) = ((50000 / 98797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (745440913 / 200000000) ≤ -Real.log (1203 / 50000) ∧
    -Real.log (1203 / 50000) ≤ (3727204571 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 5531)) (n := 12)
    (lo := (52293733 / 200000000)) (hi := (130734333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2406) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2406) = 1/(1203 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3727204571 / 1000000000) (-745440913 / 200000000) (Real.log (1203 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340559819 / 500000000) ≤ -Real.log (1000000 / 1976089) ∧
    -Real.log (1000000 / 1976089) ≤ (681119639 / 1000000000) := by
  have h := checkLog_sound (w := (976089 / 2976089)) (n := 12)
    (lo := (340559819 / 500000000)) (hi := (681119639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976089 / 1000000) = 1/(1000000 / 1976089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340559819 / 500000000) (681119639 / 1000000000) (Real.log (1976089 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976089 / 1000000) = -Real.log (1000000 / 1976089) := by
    rw [show ((1976089 / 1000000) : ℝ) = ((1000000 / 1976089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (116669271 / 31250000) ≤ -Real.log (23911 / 1000000) ∧
    -Real.log (23911 / 1000000) ≤ (1866708339 / 500000000) := by
  have h := checkLog_sound (w := (7339 / 55161)) (n := 12)
    (lo := (66920193 / 250000000)) (hi := (267680773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23911) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23911) = 1/(23911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1866708339 / 500000000) (-116669271 / 31250000) (Real.log (23911 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680974391 / 1000000000) ≤ -Real.log (500000 / 987901) ∧
    -Real.log (500000 / 987901) ≤ (85121799 / 125000000) := by
  have h := checkLog_sound (w := (487901 / 1487901)) (n := 12)
    (lo := (680974391 / 1000000000)) (hi := (85121799 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987901 / 500000) = 1/(500000 / 987901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680974391 / 1000000000) (85121799 / 125000000) (Real.log (987901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987901 / 500000) = -Real.log (500000 / 987901) := by
    rw [show ((987901 / 500000) : ℝ) = ((500000 / 987901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3721485291 / 1000000000) ≤ -Real.log (12099 / 500000) ∧
    -Real.log (12099 / 500000) ≤ (3721485297 / 1000000000) := by
  have h := checkLog_sound (w := (1763 / 13862)) (n := 12)
    (lo := (255749391 / 1000000000)) (hi := (15984337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12099) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12099) = 1/(12099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3721485297 / 1000000000) (-3721485291 / 1000000000) (Real.log (12099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681050813 / 1000000000) ≤ -Real.log (1000000 / 1975953) ∧
    -Real.log (1000000 / 1975953) ≤ (340525407 / 500000000) := by
  have h := checkLog_sound (w := (975953 / 2975953)) (n := 12)
    (lo := (681050813 / 1000000000)) (hi := (340525407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975953 / 1000000) = 1/(1000000 / 1975953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681050813 / 1000000000) (340525407 / 500000000) (Real.log (1975953 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975953 / 1000000) = -Real.log (1000000 / 1975953) := by
    rw [show ((1975953 / 1000000) : ℝ) = ((1000000 / 1975953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3727745027 / 1000000000) ≤ -Real.log (24047 / 1000000) ∧
    -Real.log (24047 / 1000000) ≤ (3727745033 / 1000000000) := by
  have h := checkLog_sound (w := (7203 / 55297)) (n := 12)
    (lo := (262009127 / 1000000000)) (hi := (32751141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24047) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24047) = 1/(24047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3727745033 / 1000000000) (-3727745027 / 1000000000) (Real.log (24047 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4408248799 / 1000000000) ≤ -Real.log (31250000000 / 2566422485453) ∧
    -Real.log (31250000000 / 2566422485453) ≤ (2204124403 / 500000000) := by
  have h := checkLog_sound (w := (566422485453 / 4566422485453)) (n := 12)
    (lo := (249365719 / 1000000000)) (hi := (6234143 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2566422485453 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2566422485453 / 2000000000000) = 1/(31250000000 / 2566422485453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4408248799 / 1000000000) (2204124403 / 500000000) (Real.log (2566422485453 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2566422485453 / 31250000000) = -Real.log (31250000000 / 2566422485453) := by
    rw [show ((2566422485453 / 31250000000) : ℝ) = ((31250000000 / 2566422485453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (441453631 / 100000000) ≤ -Real.log (62500000000 / 5165219459663) ∧
    -Real.log (62500000000 / 5165219459663) ≤ (4414536317 / 1000000000) := by
  have h := checkLog_sound (w := (1165219459663 / 9165219459663)) (n := 12)
    (lo := (25565323 / 100000000)) (hi := (255653231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5165219459663 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5165219459663 / 4000000000000) = 1/(62500000000 / 5165219459663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (441453631 / 100000000) (4414536317 / 1000000000) (Real.log (5165219459663 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5165219459663 / 62500000000) = -Real.log (62500000000 / 5165219459663) := by
    rw [show ((5165219459663 / 62500000000) : ℝ) = ((62500000000 / 5165219459663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2201229841 / 500000000) ≤ -Real.log (500000000000 / 40825729399123) ∧
    -Real.log (500000000000 / 40825729399123) ≤ (4402459689 / 1000000000) := by
  have h := checkLog_sound (w := (8825729399123 / 72825729399123)) (n := 12)
    (lo := (121788301 / 500000000)) (hi := (243576603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40825729399123 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40825729399123 / 32000000000000) = 1/(500000000000 / 40825729399123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2201229841 / 500000000) (4402459689 / 1000000000) (Real.log (40825729399123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40825729399123 / 500000000000) = -Real.log (500000000000 / 40825729399123) := by
    rw [show ((40825729399123 / 500000000000) : ℝ) = ((500000000000 / 40825729399123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (13777487 / 3125000) ≤ -Real.log (250000000000 / 20542614463343) ∧
    -Real.log (250000000000 / 20542614463343) ≤ (4408795847 / 1000000000) := by
  have h := checkLog_sound (w := (4542614463343 / 36542614463343)) (n := 12)
    (lo := (6247819 / 25000000)) (hi := (249912761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20542614463343 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20542614463343 / 16000000000000) = 1/(250000000000 / 20542614463343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (13777487 / 3125000) (4408795847 / 1000000000) (Real.log (20542614463343 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20542614463343 / 250000000000) = -Real.log (250000000000 / 20542614463343) := by
    rw [show ((20542614463343 / 250000000000) : ℝ) = ((250000000000 / 20542614463343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053
