import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054
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

theorem reflection_log_1_neg : (678682721 / 1000000000) ≤ -Real.log (102400 / 201859) ∧
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


theorem reflection_log_1 : Bounds (678682721 / 1000000000) (339341361 / 500000000) (Real.log (201859 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201859 / 102400) = -Real.log (102400 / 201859) := by
    rw [show ((201859 / 102400) : ℝ) = ((102400 / 201859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71002741 / 20000000) ≤ -Real.log (2941 / 102400) ∧
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


theorem reflection_log_2 : Bounds (-110941783 / 31250000) (-71002741 / 20000000) (Real.log (2941 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678588591 / 1000000000) ≤ -Real.log (1280 / 2523) ∧
    -Real.log (1280 / 2523) ≤ (42411787 / 62500000) := by
  have h := checkLog_sound (w := (1243 / 3803)) (n := 12)
    (lo := (678588591 / 1000000000)) (hi := (42411787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 1280) = 1/(1280 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678588591 / 1000000000) (42411787 / 62500000) (Real.log (2523 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2523 / 1280) = -Real.log (1280 / 2523) := by
    rw [show ((2523 / 1280) : ℝ) = ((1280 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3543697441 / 1000000000) ≤ -Real.log (37 / 1280) ∧
    -Real.log (37 / 1280) ≤ (3543697447 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 37) = 1/(37 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3543697447 / 1000000000) (-3543697441 / 1000000000) (Real.log (37 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332002983 / 500000000) ≤ -Real.log (51200 / 99459) ∧
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


theorem reflection_log_5 : Bounds (332002983 / 500000000) (664005967 / 1000000000) (Real.log (99459 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99459 / 51200) = -Real.log (51200 / 99459) := by
    rw [show ((99459 / 51200) : ℝ) = ((51200 / 99459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (285698987 / 100000000) ≤ -Real.log (2941 / 51200) ∧
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


theorem reflection_log_6 : Bounds (-22855919 / 8000000) (-285698987 / 100000000) (Real.log (2941 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132762983 / 200000000) ≤ -Real.log (640 / 1243) ∧
    -Real.log (640 / 1243) ≤ (165953729 / 250000000) := by
  have h := checkLog_sound (w := (603 / 1883)) (n := 12)
    (lo := (132762983 / 200000000)) (hi := (165953729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 640) = 1/(640 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132762983 / 200000000) (165953729 / 250000000) (Real.log (1243 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1243 / 640) = -Real.log (640 / 1243) := by
    rw [show ((1243 / 640) : ℝ) = ((640 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2850550261 / 1000000000) ≤ -Real.log (37 / 640) ∧
    -Real.log (37 / 640) ≤ (1425275133 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 37) = 1/(37 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1425275133 / 500000000) (-2850550261 / 1000000000) (Real.log (37 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68096933 / 100000000) ≤ -Real.log (62500 / 123487) ∧
    -Real.log (62500 / 123487) ≤ (680969331 / 1000000000) := by
  have h := checkLog_sound (w := (60987 / 185987)) (n := 12)
    (lo := (68096933 / 100000000)) (hi := (680969331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123487 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123487 / 62500) = 1/(62500 / 123487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68096933 / 100000000) (680969331 / 1000000000) (Real.log (123487 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123487 / 62500) = -Real.log (62500 / 123487) := by
    rw [show ((123487 / 62500) : ℝ) = ((62500 / 123487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3721072119 / 1000000000) ≤ -Real.log (1513 / 62500) ∧
    -Real.log (1513 / 62500) ≤ (29768577 / 8000000) := by
  have h := checkLog_sound (w := (3521 / 27729)) (n := 12)
    (lo := (255336219 / 1000000000)) (hi := (12766811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12104) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12104) = 1/(1513 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-29768577 / 8000000) (-3721072119 / 1000000000) (Real.log (1513 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34052237 / 50000000) ≤ -Real.log (1000000 / 1975941) ∧
    -Real.log (1000000 / 1975941) ≤ (681044741 / 1000000000) := by
  have h := checkLog_sound (w := (975941 / 2975941)) (n := 12)
    (lo := (34052237 / 50000000)) (hi := (681044741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975941 / 1000000) = 1/(1000000 / 1975941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34052237 / 50000000) (681044741 / 1000000000) (Real.log (1975941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975941 / 1000000) = -Real.log (1000000 / 1975941) := by
    rw [show ((1975941 / 1000000) : ℝ) = ((1000000 / 1975941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3727246129 / 1000000000) ≤ -Real.log (24059 / 1000000) ∧
    -Real.log (24059 / 1000000) ≤ (745449227 / 200000000) := by
  have h := checkLog_sound (w := (7191 / 55309)) (n := 12)
    (lo := (261510229 / 1000000000)) (hi := (26151023 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24059) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24059) = 1/(24059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-745449227 / 200000000) (-3727246129 / 1000000000) (Real.log (24059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68089847 / 100000000) ≤ -Real.log (250000 / 493913) ∧
    -Real.log (250000 / 493913) ≤ (680898471 / 1000000000) := by
  have h := checkLog_sound (w := (243913 / 743913)) (n := 12)
    (lo := (68089847 / 100000000)) (hi := (680898471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493913 / 250000) = 1/(250000 / 493913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68089847 / 100000000) (680898471 / 1000000000) (Real.log (493913 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493913 / 250000) = -Real.log (250000 / 493913) := by
    rw [show ((493913 / 250000) : ℝ) = ((250000 / 493913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (743061113 / 200000000) ≤ -Real.log (6087 / 250000) ∧
    -Real.log (6087 / 250000) ≤ (3715305571 / 1000000000) := by
  have h := checkLog_sound (w := (3451 / 27799)) (n := 12)
    (lo := (49913933 / 200000000)) (hi := (124784833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12174) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12174) = 1/(6087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3715305571 / 1000000000) (-743061113 / 200000000) (Real.log (6087 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680974897 / 1000000000) ≤ -Real.log (1000000 / 1975803) ∧
    -Real.log (1000000 / 1975803) ≤ (680974899 / 1000000000) := by
  have h := checkLog_sound (w := (975803 / 2975803)) (n := 12)
    (lo := (680974897 / 1000000000)) (hi := (680974899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975803 / 1000000) = 1/(1000000 / 1975803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680974897 / 1000000000) (680974899 / 1000000000) (Real.log (1975803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975803 / 1000000) = -Real.log (1000000 / 1975803) := by
    rw [show ((1975803 / 1000000) : ℝ) = ((1000000 / 1975803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3721526617 / 1000000000) ≤ -Real.log (24197 / 1000000) ∧
    -Real.log (24197 / 1000000) ≤ (3721526623 / 1000000000) := by
  have h := checkLog_sound (w := (7053 / 55447)) (n := 12)
    (lo := (255790717 / 1000000000)) (hi := (127895359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24197) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24197) = 1/(24197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3721526623 / 1000000000) (-3721526617 / 1000000000) (Real.log (24197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4402041449 / 1000000000) ≤ -Real.log (250000000000 / 20404329147389) ∧
    -Real.log (250000000000 / 20404329147389) ≤ (275127591 / 62500000) := by
  have h := checkLog_sound (w := (4404329147389 / 36404329147389)) (n := 12)
    (lo := (243158369 / 1000000000)) (hi := (24315837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20404329147389 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20404329147389 / 16000000000000) = 1/(250000000000 / 20404329147389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4402041449 / 1000000000) (275127591 / 62500000) (Real.log (20404329147389 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20404329147389 / 250000000000) = -Real.log (250000000000 / 20404329147389) := by
    rw [show ((20404329147389 / 250000000000) : ℝ) = ((250000000000 / 20404329147389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4408290869 / 1000000000) ≤ -Real.log (10000000000 / 821289746041) ∧
    -Real.log (10000000000 / 821289746041) ≤ (1102072719 / 250000000) := by
  have h := checkLog_sound (w := (181289746041 / 1461289746041)) (n := 12)
    (lo := (249407789 / 1000000000)) (hi := (24940779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821289746041 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(821289746041 / 640000000000) = 1/(10000000000 / 821289746041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4408290869 / 1000000000) (1102072719 / 250000000) (Real.log (821289746041 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (821289746041 / 10000000000) = -Real.log (10000000000 / 821289746041) := by
    rw [show ((821289746041 / 10000000000) : ℝ) = ((10000000000 / 821289746041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (879240807 / 200000000) ≤ -Real.log (500000000000 / 40571135206177) ∧
    -Real.log (500000000000 / 40571135206177) ≤ (2198102021 / 500000000) := by
  have h := checkLog_sound (w := (8571135206177 / 72571135206177)) (n := 12)
    (lo := (47464191 / 200000000)) (hi := (59330239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40571135206177 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40571135206177 / 32000000000000) = 1/(500000000000 / 40571135206177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (879240807 / 200000000) (2198102021 / 500000000) (Real.log (40571135206177 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40571135206177 / 500000000000) = -Real.log (500000000000 / 40571135206177) := by
    rw [show ((40571135206177 / 500000000000) : ℝ) = ((500000000000 / 40571135206177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (880500303 / 200000000) ≤ -Real.log (250000000000 / 20413718642807) ∧
    -Real.log (250000000000 / 20413718642807) ≤ (2201250761 / 500000000) := by
  have h := checkLog_sound (w := (4413718642807 / 36413718642807)) (n := 12)
    (lo := (48723687 / 200000000)) (hi := (60904609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20413718642807 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20413718642807 / 16000000000000) = 1/(250000000000 / 20413718642807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (880500303 / 200000000) (2201250761 / 500000000) (Real.log (20413718642807 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20413718642807 / 250000000000) = -Real.log (250000000000 / 20413718642807) := by
    rw [show ((20413718642807 / 250000000000) : ℝ) = ((250000000000 / 20413718642807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054
