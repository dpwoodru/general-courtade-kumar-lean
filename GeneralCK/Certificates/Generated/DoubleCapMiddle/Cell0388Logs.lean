import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0388
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

theorem reflection_log_1_neg : (20310027 / 100000000) ≤ -Real.log (5120 / 6273) ∧
    -Real.log (5120 / 6273) ≤ (203100271 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 11393)) (n := 12)
    (lo := (20310027 / 100000000)) (hi := (203100271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6273 / 5120) = 1/(5120 / 6273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20310027 / 100000000) (203100271 / 1000000000) (Real.log (6273 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6273 / 5120) = -Real.log (5120 / 6273) := by
    rw [show ((6273 / 5120) : ℝ) = ((5120 / 6273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (255144297 / 1000000000) ≤ -Real.log (3967 / 5120) ∧
    -Real.log (3967 / 5120) ≤ (127572149 / 500000000) := by
  have h := checkLog_sound (w := (1153 / 9087)) (n := 12)
    (lo := (255144297 / 1000000000)) (hi := (127572149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3967) = 1/(3967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127572149 / 500000000) (-255144297 / 1000000000) (Real.log (3967 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (202861121 / 1000000000) ≤ -Real.log (10240 / 12543) ∧
    -Real.log (10240 / 12543) ≤ (101430561 / 500000000) := by
  have h := checkLog_sound (w := (2303 / 22783)) (n := 12)
    (lo := (202861121 / 1000000000)) (hi := (101430561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12543 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12543 / 10240) = 1/(10240 / 12543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (202861121 / 1000000000) (101430561 / 500000000) (Real.log (12543 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12543 / 10240) = -Real.log (10240 / 12543) := by
    rw [show ((12543 / 10240) : ℝ) = ((10240 / 12543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (254766249 / 1000000000) ≤ -Real.log (7937 / 10240) ∧
    -Real.log (7937 / 10240) ≤ (203813 / 800000) := by
  have h := checkLog_sound (w := (2303 / 18177)) (n := 12)
    (lo := (254766249 / 1000000000)) (hi := (203813 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7937) = 1/(7937 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-203813 / 800000) (-254766249 / 1000000000) (Real.log (7937 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (92958229 / 250000000) ≤ -Real.log (2560 / 3713) ∧
    -Real.log (2560 / 3713) ≤ (371832917 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 6273)) (n := 12)
    (lo := (92958229 / 250000000)) (hi := (371832917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3713 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3713 / 2560) = 1/(2560 / 3713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (92958229 / 250000000) (371832917 / 1000000000) (Real.log (3713 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3713 / 2560) = -Real.log (2560 / 3713) := by
    rw [show ((3713 / 2560) : ℝ) = ((2560 / 3713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14963687 / 25000000) ≤ -Real.log (1407 / 2560) ∧
    -Real.log (1407 / 2560) ≤ (598547481 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 3967)) (n := 12)
    (lo := (14963687 / 25000000)) (hi := (598547481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1407) = 1/(1407 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-598547481 / 1000000000) (-14963687 / 25000000) (Real.log (1407 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (371428849 / 1000000000) ≤ -Real.log (5120 / 7423) ∧
    -Real.log (5120 / 7423) ≤ (7428577 / 20000000) := by
  have h := checkLog_sound (w := (2303 / 12543)) (n := 12)
    (lo := (371428849 / 1000000000)) (hi := (7428577 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7423 / 5120) = 1/(5120 / 7423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (371428849 / 1000000000) (7428577 / 20000000) (Real.log (7423 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7423 / 5120) = -Real.log (5120 / 7423) := by
    rw [show ((7423 / 5120) : ℝ) = ((5120 / 7423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11949639 / 20000000) ≤ -Real.log (2817 / 5120) ∧
    -Real.log (2817 / 5120) ≤ (597481951 / 1000000000) := by
  have h := checkLog_sound (w := (2303 / 7937)) (n := 12)
    (lo := (11949639 / 20000000)) (hi := (597481951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2817) = 1/(2817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-597481951 / 1000000000) (-11949639 / 20000000) (Real.log (2817 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139191863 / 500000000) ≤ -Real.log (1000000 / 1320993) ∧
    -Real.log (1000000 / 1320993) ≤ (278383727 / 1000000000) := by
  have h := checkLog_sound (w := (320993 / 2320993)) (n := 12)
    (lo := (139191863 / 500000000)) (hi := (278383727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320993 / 1000000) = 1/(1000000 / 1320993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139191863 / 500000000) (278383727 / 1000000000) (Real.log (1320993 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1320993 / 1000000) = -Real.log (1000000 / 1320993) := by
    rw [show ((1320993 / 1000000) : ℝ) = ((1000000 / 1320993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193561921 / 500000000) ≤ -Real.log (679007 / 1000000) ∧
    -Real.log (679007 / 1000000) ≤ (387123843 / 1000000000) := by
  have h := checkLog_sound (w := (320993 / 1679007)) (n := 12)
    (lo := (193561921 / 500000000)) (hi := (387123843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679007) = 1/(679007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-387123843 / 1000000000) (-193561921 / 500000000) (Real.log (679007 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34838459 / 125000000) ≤ -Real.log (1000000 / 1321421) ∧
    -Real.log (1000000 / 1321421) ≤ (278707673 / 1000000000) := by
  have h := checkLog_sound (w := (321421 / 2321421)) (n := 12)
    (lo := (34838459 / 125000000)) (hi := (278707673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321421 / 1000000) = 1/(1000000 / 1321421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34838459 / 125000000) (278707673 / 1000000000) (Real.log (1321421 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1321421 / 1000000) = -Real.log (1000000 / 1321421) := by
    rw [show ((1321421 / 1000000) : ℝ) = ((1000000 / 1321421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (387754373 / 1000000000) ≤ -Real.log (678579 / 1000000) ∧
    -Real.log (678579 / 1000000) ≤ (193877187 / 500000000) := by
  have h := checkLog_sound (w := (321421 / 1678579)) (n := 12)
    (lo := (387754373 / 1000000000)) (hi := (193877187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678579) = 1/(678579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193877187 / 500000000) (-387754373 / 1000000000) (Real.log (678579 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52492287 / 250000000) ≤ -Real.log (25000 / 30841) ∧
    -Real.log (25000 / 30841) ≤ (209969149 / 1000000000) := by
  have h := checkLog_sound (w := (5841 / 55841)) (n := 12)
    (lo := (52492287 / 250000000)) (hi := (209969149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30841 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30841 / 25000) = 1/(25000 / 30841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52492287 / 250000000) (209969149 / 1000000000) (Real.log (30841 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30841 / 25000) = -Real.log (25000 / 30841) := by
    rw [show ((30841 / 25000) : ℝ) = ((25000 / 30841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (53220649 / 200000000) ≤ -Real.log (19159 / 25000) ∧
    -Real.log (19159 / 25000) ≤ (133051623 / 500000000) := by
  have h := checkLog_sound (w := (5841 / 44159)) (n := 12)
    (lo := (53220649 / 200000000)) (hi := (133051623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19159) = 1/(19159 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-133051623 / 500000000) (-53220649 / 200000000) (Real.log (19159 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (105118307 / 500000000) ≤ -Real.log (100000 / 123397) ∧
    -Real.log (100000 / 123397) ≤ (42047323 / 200000000) := by
  have h := checkLog_sound (w := (23397 / 223397)) (n := 12)
    (lo := (105118307 / 500000000)) (hi := (42047323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123397 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123397 / 100000) = 1/(100000 / 123397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105118307 / 500000000) (42047323 / 200000000) (Real.log (123397 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123397 / 100000) = -Real.log (100000 / 123397) := by
    rw [show ((123397 / 100000) : ℝ) = ((100000 / 123397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53306789 / 200000000) ≤ -Real.log (76603 / 100000) ∧
    -Real.log (76603 / 100000) ≤ (133266973 / 500000000) := by
  have h := checkLog_sound (w := (23397 / 176603)) (n := 12)
    (lo := (53306789 / 200000000)) (hi := (133266973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76603) = 1/(76603 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-133266973 / 500000000) (-53306789 / 200000000) (Real.log (76603 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (41594223 / 62500000) ≤ -Real.log (250000000000 / 486369433599) ∧
    -Real.log (250000000000 / 486369433599) ≤ (665507569 / 1000000000) := by
  have h := checkLog_sound (w := (236369433599 / 736369433599)) (n := 12)
    (lo := (41594223 / 62500000)) (hi := (665507569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486369433599 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486369433599 / 250000000000) = 1/(250000000000 / 486369433599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (41594223 / 62500000) (665507569 / 1000000000) (Real.log (486369433599 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (486369433599 / 250000000000) = -Real.log (250000000000 / 486369433599) := by
    rw [show ((486369433599 / 250000000000) : ℝ) = ((250000000000 / 486369433599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133292409 / 200000000) ≤ -Real.log (500000000000 / 973667767497) ∧
    -Real.log (500000000000 / 973667767497) ≤ (333231023 / 500000000) := by
  have h := checkLog_sound (w := (473667767497 / 1473667767497)) (n := 12)
    (lo := (133292409 / 200000000)) (hi := (333231023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973667767497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973667767497 / 500000000000) = 1/(500000000000 / 973667767497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133292409 / 200000000) (333231023 / 500000000) (Real.log (973667767497 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (973667767497 / 500000000000) = -Real.log (500000000000 / 973667767497) := by
    rw [show ((973667767497 / 500000000000) : ℝ) = ((500000000000 / 973667767497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (238036197 / 500000000) ≤ -Real.log (125000000000 / 201217443499) ∧
    -Real.log (125000000000 / 201217443499) ≤ (95214479 / 200000000) := by
  have h := checkLog_sound (w := (76217443499 / 326217443499)) (n := 12)
    (lo := (238036197 / 500000000)) (hi := (95214479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201217443499 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201217443499 / 125000000000) = 1/(125000000000 / 201217443499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (238036197 / 500000000) (95214479 / 200000000) (Real.log (201217443499 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (201217443499 / 125000000000) = -Real.log (125000000000 / 201217443499) := by
    rw [show ((201217443499 / 125000000000) : ℝ) = ((125000000000 / 201217443499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (476770559 / 1000000000) ≤ -Real.log (100000000000 / 161086380429) ∧
    -Real.log (100000000000 / 161086380429) ≤ (372477 / 781250) := by
  have h := checkLog_sound (w := (61086380429 / 261086380429)) (n := 12)
    (lo := (476770559 / 1000000000)) (hi := (372477 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161086380429 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161086380429 / 100000000000) = 1/(100000000000 / 161086380429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (476770559 / 1000000000) (372477 / 781250) (Real.log (161086380429 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161086380429 / 100000000000) = -Real.log (100000000000 / 161086380429) := by
    rw [show ((161086380429 / 100000000000) : ℝ) = ((100000000000 / 161086380429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0388
