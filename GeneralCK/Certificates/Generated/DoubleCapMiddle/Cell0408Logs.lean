import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0408
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

theorem reflection_log_1_neg : (198306397 / 1000000000) ≤ -Real.log (5120 / 6243) ∧
    -Real.log (5120 / 6243) ≤ (99153199 / 500000000) := by
  have h := checkLog_sound (w := (1123 / 11363)) (n := 12)
    (lo := (198306397 / 1000000000)) (hi := (99153199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6243 / 5120) = 1/(5120 / 6243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198306397 / 1000000000) (99153199 / 500000000) (Real.log (6243 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6243 / 5120) = -Real.log (5120 / 6243) := by
    rw [show ((6243 / 5120) : ℝ) = ((5120 / 6243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (247610359 / 1000000000) ≤ -Real.log (3997 / 5120) ∧
    -Real.log (3997 / 5120) ≤ (6190259 / 25000000) := by
  have h := checkLog_sound (w := (1123 / 9117)) (n := 12)
    (lo := (247610359 / 1000000000)) (hi := (6190259 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3997) = 1/(3997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6190259 / 25000000) (-247610359 / 1000000000) (Real.log (3997 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198066099 / 1000000000) ≤ -Real.log (10240 / 12483) ∧
    -Real.log (10240 / 12483) ≤ (1980661 / 10000000) := by
  have h := checkLog_sound (w := (2243 / 22723)) (n := 12)
    (lo := (198066099 / 1000000000)) (hi := (1980661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12483 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12483 / 10240) = 1/(10240 / 12483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198066099 / 1000000000) (1980661 / 10000000) (Real.log (12483 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12483 / 10240) = -Real.log (10240 / 12483) := by
    rw [show ((12483 / 10240) : ℝ) = ((10240 / 12483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (61808787 / 250000000) ≤ -Real.log (7997 / 10240) ∧
    -Real.log (7997 / 10240) ≤ (247235149 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 18237)) (n := 12)
    (lo := (61808787 / 250000000)) (hi := (247235149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7997) = 1/(7997 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-247235149 / 1000000000) (-61808787 / 250000000) (Real.log (7997 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (181860189 / 500000000) ≤ -Real.log (2560 / 3683) ∧
    -Real.log (2560 / 3683) ≤ (363720379 / 1000000000) := by
  have h := checkLog_sound (w := (1123 / 6243)) (n := 12)
    (lo := (181860189 / 500000000)) (hi := (363720379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3683 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3683 / 2560) = 1/(2560 / 3683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (181860189 / 500000000) (363720379 / 1000000000) (Real.log (3683 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3683 / 2560) = -Real.log (2560 / 3683) := by
    rw [show ((3683 / 2560) : ℝ) = ((2560 / 3683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (577449651 / 1000000000) ≤ -Real.log (1437 / 2560) ∧
    -Real.log (1437 / 2560) ≤ (144362413 / 250000000) := by
  have h := checkLog_sound (w := (1123 / 3997)) (n := 12)
    (lo := (577449651 / 1000000000)) (hi := (144362413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1437) = 1/(1437 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-144362413 / 250000000) (-577449651 / 1000000000) (Real.log (1437 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (363313019 / 1000000000) ≤ -Real.log (5120 / 7363) ∧
    -Real.log (5120 / 7363) ≤ (18165651 / 50000000) := by
  have h := checkLog_sound (w := (2243 / 12483)) (n := 12)
    (lo := (363313019 / 1000000000)) (hi := (18165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7363 / 5120) = 1/(5120 / 7363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (363313019 / 1000000000) (18165651 / 50000000) (Real.log (7363 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7363 / 5120) = -Real.log (5120 / 7363) := by
    rw [show ((7363 / 5120) : ℝ) = ((5120 / 7363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (288203177 / 500000000) ≤ -Real.log (2877 / 5120) ∧
    -Real.log (2877 / 5120) ≤ (115281271 / 200000000) := by
  have h := checkLog_sound (w := (2243 / 7997)) (n := 12)
    (lo := (288203177 / 500000000)) (hi := (115281271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2877) = 1/(2877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115281271 / 200000000) (-288203177 / 500000000) (Real.log (2877 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135955429 / 500000000) ≤ -Real.log (100000 / 131247) ∧
    -Real.log (100000 / 131247) ≤ (271910859 / 1000000000) := by
  have h := checkLog_sound (w := (31247 / 231247)) (n := 12)
    (lo := (135955429 / 500000000)) (hi := (271910859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131247 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131247 / 100000) = 1/(100000 / 131247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135955429 / 500000000) (271910859 / 1000000000) (Real.log (131247 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (131247 / 100000) = -Real.log (100000 / 131247) := by
    rw [show ((131247 / 100000) : ℝ) = ((100000 / 131247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187324907 / 500000000) ≤ -Real.log (68753 / 100000) ∧
    -Real.log (68753 / 100000) ≤ (74929963 / 200000000) := by
  have h := checkLog_sound (w := (31247 / 168753)) (n := 12)
    (lo := (187324907 / 500000000)) (hi := (74929963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68753) = 1/(68753 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-74929963 / 200000000) (-187324907 / 500000000) (Real.log (68753 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (54447229 / 200000000) ≤ -Real.log (1000000 / 1312897) ∧
    -Real.log (1000000 / 1312897) ≤ (136118073 / 500000000) := by
  have h := checkLog_sound (w := (312897 / 2312897)) (n := 12)
    (lo := (54447229 / 200000000)) (hi := (136118073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312897 / 1000000) = 1/(1000000 / 1312897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (54447229 / 200000000) (136118073 / 500000000) (Real.log (1312897 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1312897 / 1000000) = -Real.log (1000000 / 1312897) := by
    rw [show ((1312897 / 1000000) : ℝ) = ((1000000 / 1312897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37527107 / 100000000) ≤ -Real.log (687103 / 1000000) ∧
    -Real.log (687103 / 1000000) ≤ (375271071 / 1000000000) := by
  have h := checkLog_sound (w := (312897 / 1687103)) (n := 12)
    (lo := (37527107 / 100000000)) (hi := (375271071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687103) = 1/(687103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-375271071 / 1000000000) (-37527107 / 100000000) (Real.log (687103 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102321941 / 500000000) ≤ -Real.log (62500 / 76693) ∧
    -Real.log (62500 / 76693) ≤ (204643883 / 1000000000) := by
  have h := checkLog_sound (w := (14193 / 139193)) (n := 12)
    (lo := (102321941 / 500000000)) (hi := (204643883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76693 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76693 / 62500) = 1/(62500 / 76693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102321941 / 500000000) (204643883 / 1000000000) (Real.log (76693 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (76693 / 62500) = -Real.log (62500 / 76693) := by
    rw [show ((76693 / 62500) : ℝ) = ((62500 / 76693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257590079 / 1000000000) ≤ -Real.log (48307 / 62500) ∧
    -Real.log (48307 / 62500) ≤ (804969 / 3125000) := by
  have h := checkLog_sound (w := (14193 / 110807)) (n := 12)
    (lo := (257590079 / 1000000000)) (hi := (804969 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48307) = 1/(48307 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-804969 / 3125000) (-257590079 / 1000000000) (Real.log (48307 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204910331 / 1000000000) ≤ -Real.log (200000 / 245483) ∧
    -Real.log (200000 / 245483) ≤ (51227583 / 250000000) := by
  have h := checkLog_sound (w := (45483 / 445483)) (n := 12)
    (lo := (204910331 / 1000000000)) (hi := (51227583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245483 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245483 / 200000) = 1/(200000 / 245483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204910331 / 1000000000) (51227583 / 250000000) (Real.log (245483 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (245483 / 200000) = -Real.log (200000 / 245483) := by
    rw [show ((245483 / 200000) : ℝ) = ((200000 / 245483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258013243 / 1000000000) ≤ -Real.log (154517 / 200000) ∧
    -Real.log (154517 / 200000) ≤ (64503311 / 250000000) := by
  have h := checkLog_sound (w := (45483 / 354517)) (n := 12)
    (lo := (258013243 / 1000000000)) (hi := (64503311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154517) = 1/(154517 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64503311 / 250000000) (-258013243 / 1000000000) (Real.log (154517 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (20205021 / 31250000) ≤ -Real.log (1562500000 / 2982756207) ∧
    -Real.log (1562500000 / 2982756207) ≤ (646560673 / 1000000000) := by
  have h := checkLog_sound (w := (1420256207 / 4545256207)) (n := 12)
    (lo := (20205021 / 31250000)) (hi := (646560673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2982756207 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2982756207 / 1562500000) = 1/(1562500000 / 2982756207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (20205021 / 31250000) (646560673 / 1000000000) (Real.log (2982756207 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2982756207 / 1562500000) = -Real.log (1562500000 / 2982756207) := by
    rw [show ((2982756207 / 1562500000) : ℝ) = ((1562500000 / 2982756207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40469201 / 62500000) ≤ -Real.log (250000000000 / 477692936867) ∧
    -Real.log (250000000000 / 477692936867) ≤ (647507217 / 1000000000) := by
  have h := checkLog_sound (w := (227692936867 / 727692936867)) (n := 12)
    (lo := (40469201 / 62500000)) (hi := (647507217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477692936867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477692936867 / 250000000000) = 1/(250000000000 / 477692936867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40469201 / 62500000) (647507217 / 1000000000) (Real.log (477692936867 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (477692936867 / 250000000000) = -Real.log (250000000000 / 477692936867) := by
    rw [show ((477692936867 / 250000000000) : ℝ) = ((250000000000 / 477692936867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (462233961 / 1000000000) ≤ -Real.log (125000000000 / 198452087689) ∧
    -Real.log (125000000000 / 198452087689) ≤ (231116981 / 500000000) := by
  have h := checkLog_sound (w := (73452087689 / 323452087689)) (n := 12)
    (lo := (462233961 / 1000000000)) (hi := (231116981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198452087689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198452087689 / 125000000000) = 1/(125000000000 / 198452087689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (462233961 / 1000000000) (231116981 / 500000000) (Real.log (198452087689 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198452087689 / 125000000000) = -Real.log (125000000000 / 198452087689) := by
    rw [show ((198452087689 / 125000000000) : ℝ) = ((125000000000 / 198452087689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18516943 / 40000000) ≤ -Real.log (500000000000 / 794355960833) ∧
    -Real.log (500000000000 / 794355960833) ≤ (57865447 / 125000000) := by
  have h := checkLog_sound (w := (294355960833 / 1294355960833)) (n := 12)
    (lo := (18516943 / 40000000)) (hi := (57865447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794355960833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794355960833 / 500000000000) = 1/(500000000000 / 794355960833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18516943 / 40000000) (57865447 / 125000000) (Real.log (794355960833 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (794355960833 / 500000000000) = -Real.log (500000000000 / 794355960833) := by
    rw [show ((794355960833 / 500000000000) : ℝ) = ((500000000000 / 794355960833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0408
