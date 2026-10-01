import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0175
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

theorem reflection_log_1_neg : (276832411 / 1000000000) ≤ -Real.log (5120 / 6753) ∧
    -Real.log (5120 / 6753) ≤ (69208103 / 250000000) := by
  have h := checkLog_sound (w := (1633 / 11873)) (n := 12)
    (lo := (276832411 / 1000000000)) (hi := (69208103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6753 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6753 / 5120) = 1/(5120 / 6753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (276832411 / 1000000000) (69208103 / 250000000) (Real.log (6753 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6753 / 5120) = -Real.log (5120 / 6753) := by
    rw [show ((6753 / 5120) : ℝ) = ((5120 / 6753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (384112671 / 1000000000) ≤ -Real.log (3487 / 5120) ∧
    -Real.log (3487 / 5120) ≤ (12003521 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 8607)) (n := 12)
    (lo := (384112671 / 1000000000)) (hi := (12003521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3487) = 1/(3487 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12003521 / 31250000) (-384112671 / 1000000000) (Real.log (3487 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55277613 / 200000000) ≤ -Real.log (512 / 675) ∧
    -Real.log (512 / 675) ≤ (138194033 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1187)) (n := 12)
    (lo := (55277613 / 200000000)) (hi := (138194033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675 / 512) = 1/(512 / 675) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55277613 / 200000000) (138194033 / 500000000) (Real.log (675 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (675 / 512) = -Real.log (512 / 675) := by
    rw [show ((675 / 512) : ℝ) = ((512 / 675) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (191626351 / 500000000) ≤ -Real.log (349 / 512) ∧
    -Real.log (349 / 512) ≤ (383252703 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 861)) (n := 12)
    (lo := (191626351 / 500000000)) (hi := (383252703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 349) = 1/(349 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-383252703 / 1000000000) (-191626351 / 500000000) (Real.log (349 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (493409209 / 1000000000) ≤ -Real.log (2560 / 4193) ∧
    -Real.log (2560 / 4193) ≤ (49340921 / 100000000) := by
  have h := checkLog_sound (w := (1633 / 6753)) (n := 12)
    (lo := (493409209 / 1000000000)) (hi := (49340921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4193 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4193 / 2560) = 1/(2560 / 4193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (493409209 / 1000000000) (49340921 / 100000000) (Real.log (4193 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4193 / 2560) = -Real.log (2560 / 4193) := by
    rw [show ((4193 / 2560) : ℝ) = ((2560 / 4193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1015808971 / 1000000000) ≤ -Real.log (927 / 2560) ∧
    -Real.log (927 / 2560) ≤ (1015808973 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 927) = 1/(927 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1015808973 / 1000000000) (-1015808971 / 1000000000) (Real.log (927 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19707739 / 40000000) ≤ -Real.log (256 / 419) ∧
    -Real.log (256 / 419) ≤ (123173369 / 250000000) := by
  have h := checkLog_sound (w := (163 / 675)) (n := 12)
    (lo := (19707739 / 40000000)) (hi := (123173369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419 / 256) = 1/(256 / 419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19707739 / 40000000) (123173369 / 250000000) (Real.log (419 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (419 / 256) = -Real.log (256 / 419) := by
    rw [show ((419 / 256) : ℝ) = ((256 / 419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20251559 / 20000000) ≤ -Real.log (93 / 256) ∧
    -Real.log (93 / 256) ≤ (31643061 / 31250000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 93) = 1/(93 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31643061 / 31250000) (-20251559 / 20000000) (Real.log (93 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75618097 / 200000000) ≤ -Real.log (200000 / 291899) ∧
    -Real.log (200000 / 291899) ≤ (189045243 / 500000000) := by
  have h := checkLog_sound (w := (91899 / 491899)) (n := 12)
    (lo := (75618097 / 200000000)) (hi := (189045243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291899 / 200000) = 1/(200000 / 291899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75618097 / 200000000) (189045243 / 500000000) (Real.log (291899 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (291899 / 200000) = -Real.log (200000 / 291899) := by
    rw [show ((291899 / 200000) : ℝ) = ((200000 / 291899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (615251391 / 1000000000) ≤ -Real.log (108101 / 200000) ∧
    -Real.log (108101 / 200000) ≤ (9613303 / 15625000) := by
  have h := checkLog_sound (w := (91899 / 308101)) (n := 12)
    (lo := (615251391 / 1000000000)) (hi := (9613303 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 108101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 108101) = 1/(108101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9613303 / 15625000) (-615251391 / 1000000000) (Real.log (108101 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (189349707 / 500000000) ≤ -Real.log (31250 / 45637) ∧
    -Real.log (31250 / 45637) ≤ (75739883 / 200000000) := by
  have h := checkLog_sound (w := (14387 / 76887)) (n := 12)
    (lo := (189349707 / 500000000)) (hi := (75739883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45637 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45637 / 31250) = 1/(31250 / 45637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (189349707 / 500000000) (75739883 / 200000000) (Real.log (45637 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (45637 / 31250) = -Real.log (31250 / 45637) := by
    rw [show ((45637 / 31250) : ℝ) = ((31250 / 45637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (616897503 / 1000000000) ≤ -Real.log (16863 / 31250) ∧
    -Real.log (16863 / 31250) ≤ (19278047 / 31250000) := by
  have h := checkLog_sound (w := (14387 / 48113)) (n := 12)
    (lo := (616897503 / 1000000000)) (hi := (19278047 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 16863) = 1/(16863 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19278047 / 31250000) (-616897503 / 1000000000) (Real.log (16863 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1482063 / 5000000) ≤ -Real.log (40000 / 53801) ∧
    -Real.log (40000 / 53801) ≤ (296412601 / 1000000000) := by
  have h := checkLog_sound (w := (13801 / 93801)) (n := 12)
    (lo := (1482063 / 5000000)) (hi := (296412601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53801 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53801 / 40000) = 1/(40000 / 53801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1482063 / 5000000) (296412601 / 1000000000) (Real.log (53801 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53801 / 40000) = -Real.log (40000 / 53801) := by
    rw [show ((53801 / 40000) : ℝ) = ((40000 / 53801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (105789553 / 250000000) ≤ -Real.log (26199 / 40000) ∧
    -Real.log (26199 / 40000) ≤ (423158213 / 1000000000) := by
  have h := checkLog_sound (w := (13801 / 66199)) (n := 12)
    (lo := (105789553 / 250000000)) (hi := (423158213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26199) = 1/(26199 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-423158213 / 1000000000) (-105789553 / 250000000) (Real.log (26199 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59394011 / 200000000) ≤ -Real.log (40000 / 53831) ∧
    -Real.log (40000 / 53831) ≤ (37121257 / 125000000) := by
  have h := checkLog_sound (w := (13831 / 93831)) (n := 12)
    (lo := (59394011 / 200000000)) (hi := (37121257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53831 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53831 / 40000) = 1/(40000 / 53831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59394011 / 200000000) (37121257 / 125000000) (Real.log (53831 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53831 / 40000) = -Real.log (40000 / 53831) := by
    rw [show ((53831 / 40000) : ℝ) = ((40000 / 53831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (424303949 / 1000000000) ≤ -Real.log (26169 / 40000) ∧
    -Real.log (26169 / 40000) ≤ (8486079 / 20000000) := by
  have h := checkLog_sound (w := (13831 / 66169)) (n := 12)
    (lo := (424303949 / 1000000000)) (hi := (8486079 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26169) = 1/(26169 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-8486079 / 20000000) (-424303949 / 1000000000) (Real.log (26169 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (248335469 / 250000000) ≤ -Real.log (250000000000 / 675060822749) ∧
    -Real.log (250000000000 / 675060822749) ≤ (496670939 / 500000000) := by
  have h := checkLog_sound (w := (175060822749 / 1175060822749)) (n := 12)
    (lo := (37524337 / 125000000)) (hi := (300194697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675060822749 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(675060822749 / 500000000000) = 1/(250000000000 / 675060822749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (248335469 / 250000000) (496670939 / 500000000) (Real.log (675060822749 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (675060822749 / 250000000000) = -Real.log (250000000000 / 675060822749) := by
    rw [show ((675060822749 / 250000000000) : ℝ) = ((250000000000 / 675060822749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (995596917 / 1000000000) ≤ -Real.log (500000000000 / 1353169661389) ∧
    -Real.log (500000000000 / 1353169661389) ≤ (995596919 / 1000000000) := by
  have h := checkLog_sound (w := (353169661389 / 2353169661389)) (n := 12)
    (lo := (302449737 / 1000000000)) (hi := (151224869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353169661389 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1353169661389 / 1000000000000) = 1/(500000000000 / 1353169661389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (995596917 / 1000000000) (995596919 / 1000000000) (Real.log (1353169661389 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1353169661389 / 500000000000) = -Real.log (500000000000 / 1353169661389) := by
    rw [show ((1353169661389 / 500000000000) : ℝ) = ((500000000000 / 1353169661389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (719570811 / 1000000000) ≤ -Real.log (250000000000 / 513387915569) ∧
    -Real.log (250000000000 / 513387915569) ≤ (719570813 / 1000000000) := by
  have h := checkLog_sound (w := (13387915569 / 1013387915569)) (n := 12)
    (lo := (26423631 / 1000000000)) (hi := (1651477 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513387915569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513387915569 / 500000000000) = 1/(250000000000 / 513387915569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (719570811 / 1000000000) (719570813 / 1000000000) (Real.log (513387915569 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (513387915569 / 250000000000) = -Real.log (250000000000 / 513387915569) := by
    rw [show ((513387915569 / 250000000000) : ℝ) = ((250000000000 / 513387915569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (180318501 / 250000000) ≤ -Real.log (500000000000 / 1028526118691) ∧
    -Real.log (500000000000 / 1028526118691) ≤ (360637003 / 500000000) := by
  have h := checkLog_sound (w := (28526118691 / 2028526118691)) (n := 12)
    (lo := (3515853 / 125000000)) (hi := (1125073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1028526118691 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1028526118691 / 1000000000000) = 1/(500000000000 / 1028526118691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (180318501 / 250000000) (360637003 / 500000000) (Real.log (1028526118691 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1028526118691 / 500000000000) = -Real.log (500000000000 / 1028526118691) := by
    rw [show ((1028526118691 / 500000000000) : ℝ) = ((500000000000 / 1028526118691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0175
