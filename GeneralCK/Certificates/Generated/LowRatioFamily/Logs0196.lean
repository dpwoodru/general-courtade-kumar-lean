import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12544_neg : (3787197 / 12500000) ≤ -Real.log (738617 / 1000000) ∧
    -Real.log (738617 / 1000000) ≤ (302975761 / 1000000000) := by
  have h := checkLog_sound (w := (261383 / 1738617)) (n := 12)
    (lo := (3787197 / 12500000)) (hi := (302975761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738617) = 1/(738617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12544 : Bounds (-302975761 / 1000000000) (-3787197 / 12500000) (Real.log (738617 / 1000000)) := by
  have h := reflection_log_12544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12545_neg : (46608479 / 200000000) ≤ -Real.log (200000 / 252487) ∧
    -Real.log (200000 / 252487) ≤ (58260599 / 250000000) := by
  have h := checkLog_sound (w := (52487 / 452487)) (n := 12)
    (lo := (46608479 / 200000000)) (hi := (58260599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252487 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252487 / 200000) = 1/(200000 / 252487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12545 : Bounds (46608479 / 200000000) (58260599 / 250000000) (Real.log (252487 / 200000)) := by
  have h := reflection_log_12545_neg
  have he : Real.log (252487 / 200000) = -Real.log (200000 / 252487) := by
    rw [show ((252487 / 200000) : ℝ) = ((200000 / 252487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12546_neg : (304401059 / 1000000000) ≤ -Real.log (147513 / 200000) ∧
    -Real.log (147513 / 200000) ≤ (15220053 / 50000000) := by
  have h := checkLog_sound (w := (52487 / 347513)) (n := 12)
    (lo := (304401059 / 1000000000)) (hi := (15220053 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147513) = 1/(147513 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12546 : Bounds (-15220053 / 50000000) (-304401059 / 1000000000) (Real.log (147513 / 200000)) := by
  have h := reflection_log_12546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12547_neg : (71358663 / 1000000000) ≤ -Real.log (37245114831 / 40000000000) ∧
    -Real.log (37245114831 / 40000000000) ≤ (8919833 / 125000000) := by
  have h := checkLog_sound (w := (2754885169 / 77245114831)) (n := 12)
    (lo := (71358663 / 1000000000)) (hi := (8919833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37245114831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37245114831) = 1/(37245114831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12547 : Bounds (-8919833 / 125000000) (-71358663 / 1000000000) (Real.log (37245114831 / 40000000000)) := by
  have h := reflection_log_12547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12548_neg : (35383511 / 500000000) ≤ -Real.log (931678927311 / 1000000000000) ∧
    -Real.log (931678927311 / 1000000000000) ≤ (70767023 / 1000000000) := by
  have h := checkLog_sound (w := (68321072689 / 1931678927311)) (n := 12)
    (lo := (35383511 / 500000000)) (hi := (70767023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931678927311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931678927311) = 1/(931678927311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12548 : Bounds (-70767023 / 1000000000) (-35383511 / 500000000) (Real.log (931678927311 / 1000000000000)) := by
  have h := reflection_log_12548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12549_neg : (267592249 / 500000000) ≤ -Real.log (250000000000 / 426940823187) ∧
    -Real.log (250000000000 / 426940823187) ≤ (535184499 / 1000000000) := by
  have h := checkLog_sound (w := (176940823187 / 676940823187)) (n := 12)
    (lo := (267592249 / 500000000)) (hi := (535184499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426940823187 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426940823187 / 250000000000) = 1/(250000000000 / 426940823187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12549 : Bounds (267592249 / 500000000) (535184499 / 1000000000) (Real.log (426940823187 / 250000000000)) := by
  have h := reflection_log_12549_neg
  have he : Real.log (426940823187 / 250000000000) = -Real.log (250000000000 / 426940823187) := by
    rw [show ((426940823187 / 250000000000) : ℝ) = ((250000000000 / 426940823187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12550_neg : (268721727 / 500000000) ≤ -Real.log (500000000000 / 855812708033) ∧
    -Real.log (500000000000 / 855812708033) ≤ (107488691 / 200000000) := by
  have h := checkLog_sound (w := (355812708033 / 1355812708033)) (n := 12)
    (lo := (268721727 / 500000000)) (hi := (107488691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855812708033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855812708033 / 500000000000) = 1/(500000000000 / 855812708033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12550 : Bounds (268721727 / 500000000) (107488691 / 200000000) (Real.log (855812708033 / 500000000000)) := by
  have h := reflection_log_12550_neg
  have he : Real.log (855812708033 / 500000000000) = -Real.log (500000000000 / 855812708033) := by
    rw [show ((855812708033 / 500000000000) : ℝ) = ((500000000000 / 855812708033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12551_neg : (273986849 / 250000000) ≤ -Real.log (500000000000 / 1496007984031) ∧
    -Real.log (500000000000 / 1496007984031) ≤ (547973699 / 500000000) := by
  have h := checkLog_sound (w := (496007984031 / 2496007984031)) (n := 12)
    (lo := (50350027 / 125000000)) (hi := (402800217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496007984031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1496007984031 / 1000000000000) = 1/(500000000000 / 1496007984031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12551 : Bounds (273986849 / 250000000) (547973699 / 500000000) (Real.log (1496007984031 / 500000000000)) := by
  have h := reflection_log_12551_neg
  have he : Real.log (1496007984031 / 500000000000) = -Real.log (500000000000 / 1496007984031) := by
    rw [show ((1496007984031 / 500000000000) : ℝ) = ((500000000000 / 1496007984031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12552_neg : (17165817 / 15625000) ≤ -Real.log (1 / 3) ∧
    -Real.log (1 / 3) ≤ (109861229 / 100000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3 / 2) = 1/(1 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12552 : Bounds (17165817 / 15625000) (109861229 / 100000000) (Real.log (3 / 1)) := by
  have h := reflection_log_12552_neg
  have he : Real.log (3 / 1) = -Real.log (1 / 3) := by
    rw [show ((3 / 1) : ℝ) = ((1 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12553_neg : (40746311 / 100000000) ≤ -Real.log (1000 / 1503) ∧
    -Real.log (1000 / 1503) ≤ (407463111 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2503)) (n := 12)
    (lo := (40746311 / 100000000)) (hi := (407463111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1503 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1503 / 1000) = 1/(1000 / 1503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12553 : Bounds (40746311 / 100000000) (407463111 / 1000000000) (Real.log (1503 / 1000)) := by
  have h := reflection_log_12553_neg
  have he : Real.log (1503 / 1000) = -Real.log (1000 / 1503) := by
    rw [show ((1503 / 1000) : ℝ) = ((1000 / 1503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12554_neg : (174791313 / 250000000) ≤ -Real.log (497 / 1000) ∧
    -Real.log (497 / 1000) ≤ (349582627 / 500000000) := by
  have h := checkLog_sound (w := (3 / 997)) (n := 12)
    (lo := (752259 / 125000000)) (hi := (6018073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 497) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 497) = 1/(497 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12554 : Bounds (-349582627 / 500000000) (-174791313 / 250000000) (Real.log (497 / 1000)) := by
  have h := reflection_log_12554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12555_neg : (502873 / 1000000000) ≤ -Real.log (1000000 / 1000503) ∧
    -Real.log (1000000 / 1000503) ≤ (251437 / 500000000) := by
  have h := checkLog_sound (w := (503 / 2000503)) (n := 12)
    (lo := (502873 / 1000000000)) (hi := (251437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000503 / 1000000) = 1/(1000000 / 1000503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12555 : Bounds (502873 / 1000000000) (251437 / 500000000) (Real.log (1000503 / 1000000)) := by
  have h := reflection_log_12555_neg
  have he : Real.log (1000503 / 1000000) = -Real.log (1000000 / 1000503) := by
    rw [show ((1000503 / 1000000) : ℝ) = ((1000000 / 1000503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12556_neg : (251563 / 500000000) ≤ -Real.log (999497 / 1000000) ∧
    -Real.log (999497 / 1000000) ≤ (503127 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 1999497)) (n := 12)
    (lo := (251563 / 500000000)) (hi := (503127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999497) = 1/(999497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12556 : Bounds (-503127 / 1000000000) (-251563 / 500000000) (Real.log (999497 / 1000000)) := by
  have h := reflection_log_12556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12557_neg : (232666067 / 1000000000) ≤ -Real.log (25000 / 31549) ∧
    -Real.log (25000 / 31549) ≤ (58166517 / 250000000) := by
  have h := checkLog_sound (w := (6549 / 56549)) (n := 12)
    (lo := (232666067 / 1000000000)) (hi := (58166517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31549 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31549 / 25000) = 1/(25000 / 31549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12557 : Bounds (232666067 / 1000000000) (58166517 / 250000000) (Real.log (31549 / 25000)) := by
  have h := reflection_log_12557_neg
  have he : Real.log (31549 / 25000) = -Real.log (25000 / 31549) := by
    rw [show ((31549 / 25000) : ℝ) = ((25000 / 31549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12558_neg : (60751451 / 200000000) ≤ -Real.log (18451 / 25000) ∧
    -Real.log (18451 / 25000) ≤ (37969657 / 125000000) := by
  have h := checkLog_sound (w := (6549 / 43451)) (n := 12)
    (lo := (60751451 / 200000000)) (hi := (37969657 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18451) = 1/(18451 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12558 : Bounds (-37969657 / 125000000) (-60751451 / 200000000) (Real.log (18451 / 25000)) := by
  have h := reflection_log_12558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12559_neg : (11720789 / 50000000) ≤ -Real.log (100000 / 126417) ∧
    -Real.log (100000 / 126417) ≤ (234415781 / 1000000000) := by
  have h := checkLog_sound (w := (26417 / 226417)) (n := 12)
    (lo := (11720789 / 50000000)) (hi := (234415781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126417 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126417 / 100000) = 1/(100000 / 126417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12559 : Bounds (11720789 / 50000000) (234415781 / 1000000000) (Real.log (126417 / 100000)) := by
  have h := reflection_log_12559_neg
  have he : Real.log (126417 / 100000) = -Real.log (100000 / 126417) := by
    rw [show ((126417 / 100000) : ℝ) = ((100000 / 126417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12560_neg : (61351233 / 200000000) ≤ -Real.log (73583 / 100000) ∧
    -Real.log (73583 / 100000) ≤ (153378083 / 500000000) := by
  have h := checkLog_sound (w := (26417 / 173583)) (n := 12)
    (lo := (61351233 / 200000000)) (hi := (153378083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73583) = 1/(73583 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12560 : Bounds (-153378083 / 500000000) (-61351233 / 200000000) (Real.log (73583 / 100000)) := by
  have h := reflection_log_12560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12561_neg : (2260637 / 31250000) ≤ -Real.log (9302142111 / 10000000000) ∧
    -Real.log (9302142111 / 10000000000) ≤ (14468077 / 200000000) := by
  have h := checkLog_sound (w := (697857889 / 19302142111)) (n := 12)
    (lo := (2260637 / 31250000)) (hi := (14468077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9302142111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9302142111) = 1/(9302142111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12561 : Bounds (-14468077 / 200000000) (-2260637 / 31250000) (Real.log (9302142111 / 10000000000)) := by
  have h := reflection_log_12561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12562_neg : (71091187 / 1000000000) ≤ -Real.log (582110599 / 625000000) ∧
    -Real.log (582110599 / 625000000) ≤ (17772797 / 250000000) := by
  have h := checkLog_sound (w := (42889401 / 1207110599)) (n := 12)
    (lo := (71091187 / 1000000000)) (hi := (17772797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 582110599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 582110599) = 1/(582110599 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12562 : Bounds (-17772797 / 250000000) (-71091187 / 1000000000) (Real.log (582110599 / 625000000)) := by
  have h := reflection_log_12562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12563_neg : (536423323 / 1000000000) ≤ -Real.log (500000000000 / 854940111647) ∧
    -Real.log (500000000000 / 854940111647) ≤ (134105831 / 250000000) := by
  have h := checkLog_sound (w := (354940111647 / 1354940111647)) (n := 12)
    (lo := (536423323 / 1000000000)) (hi := (134105831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854940111647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854940111647 / 500000000000) = 1/(500000000000 / 854940111647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12563 : Bounds (536423323 / 1000000000) (134105831 / 250000000) (Real.log (854940111647 / 500000000000)) := by
  have h := reflection_log_12563_neg
  have he : Real.log (854940111647 / 500000000000) = -Real.log (500000000000 / 854940111647) := by
    rw [show ((854940111647 / 500000000000) : ℝ) = ((500000000000 / 854940111647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12564_neg : (108234389 / 200000000) ≤ -Real.log (250000000000 / 429504776919) ∧
    -Real.log (250000000000 / 429504776919) ≤ (270585973 / 500000000) := by
  have h := checkLog_sound (w := (179504776919 / 679504776919)) (n := 12)
    (lo := (108234389 / 200000000)) (hi := (270585973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429504776919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429504776919 / 250000000000) = 1/(250000000000 / 429504776919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12564 : Bounds (108234389 / 200000000) (270585973 / 500000000) (Real.log (429504776919 / 250000000000)) := by
  have h := reflection_log_12564_neg
  have he : Real.log (429504776919 / 250000000000) = -Real.log (250000000000 / 429504776919) := by
    rw [show ((429504776919 / 250000000000) : ℝ) = ((250000000000 / 429504776919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12565_neg : (1106628363 / 1000000000) ≤ -Real.log (31250000000 / 94504527163) ∧
    -Real.log (31250000000 / 94504527163) ≤ (221325673 / 200000000) := by
  have h := checkLog_sound (w := (32004527163 / 157004527163)) (n := 12)
    (lo := (413481183 / 1000000000)) (hi := (12921287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94504527163 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94504527163 / 62500000000) = 1/(31250000000 / 94504527163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12565 : Bounds (1106628363 / 1000000000) (221325673 / 200000000) (Real.log (94504527163 / 31250000000)) := by
  have h := reflection_log_12565_neg
  have he : Real.log (94504527163 / 31250000000) = -Real.log (31250000000 / 94504527163) := by
    rw [show ((94504527163 / 31250000000) : ℝ) = ((31250000000 / 94504527163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12566_neg : (409457129 / 1000000000) ≤ -Real.log (500 / 753) ∧
    -Real.log (500 / 753) ≤ (40945713 / 100000000) := by
  have h := checkLog_sound (w := (253 / 1253)) (n := 12)
    (lo := (409457129 / 1000000000)) (hi := (40945713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753 / 500) = 1/(500 / 753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12566 : Bounds (409457129 / 1000000000) (40945713 / 100000000) (Real.log (753 / 500)) := by
  have h := reflection_log_12566_neg
  have he : Real.log (753 / 500) = -Real.log (500 / 753) := by
    rw [show ((753 / 500) : ℝ) = ((500 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12567_neg : (705219761 / 1000000000) ≤ -Real.log (247 / 500) ∧
    -Real.log (247 / 500) ≤ (705219763 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 497)) (n := 12)
    (lo := (12072581 / 1000000000)) (hi := (6036291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 247) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 247) = 1/(247 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12567 : Bounds (-705219763 / 1000000000) (-705219761 / 1000000000) (Real.log (247 / 500)) := by
  have h := reflection_log_12567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12568_neg : (31617 / 62500000) ≤ -Real.log (500000 / 500253) ∧
    -Real.log (500000 / 500253) ≤ (505873 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1000253)) (n := 12)
    (lo := (31617 / 62500000)) (hi := (505873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500253 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500253 / 500000) = 1/(500000 / 500253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12568 : Bounds (31617 / 62500000) (505873 / 1000000000) (Real.log (500253 / 500000)) := by
  have h := reflection_log_12568_neg
  have he : Real.log (500253 / 500000) = -Real.log (500000 / 500253) := by
    rw [show ((500253 / 500000) : ℝ) = ((500000 / 500253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12569_neg : (31633 / 62500000) ≤ -Real.log (499747 / 500000) ∧
    -Real.log (499747 / 500000) ≤ (506129 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 999747)) (n := 12)
    (lo := (31633 / 62500000)) (hi := (506129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499747) = 1/(499747 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12569 : Bounds (-506129 / 1000000000) (-31633 / 62500000) (Real.log (499747 / 500000)) := by
  have h := reflection_log_12569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12570_neg : (46807519 / 200000000) ≤ -Real.log (250000 / 315923) ∧
    -Real.log (250000 / 315923) ≤ (58509399 / 250000000) := by
  have h := checkLog_sound (w := (65923 / 565923)) (n := 12)
    (lo := (46807519 / 200000000)) (hi := (58509399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315923 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315923 / 250000) = 1/(250000 / 315923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12570 : Bounds (46807519 / 200000000) (58509399 / 250000000) (Real.log (315923 / 250000)) := by
  have h := reflection_log_12570_neg
  have he : Real.log (315923 / 250000) = -Real.log (250000 / 315923) := by
    rw [show ((315923 / 250000) : ℝ) = ((250000 / 315923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12571_neg : (306106769 / 1000000000) ≤ -Real.log (184077 / 250000) ∧
    -Real.log (184077 / 250000) ≤ (30610677 / 100000000) := by
  have h := checkLog_sound (w := (65923 / 434077)) (n := 12)
    (lo := (306106769 / 1000000000)) (hi := (30610677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184077) = 1/(184077 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12571 : Bounds (-30610677 / 100000000) (-306106769 / 1000000000) (Real.log (184077 / 250000)) := by
  have h := reflection_log_12571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12572_neg : (235789651 / 1000000000) ≤ -Real.log (250000 / 316477) ∧
    -Real.log (250000 / 316477) ≤ (58947413 / 250000000) := by
  have h := checkLog_sound (w := (66477 / 566477)) (n := 12)
    (lo := (235789651 / 1000000000)) (hi := (58947413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316477 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316477 / 250000) = 1/(250000 / 316477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12572 : Bounds (235789651 / 1000000000) (58947413 / 250000000) (Real.log (316477 / 250000)) := by
  have h := reflection_log_12572_neg
  have he : Real.log (316477 / 250000) = -Real.log (250000 / 316477) := by
    rw [show ((316477 / 250000) : ℝ) = ((250000 / 316477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12573_neg : (309120917 / 1000000000) ≤ -Real.log (183523 / 250000) ∧
    -Real.log (183523 / 250000) ≤ (154560459 / 500000000) := by
  have h := checkLog_sound (w := (66477 / 433523)) (n := 12)
    (lo := (309120917 / 1000000000)) (hi := (154560459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183523) = 1/(183523 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12573 : Bounds (-154560459 / 500000000) (-309120917 / 1000000000) (Real.log (183523 / 250000)) := by
  have h := reflection_log_12573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12574_neg : (36665633 / 500000000) ≤ -Real.log (58080808471 / 62500000000) ∧
    -Real.log (58080808471 / 62500000000) ≤ (73331267 / 1000000000) := by
  have h := checkLog_sound (w := (4419191529 / 120580808471)) (n := 12)
    (lo := (36665633 / 500000000)) (hi := (73331267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58080808471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58080808471) = 1/(58080808471 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12574 : Bounds (-73331267 / 1000000000) (-36665633 / 500000000) (Real.log (58080808471 / 62500000000)) := by
  have h := reflection_log_12574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12575_neg : (36034587 / 500000000) ≤ -Real.log (58154158071 / 62500000000) ∧
    -Real.log (58154158071 / 62500000000) ≤ (2882767 / 40000000) := by
  have h := checkLog_sound (w := (4345841929 / 120654158071)) (n := 12)
    (lo := (36034587 / 500000000)) (hi := (2882767 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58154158071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58154158071) = 1/(58154158071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12575 : Bounds (-2882767 / 40000000) (-36034587 / 500000000) (Real.log (58154158071 / 62500000000)) := by
  have h := reflection_log_12575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12576_neg : (135036091 / 250000000) ≤ -Real.log (500000000000 / 858127305421) ∧
    -Real.log (500000000000 / 858127305421) ≤ (108028873 / 200000000) := by
  have h := checkLog_sound (w := (358127305421 / 1358127305421)) (n := 12)
    (lo := (135036091 / 250000000)) (hi := (108028873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858127305421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858127305421 / 500000000000) = 1/(500000000000 / 858127305421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12576 : Bounds (135036091 / 250000000) (108028873 / 200000000) (Real.log (858127305421 / 500000000000)) := by
  have h := reflection_log_12576_neg
  have he : Real.log (858127305421 / 500000000000) = -Real.log (500000000000 / 858127305421) := by
    rw [show ((858127305421 / 500000000000) : ℝ) = ((500000000000 / 858127305421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12577_neg : (68113821 / 125000000) ≤ -Real.log (100000000000 / 172445415561) ∧
    -Real.log (100000000000 / 172445415561) ≤ (544910569 / 1000000000) := by
  have h := checkLog_sound (w := (72445415561 / 272445415561)) (n := 12)
    (lo := (68113821 / 125000000)) (hi := (544910569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172445415561 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172445415561 / 100000000000) = 1/(100000000000 / 172445415561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12577 : Bounds (68113821 / 125000000) (544910569 / 1000000000) (Real.log (172445415561 / 100000000000)) := by
  have h := reflection_log_12577_neg
  have he : Real.log (172445415561 / 100000000000) = -Real.log (100000000000 / 172445415561) := by
    rw [show ((172445415561 / 100000000000) : ℝ) = ((100000000000 / 172445415561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12578_neg : (1106628363 / 1000000000) ≤ -Real.log (500000000000 / 1512072434607) ∧
    -Real.log (500000000000 / 1512072434607) ≤ (221325673 / 200000000) := by
  have h := checkLog_sound (w := (512072434607 / 2512072434607)) (n := 12)
    (lo := (413481183 / 1000000000)) (hi := (12921287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1512072434607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1512072434607 / 1000000000000) = 1/(500000000000 / 1512072434607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12578 : Bounds (1106628363 / 1000000000) (221325673 / 200000000) (Real.log (1512072434607 / 500000000000)) := by
  have h := reflection_log_12578_neg
  have he : Real.log (1512072434607 / 500000000000) = -Real.log (500000000000 / 1512072434607) := by
    rw [show ((1512072434607 / 500000000000) : ℝ) = ((500000000000 / 1512072434607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12579_neg : (111467689 / 100000000) ≤ -Real.log (62500000000 / 190536437247) ∧
    -Real.log (62500000000 / 190536437247) ≤ (278669223 / 250000000) := by
  have h := checkLog_sound (w := (65536437247 / 315536437247)) (n := 12)
    (lo := (42152971 / 100000000)) (hi := (421529711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190536437247 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(190536437247 / 125000000000) = 1/(62500000000 / 190536437247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12579 : Bounds (111467689 / 100000000) (278669223 / 250000000) (Real.log (190536437247 / 62500000000)) := by
  have h := reflection_log_12579_neg
  have he : Real.log (190536437247 / 62500000000) = -Real.log (62500000000 / 190536437247) := by
    rw [show ((190536437247 / 62500000000) : ℝ) = ((62500000000 / 190536437247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12580_neg : (411447179 / 1000000000) ≤ -Real.log (1000 / 1509) ∧
    -Real.log (1000 / 1509) ≤ (20572359 / 50000000) := by
  have h := checkLog_sound (w := (509 / 2509)) (n := 12)
    (lo := (411447179 / 1000000000)) (hi := (20572359 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509 / 1000) = 1/(1000 / 1509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12580 : Bounds (411447179 / 1000000000) (20572359 / 50000000) (Real.log (1509 / 1000)) := by
  have h := reflection_log_12580_neg
  have he : Real.log (1509 / 1000) = -Real.log (1000 / 1509) := by
    rw [show ((1509 / 1000) : ℝ) = ((1000 / 1509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12581_neg : (14226223 / 20000000) ≤ -Real.log (491 / 1000) ∧
    -Real.log (491 / 1000) ≤ (44456947 / 62500000) := by
  have h := checkLog_sound (w := (9 / 991)) (n := 12)
    (lo := (1816397 / 100000000)) (hi := (18163971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 491) = 1/(491 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12581 : Bounds (-44456947 / 62500000) (-14226223 / 20000000) (Real.log (491 / 1000)) := by
  have h := reflection_log_12581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12582_neg : (50887 / 100000000) ≤ -Real.log (1000000 / 1000509) ∧
    -Real.log (1000000 / 1000509) ≤ (508871 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 2000509)) (n := 12)
    (lo := (50887 / 100000000)) (hi := (508871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000509 / 1000000) = 1/(1000000 / 1000509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12582 : Bounds (50887 / 100000000) (508871 / 1000000000) (Real.log (1000509 / 1000000)) := by
  have h := reflection_log_12582_neg
  have he : Real.log (1000509 / 1000000) = -Real.log (1000000 / 1000509) := by
    rw [show ((1000509 / 1000000) : ℝ) = ((1000000 / 1000509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12583_neg : (509129 / 1000000000) ≤ -Real.log (999491 / 1000000) ∧
    -Real.log (999491 / 1000000) ≤ (50913 / 100000000) := by
  have h := checkLog_sound (w := (509 / 1999491)) (n := 12)
    (lo := (509129 / 1000000000)) (hi := (50913 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999491) = 1/(999491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12583 : Bounds (-50913 / 100000000) (-509129 / 1000000000) (Real.log (999491 / 1000000)) := by
  have h := reflection_log_12583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12584_neg : (58852601 / 250000000) ≤ -Real.log (250000 / 316357) ∧
    -Real.log (250000 / 316357) ≤ (47082081 / 200000000) := by
  have h := checkLog_sound (w := (66357 / 566357)) (n := 12)
    (lo := (58852601 / 250000000)) (hi := (47082081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316357 / 250000) = 1/(250000 / 316357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12584 : Bounds (58852601 / 250000000) (47082081 / 200000000) (Real.log (316357 / 250000)) := by
  have h := reflection_log_12584_neg
  have he : Real.log (316357 / 250000) = -Real.log (250000 / 316357) := by
    rw [show ((316357 / 250000) : ℝ) = ((250000 / 316357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12585_neg : (154233631 / 500000000) ≤ -Real.log (183643 / 250000) ∧
    -Real.log (183643 / 250000) ≤ (308467263 / 1000000000) := by
  have h := checkLog_sound (w := (66357 / 433643)) (n := 12)
    (lo := (154233631 / 500000000)) (hi := (308467263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183643) = 1/(183643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12585 : Bounds (-308467263 / 1000000000) (-154233631 / 500000000) (Real.log (183643 / 250000)) := by
  have h := reflection_log_12585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12586_neg : (237164003 / 1000000000) ≤ -Real.log (1000000 / 1267649) ∧
    -Real.log (1000000 / 1267649) ≤ (59291001 / 250000000) := by
  have h := checkLog_sound (w := (267649 / 2267649)) (n := 12)
    (lo := (237164003 / 1000000000)) (hi := (59291001 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267649 / 1000000) = 1/(1000000 / 1267649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12586 : Bounds (237164003 / 1000000000) (59291001 / 250000000) (Real.log (1267649 / 1000000)) := by
  have h := reflection_log_12586_neg
  have he : Real.log (1267649 / 1000000) = -Real.log (1000000 / 1267649) := by
    rw [show ((1267649 / 1000000) : ℝ) = ((1000000 / 1267649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12587_neg : (311495371 / 1000000000) ≤ -Real.log (732351 / 1000000) ∧
    -Real.log (732351 / 1000000) ≤ (77873843 / 250000000) := by
  have h := checkLog_sound (w := (267649 / 1732351)) (n := 12)
    (lo := (311495371 / 1000000000)) (hi := (77873843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732351) = 1/(732351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12587 : Bounds (-77873843 / 250000000) (-311495371 / 1000000000) (Real.log (732351 / 1000000)) := by
  have h := reflection_log_12587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12588_neg : (74331367 / 1000000000) ≤ -Real.log (928364012799 / 1000000000000) ∧
    -Real.log (928364012799 / 1000000000000) ≤ (9291421 / 125000000) := by
  have h := checkLog_sound (w := (71635987201 / 1928364012799)) (n := 12)
    (lo := (74331367 / 1000000000)) (hi := (9291421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 928364012799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 928364012799) = 1/(928364012799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12588 : Bounds (-9291421 / 125000000) (-74331367 / 1000000000) (Real.log (928364012799 / 1000000000000)) := by
  have h := reflection_log_12588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12589_neg : (73056857 / 1000000000) ≤ -Real.log (58096748551 / 62500000000) ∧
    -Real.log (58096748551 / 62500000000) ≤ (36528429 / 500000000) := by
  have h := checkLog_sound (w := (4403251449 / 120596748551)) (n := 12)
    (lo := (73056857 / 1000000000)) (hi := (36528429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58096748551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58096748551) = 1/(58096748551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12589 : Bounds (-36528429 / 500000000) (-73056857 / 1000000000) (Real.log (58096748551 / 62500000000)) := by
  have h := reflection_log_12589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12590_neg : (543877667 / 1000000000) ≤ -Real.log (500000000000 / 861336941783) ∧
    -Real.log (500000000000 / 861336941783) ≤ (135969417 / 250000000) := by
  have h := checkLog_sound (w := (361336941783 / 1361336941783)) (n := 12)
    (lo := (543877667 / 1000000000)) (hi := (135969417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861336941783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861336941783 / 500000000000) = 1/(500000000000 / 861336941783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12590 : Bounds (543877667 / 1000000000) (135969417 / 250000000) (Real.log (861336941783 / 500000000000)) := by
  have h := reflection_log_12590_neg
  have he : Real.log (861336941783 / 500000000000) = -Real.log (500000000000 / 861336941783) := by
    rw [show ((861336941783 / 500000000000) : ℝ) = ((500000000000 / 861336941783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12591_neg : (175571 / 320000) ≤ -Real.log (62500000000 / 108183183337) ∧
    -Real.log (62500000000 / 108183183337) ≤ (34291211 / 62500000) := by
  have h := checkLog_sound (w := (45683183337 / 170683183337)) (n := 12)
    (lo := (175571 / 320000)) (hi := (34291211 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108183183337 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108183183337 / 62500000000) = 1/(62500000000 / 108183183337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12591 : Bounds (175571 / 320000) (34291211 / 62500000) (Real.log (108183183337 / 62500000000)) := by
  have h := reflection_log_12591_neg
  have he : Real.log (108183183337 / 62500000000) = -Real.log (62500000000 / 108183183337) := by
    rw [show ((108183183337 / 62500000000) : ℝ) = ((62500000000 / 108183183337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12592_neg : (111467689 / 100000000) ≤ -Real.log (20000000000 / 60971659919) ∧
    -Real.log (20000000000 / 60971659919) ≤ (278669223 / 250000000) := by
  have h := checkLog_sound (w := (20971659919 / 100971659919)) (n := 12)
    (lo := (42152971 / 100000000)) (hi := (421529711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60971659919 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60971659919 / 40000000000) = 1/(20000000000 / 60971659919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12592 : Bounds (111467689 / 100000000) (278669223 / 250000000) (Real.log (60971659919 / 20000000000)) := by
  have h := reflection_log_12592_neg
  have he : Real.log (60971659919 / 20000000000) = -Real.log (20000000000 / 60971659919) := by
    rw [show ((60971659919 / 20000000000) : ℝ) = ((20000000000 / 60971659919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12593_neg : (112275833 / 100000000) ≤ -Real.log (500000000000 / 1536659877801) ∧
    -Real.log (500000000000 / 1536659877801) ≤ (280689583 / 250000000) := by
  have h := checkLog_sound (w := (536659877801 / 2536659877801)) (n := 12)
    (lo := (8592223 / 20000000)) (hi := (429611151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1536659877801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1536659877801 / 1000000000000) = 1/(500000000000 / 1536659877801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12593 : Bounds (112275833 / 100000000) (280689583 / 250000000) (Real.log (1536659877801 / 500000000000)) := by
  have h := reflection_log_12593_neg
  have he : Real.log (1536659877801 / 500000000000) = -Real.log (500000000000 / 1536659877801) := by
    rw [show ((1536659877801 / 500000000000) : ℝ) = ((500000000000 / 1536659877801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12594_neg : (413433277 / 1000000000) ≤ -Real.log (125 / 189) ∧
    -Real.log (125 / 189) ≤ (206716639 / 500000000) := by
  have h := checkLog_sound (w := (32 / 157)) (n := 12)
    (lo := (413433277 / 1000000000)) (hi := (206716639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 125) = 1/(125 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12594 : Bounds (413433277 / 1000000000) (206716639 / 500000000) (Real.log (189 / 125)) := by
  have h := reflection_log_12594_neg
  have he : Real.log (189 / 125) = -Real.log (125 / 189) := by
    rw [show ((189 / 125) : ℝ) = ((125 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12595_neg : (5604999 / 7812500) ≤ -Real.log (61 / 125) ∧
    -Real.log (61 / 125) ≤ (358719937 / 500000000) := by
  have h := checkLog_sound (w := (3 / 247)) (n := 12)
    (lo := (6073173 / 250000000)) (hi := (24292693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 122) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 122) = 1/(61 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12595 : Bounds (-358719937 / 500000000) (-5604999 / 7812500) (Real.log (61 / 125)) := by
  have h := reflection_log_12595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12596_neg : (127967 / 250000000) ≤ -Real.log (15625 / 15633) ∧
    -Real.log (15625 / 15633) ≤ (511869 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 15629)) (n := 12)
    (lo := (127967 / 250000000)) (hi := (511869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15633 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15633 / 15625) = 1/(15625 / 15633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12596 : Bounds (127967 / 250000000) (511869 / 1000000000) (Real.log (15633 / 15625)) := by
  have h := reflection_log_12596_neg
  have he : Real.log (15633 / 15625) = -Real.log (15625 / 15633) := by
    rw [show ((15633 / 15625) : ℝ) = ((15625 / 15633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12597_neg : (512131 / 1000000000) ≤ -Real.log (15617 / 15625) ∧
    -Real.log (15617 / 15625) ≤ (128033 / 250000000) := by
  have h := checkLog_sound (w := (4 / 15621)) (n := 12)
    (lo := (512131 / 1000000000)) (hi := (128033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15617) = 1/(15617 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12597 : Bounds (-128033 / 250000000) (-512131 / 1000000000) (Real.log (15617 / 15625)) := by
  have h := reflection_log_12597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12598_neg : (2367837 / 10000000) ≤ -Real.log (1000000 / 1267167) ∧
    -Real.log (1000000 / 1267167) ≤ (236783701 / 1000000000) := by
  have h := checkLog_sound (w := (267167 / 2267167)) (n := 12)
    (lo := (2367837 / 10000000)) (hi := (236783701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267167 / 1000000) = 1/(1000000 / 1267167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12598 : Bounds (2367837 / 10000000) (236783701 / 1000000000) (Real.log (1267167 / 1000000)) := by
  have h := reflection_log_12598_neg
  have he : Real.log (1267167 / 1000000) = -Real.log (1000000 / 1267167) := by
    rw [show ((1267167 / 1000000) : ℝ) = ((1000000 / 1267167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12599_neg : (310837433 / 1000000000) ≤ -Real.log (732833 / 1000000) ∧
    -Real.log (732833 / 1000000) ≤ (155418717 / 500000000) := by
  have h := checkLog_sound (w := (267167 / 1732833)) (n := 12)
    (lo := (310837433 / 1000000000)) (hi := (155418717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732833) = 1/(732833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12599 : Bounds (-155418717 / 500000000) (-310837433 / 1000000000) (Real.log (732833 / 1000000)) := by
  have h := reflection_log_12599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12600_neg : (238539621 / 1000000000) ≤ -Real.log (500000 / 634697) ∧
    -Real.log (500000 / 634697) ≤ (119269811 / 500000000) := by
  have h := checkLog_sound (w := (134697 / 1134697)) (n := 12)
    (lo := (238539621 / 1000000000)) (hi := (119269811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634697 / 500000) = 1/(500000 / 634697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12600 : Bounds (238539621 / 1000000000) (119269811 / 500000000) (Real.log (634697 / 500000)) := by
  have h := reflection_log_12600_neg
  have he : Real.log (634697 / 500000) = -Real.log (500000 / 634697) := by
    rw [show ((634697 / 500000) : ℝ) = ((500000 / 634697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12601_neg : (39235119 / 125000000) ≤ -Real.log (365303 / 500000) ∧
    -Real.log (365303 / 500000) ≤ (313880953 / 1000000000) := by
  have h := checkLog_sound (w := (134697 / 865303)) (n := 12)
    (lo := (39235119 / 125000000)) (hi := (313880953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365303) = 1/(365303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12601 : Bounds (-313880953 / 1000000000) (-39235119 / 125000000) (Real.log (365303 / 500000)) := by
  have h := reflection_log_12601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12602_neg : (7534133 / 100000000) ≤ -Real.log (231856718191 / 250000000000) ∧
    -Real.log (231856718191 / 250000000000) ≤ (75341331 / 1000000000) := by
  have h := checkLog_sound (w := (18143281809 / 481856718191)) (n := 12)
    (lo := (7534133 / 100000000)) (hi := (75341331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231856718191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231856718191) = 1/(231856718191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12602 : Bounds (-75341331 / 1000000000) (-7534133 / 100000000) (Real.log (231856718191 / 250000000000)) := by
  have h := reflection_log_12602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12603_neg : (74053733 / 1000000000) ≤ -Real.log (928621794111 / 1000000000000) ∧
    -Real.log (928621794111 / 1000000000000) ≤ (37026867 / 500000000) := by
  have h := checkLog_sound (w := (71378205889 / 1928621794111)) (n := 12)
    (lo := (74053733 / 1000000000)) (hi := (37026867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 928621794111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 928621794111) = 1/(928621794111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12603 : Bounds (-37026867 / 500000000) (-74053733 / 1000000000) (Real.log (928621794111 / 1000000000000)) := by
  have h := reflection_log_12603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12604_neg : (547621133 / 1000000000) ≤ -Real.log (500000000000 / 864567370737) ∧
    -Real.log (500000000000 / 864567370737) ≤ (273810567 / 500000000) := by
  have h := checkLog_sound (w := (364567370737 / 1364567370737)) (n := 12)
    (lo := (547621133 / 1000000000)) (hi := (273810567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864567370737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864567370737 / 500000000000) = 1/(500000000000 / 864567370737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12604 : Bounds (547621133 / 1000000000) (273810567 / 500000000) (Real.log (864567370737 / 500000000000)) := by
  have h := reflection_log_12604_neg
  have he : Real.log (864567370737 / 500000000000) = -Real.log (500000000000 / 864567370737) := by
    rw [show ((864567370737 / 500000000000) : ℝ) = ((500000000000 / 864567370737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12605_neg : (552420573 / 1000000000) ≤ -Real.log (125000000000 / 217181695743) ∧
    -Real.log (125000000000 / 217181695743) ≤ (276210287 / 500000000) := by
  have h := checkLog_sound (w := (92181695743 / 342181695743)) (n := 12)
    (lo := (552420573 / 1000000000)) (hi := (276210287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217181695743 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217181695743 / 125000000000) = 1/(125000000000 / 217181695743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12605 : Bounds (552420573 / 1000000000) (276210287 / 500000000) (Real.log (217181695743 / 125000000000)) := by
  have h := reflection_log_12605_neg
  have he : Real.log (217181695743 / 125000000000) = -Real.log (125000000000 / 217181695743) := by
    rw [show ((217181695743 / 125000000000) : ℝ) = ((125000000000 / 217181695743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12606_neg : (112275833 / 100000000) ≤ -Real.log (2500000000 / 7683299389) ∧
    -Real.log (2500000000 / 7683299389) ≤ (280689583 / 250000000) := by
  have h := checkLog_sound (w := (2683299389 / 12683299389)) (n := 12)
    (lo := (8592223 / 20000000)) (hi := (429611151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7683299389 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7683299389 / 5000000000) = 1/(2500000000 / 7683299389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12606 : Bounds (112275833 / 100000000) (280689583 / 250000000) (Real.log (7683299389 / 2500000000)) := by
  have h := reflection_log_12606_neg
  have he : Real.log (7683299389 / 2500000000) = -Real.log (2500000000 / 7683299389) := by
    rw [show ((7683299389 / 2500000000) : ℝ) = ((2500000000 / 7683299389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12607_neg : (22617463 / 20000000) ≤ -Real.log (500000000000 / 1549180327869) ∧
    -Real.log (500000000000 / 1549180327869) ≤ (17669893 / 15625000) := by
  have h := checkLog_sound (w := (549180327869 / 2549180327869)) (n := 12)
    (lo := (43772597 / 100000000)) (hi := (437725971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549180327869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1549180327869 / 1000000000000) = 1/(500000000000 / 1549180327869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12607 : Bounds (22617463 / 20000000) (17669893 / 15625000) (Real.log (1549180327869 / 500000000000)) := by
  have h := reflection_log_12607_neg
  have he : Real.log (1549180327869 / 500000000000) = -Real.log (500000000000 / 1549180327869) := by
    rw [show ((1549180327869 / 500000000000) : ℝ) = ((500000000000 / 1549180327869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
