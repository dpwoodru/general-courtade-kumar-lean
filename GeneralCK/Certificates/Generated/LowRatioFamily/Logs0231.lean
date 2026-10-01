import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14784_neg : (966654337 / 250000000) ≤ -Real.log (500000000000 / 23890243902439) ∧
    -Real.log (500000000000 / 23890243902439) ≤ (1933308677 / 500000000) := by
  have h := checkLog_sound (w := (7890243902439 / 39890243902439)) (n := 12)
    (lo := (50110181 / 125000000)) (hi := (400881449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23890243902439 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23890243902439 / 16000000000000) = 1/(500000000000 / 23890243902439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14784 : Bounds (966654337 / 250000000) (1933308677 / 500000000) (Real.log (23890243902439 / 500000000000)) := by
  have h := reflection_log_14784_neg
  have he : Real.log (23890243902439 / 500000000000) = -Real.log (500000000000 / 23890243902439) := by
    rw [show ((23890243902439 / 500000000000) : ℝ) = ((500000000000 / 23890243902439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14785_neg : (778364059 / 200000000) ≤ -Real.log (1 / 49) ∧
    -Real.log (1 / 49) ≤ (3891820301 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(49 / 32) = 1/(1 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14785 : Bounds (778364059 / 200000000) (3891820301 / 1000000000) (Real.log (49 / 1)) := by
  have h := reflection_log_14785_neg
  have he : Real.log (49 / 1) = -Real.log (1 / 49) := by
    rw [show ((49 / 1) : ℝ) = ((1 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14786_neg : (673454547 / 1000000000) ≤ -Real.log (1000 / 1961) ∧
    -Real.log (1000 / 1961) ≤ (168363637 / 250000000) := by
  have h := checkLog_sound (w := (961 / 2961)) (n := 12)
    (lo := (673454547 / 1000000000)) (hi := (168363637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961 / 1000) = 1/(1000 / 1961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14786 : Bounds (673454547 / 1000000000) (168363637 / 250000000) (Real.log (1961 / 1000)) := by
  have h := reflection_log_14786_neg
  have he : Real.log (1961 / 1000) = -Real.log (1000 / 1961) := by
    rw [show ((1961 / 1000) : ℝ) = ((1000 / 1961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14787_neg : (324419363 / 100000000) ≤ -Real.log (39 / 1000) ∧
    -Real.log (39 / 1000) ≤ (648838727 / 200000000) := by
  have h := checkLog_sound (w := (47 / 203)) (n := 12)
    (lo := (47160491 / 100000000)) (hi := (471604911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 78) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 78) = 1/(39 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14787 : Bounds (-648838727 / 200000000) (-324419363 / 100000000) (Real.log (39 / 1000)) := by
  have h := reflection_log_14787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14788_neg : (480269 / 500000000) ≤ -Real.log (1000000 / 1000961) ∧
    -Real.log (1000000 / 1000961) ≤ (960539 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 2000961)) (n := 12)
    (lo := (480269 / 500000000)) (hi := (960539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000961 / 1000000) = 1/(1000000 / 1000961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14788 : Bounds (480269 / 500000000) (960539 / 1000000000) (Real.log (1000961 / 1000000)) := by
  have h := reflection_log_14788_neg
  have he : Real.log (1000961 / 1000000) = -Real.log (1000000 / 1000961) := by
    rw [show ((1000961 / 1000000) : ℝ) = ((1000000 / 1000961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14789_neg : (480731 / 500000000) ≤ -Real.log (999039 / 1000000) ∧
    -Real.log (999039 / 1000000) ≤ (961463 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 1999039)) (n := 12)
    (lo := (480731 / 500000000)) (hi := (961463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999039) = 1/(999039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14789 : Bounds (-961463 / 1000000000) (-480731 / 500000000) (Real.log (999039 / 1000000)) := by
  have h := reflection_log_14789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14790_neg : (472226781 / 1000000000) ≤ -Real.log (1000000 / 1603561) ∧
    -Real.log (1000000 / 1603561) ≤ (236113391 / 500000000) := by
  have h := checkLog_sound (w := (603561 / 2603561)) (n := 12)
    (lo := (472226781 / 1000000000)) (hi := (236113391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603561 / 1000000) = 1/(1000000 / 1603561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14790 : Bounds (472226781 / 1000000000) (236113391 / 500000000) (Real.log (1603561 / 1000000)) := by
  have h := reflection_log_14790_neg
  have he : Real.log (1603561 / 1000000) = -Real.log (1000000 / 1603561) := by
    rw [show ((1603561 / 1000000) : ℝ) = ((1000000 / 1603561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14791_neg : (185046619 / 200000000) ≤ -Real.log (396439 / 1000000) ∧
    -Real.log (396439 / 1000000) ≤ (925233097 / 1000000000) := by
  have h := checkLog_sound (w := (103561 / 896439)) (n := 12)
    (lo := (46417183 / 200000000)) (hi := (58021479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 396439) = 1/(396439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14791 : Bounds (-925233097 / 1000000000) (-185046619 / 200000000) (Real.log (396439 / 1000000)) := by
  have h := reflection_log_14791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14792_neg : (118337319 / 250000000) ≤ -Real.log (500000 / 802681) ∧
    -Real.log (500000 / 802681) ≤ (473349277 / 1000000000) := by
  have h := checkLog_sound (w := (302681 / 1302681)) (n := 12)
    (lo := (118337319 / 250000000)) (hi := (473349277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802681 / 500000) = 1/(500000 / 802681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14792 : Bounds (118337319 / 250000000) (473349277 / 1000000000) (Real.log (802681 / 500000)) := by
  have h := reflection_log_14792_neg
  have he : Real.log (802681 / 500000) = -Real.log (500000 / 802681) := by
    rw [show ((802681 / 500000) : ℝ) = ((500000 / 802681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14793_neg : (929786389 / 1000000000) ≤ -Real.log (197319 / 500000) ∧
    -Real.log (197319 / 500000) ≤ (929786391 / 1000000000) := by
  have h := checkLog_sound (w := (52681 / 447319)) (n := 12)
    (lo := (236639209 / 1000000000)) (hi := (23663921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 197319) = 1/(197319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14793 : Bounds (-929786391 / 1000000000) (-929786389 / 1000000000) (Real.log (197319 / 500000)) := by
  have h := reflection_log_14793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14794_neg : (456437113 / 1000000000) ≤ -Real.log (158384212239 / 250000000000) ∧
    -Real.log (158384212239 / 250000000000) ≤ (228218557 / 500000000) := by
  have h := checkLog_sound (w := (91615787761 / 408384212239)) (n := 12)
    (lo := (456437113 / 1000000000)) (hi := (228218557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 158384212239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 158384212239) = 1/(158384212239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14794 : Bounds (-228218557 / 500000000) (-456437113 / 1000000000) (Real.log (158384212239 / 250000000000)) := by
  have h := reflection_log_14794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14795_neg : (226503157 / 500000000) ≤ -Real.log (635714119279 / 1000000000000) ∧
    -Real.log (635714119279 / 1000000000000) ≤ (90601263 / 200000000) := by
  have h := checkLog_sound (w := (364285880721 / 1635714119279)) (n := 12)
    (lo := (226503157 / 500000000)) (hi := (90601263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 635714119279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 635714119279) = 1/(635714119279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14795 : Bounds (-90601263 / 200000000) (-226503157 / 500000000) (Real.log (635714119279 / 1000000000000)) := by
  have h := reflection_log_14795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14796_neg : (11179679 / 8000000) ≤ -Real.log (500000000000 / 2022456166017) ∧
    -Real.log (500000000000 / 2022456166017) ≤ (698729939 / 500000000) := by
  have h := checkLog_sound (w := (22456166017 / 4022456166017)) (n := 12)
    (lo := (2233103 / 200000000)) (hi := (2791379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2022456166017 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2022456166017 / 2000000000000) = 1/(500000000000 / 2022456166017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14796 : Bounds (11179679 / 8000000) (698729939 / 500000000) (Real.log (2022456166017 / 500000000000)) := by
  have h := reflection_log_14796_neg
  have he : Real.log (2022456166017 / 500000000000) = -Real.log (500000000000 / 2022456166017) := by
    rw [show ((2022456166017 / 500000000000) : ℝ) = ((500000000000 / 2022456166017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14797_neg : (280627133 / 200000000) ≤ -Real.log (500000000000 / 2033967838881) ∧
    -Real.log (500000000000 / 2033967838881) ≤ (350783917 / 250000000) := by
  have h := checkLog_sound (w := (33967838881 / 4033967838881)) (n := 12)
    (lo := (3368261 / 200000000)) (hi := (8420653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2033967838881 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2033967838881 / 2000000000000) = 1/(500000000000 / 2033967838881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14797 : Bounds (280627133 / 200000000) (350783917 / 250000000) (Real.log (2033967838881 / 500000000000)) := by
  have h := reflection_log_14797_neg
  have he : Real.log (2033967838881 / 500000000000) = -Real.log (500000000000 / 2033967838881) := by
    rw [show ((2033967838881 / 500000000000) : ℝ) = ((500000000000 / 2033967838881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14798_neg : (3917648177 / 1000000000) ≤ -Real.log (250000000000 / 12570512820513) ∧
    -Real.log (250000000000 / 12570512820513) ≤ (3917648183 / 1000000000) := by
  have h := checkLog_sound (w := (4570512820513 / 20570512820513)) (n := 12)
    (lo := (451912277 / 1000000000)) (hi := (225956139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12570512820513 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12570512820513 / 8000000000000) = 1/(250000000000 / 12570512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14798 : Bounds (3917648177 / 1000000000) (3917648183 / 1000000000) (Real.log (12570512820513 / 250000000000)) := by
  have h := reflection_log_14798_neg
  have he : Real.log (12570512820513 / 250000000000) = -Real.log (250000000000 / 12570512820513) := by
    rw [show ((12570512820513 / 250000000000) : ℝ) = ((250000000000 / 12570512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14799_neg : (673964361 / 1000000000) ≤ -Real.log (500 / 981) ∧
    -Real.log (500 / 981) ≤ (336982181 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1481)) (n := 12)
    (lo := (673964361 / 1000000000)) (hi := (336982181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981 / 500) = 1/(500 / 981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14799 : Bounds (673964361 / 1000000000) (336982181 / 500000000) (Real.log (981 / 500)) := by
  have h := reflection_log_14799_neg
  have he : Real.log (981 / 500) = -Real.log (500 / 981) := by
    rw [show ((981 / 500) : ℝ) = ((500 / 981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14800_neg : (3270169117 / 1000000000) ≤ -Real.log (19 / 500) ∧
    -Real.log (19 / 500) ≤ (1635084561 / 500000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 76) = 1/(19 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14800 : Bounds (-1635084561 / 500000000) (-3270169117 / 1000000000) (Real.log (19 / 500)) := by
  have h := reflection_log_14800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14801_neg : (961537 / 1000000000) ≤ -Real.log (500000 / 500481) ∧
    -Real.log (500000 / 500481) ≤ (480769 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1000481)) (n := 12)
    (lo := (961537 / 1000000000)) (hi := (480769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500481 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500481 / 500000) = 1/(500000 / 500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14801 : Bounds (961537 / 1000000000) (480769 / 500000000) (Real.log (500481 / 500000)) := by
  have h := reflection_log_14801_neg
  have he : Real.log (500481 / 500000) = -Real.log (500000 / 500481) := by
    rw [show ((500481 / 500000) : ℝ) = ((500000 / 500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14802_neg : (962463 / 1000000000) ≤ -Real.log (499519 / 500000) ∧
    -Real.log (499519 / 500000) ≤ (30077 / 31250000) := by
  have h := checkLog_sound (w := (481 / 999519)) (n := 12)
    (lo := (962463 / 1000000000)) (hi := (30077 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499519) = 1/(499519 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14802 : Bounds (-30077 / 31250000) (-962463 / 1000000000) (Real.log (499519 / 500000)) := by
  have h := reflection_log_14802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14803_neg : (29558863 / 62500000) ≤ -Real.log (250000 / 401177) ∧
    -Real.log (250000 / 401177) ≤ (472941809 / 1000000000) := by
  have h := checkLog_sound (w := (151177 / 651177)) (n := 12)
    (lo := (29558863 / 62500000)) (hi := (472941809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401177 / 250000) = 1/(250000 / 401177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14803 : Bounds (29558863 / 62500000) (472941809 / 1000000000) (Real.log (401177 / 250000)) := by
  have h := reflection_log_14803_neg
  have he : Real.log (401177 / 250000) = -Real.log (250000 / 401177) := by
    rw [show ((401177 / 250000) : ℝ) = ((250000 / 401177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14804_neg : (464065273 / 500000000) ≤ -Real.log (98823 / 250000) ∧
    -Real.log (98823 / 250000) ≤ (232032637 / 250000000) := by
  have h := checkLog_sound (w := (26177 / 223823)) (n := 12)
    (lo := (117491683 / 500000000)) (hi := (234983367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98823) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 98823) = 1/(98823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14804 : Bounds (-232032637 / 250000000) (-464065273 / 500000000) (Real.log (98823 / 250000)) := by
  have h := reflection_log_14804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14805_neg : (237033307 / 500000000) ≤ -Real.log (500000 / 803257) ∧
    -Real.log (500000 / 803257) ≤ (94813323 / 200000000) := by
  have h := checkLog_sound (w := (303257 / 1303257)) (n := 12)
    (lo := (237033307 / 500000000)) (hi := (94813323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803257 / 500000) = 1/(500000 / 803257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14805 : Bounds (237033307 / 500000000) (94813323 / 200000000) (Real.log (803257 / 500000)) := by
  have h := reflection_log_14805_neg
  have he : Real.log (803257 / 500000) = -Real.log (500000 / 803257) := by
    rw [show ((803257 / 500000) : ℝ) = ((500000 / 803257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14806_neg : (932709789 / 1000000000) ≤ -Real.log (196743 / 500000) ∧
    -Real.log (196743 / 500000) ≤ (932709791 / 1000000000) := by
  have h := checkLog_sound (w := (53257 / 446743)) (n := 12)
    (lo := (239562609 / 1000000000)) (hi := (23956261 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 196743) = 1/(196743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14806 : Bounds (-932709791 / 1000000000) (-932709789 / 1000000000) (Real.log (196743 / 500000)) := by
  have h := reflection_log_14806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14807_neg : (18345727 / 40000000) ≤ -Real.log (158035191951 / 250000000000) ∧
    -Real.log (158035191951 / 250000000000) ≤ (57330397 / 125000000) := by
  have h := checkLog_sound (w := (91964808049 / 408035191951)) (n := 12)
    (lo := (18345727 / 40000000)) (hi := (57330397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 158035191951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 158035191951) = 1/(158035191951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14807 : Bounds (-57330397 / 125000000) (-18345727 / 40000000) (Real.log (158035191951 / 250000000000)) := by
  have h := reflection_log_14807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14808_neg : (227594369 / 500000000) ≤ -Real.log (39645514671 / 62500000000) ∧
    -Real.log (39645514671 / 62500000000) ≤ (455188739 / 1000000000) := by
  have h := checkLog_sound (w := (22854485329 / 102145514671)) (n := 12)
    (lo := (227594369 / 500000000)) (hi := (455188739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39645514671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39645514671) = 1/(39645514671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14808 : Bounds (-455188739 / 1000000000) (-227594369 / 500000000) (Real.log (39645514671 / 62500000000)) := by
  have h := reflection_log_14808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14809_neg : (700536177 / 500000000) ≤ -Real.log (50000000000 / 202977545713) ∧
    -Real.log (50000000000 / 202977545713) ≤ (1401072357 / 1000000000) := by
  have h := checkLog_sound (w := (2977545713 / 402977545713)) (n := 12)
    (lo := (7388997 / 500000000)) (hi := (2955599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202977545713 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(202977545713 / 200000000000) = 1/(50000000000 / 202977545713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14809 : Bounds (700536177 / 500000000) (1401072357 / 1000000000) (Real.log (202977545713 / 50000000000)) := by
  have h := reflection_log_14809_neg
  have he : Real.log (202977545713 / 50000000000) = -Real.log (50000000000 / 202977545713) := by
    rw [show ((202977545713 / 50000000000) : ℝ) = ((50000000000 / 202977545713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14810_neg : (703388201 / 500000000) ≤ -Real.log (62500000000 / 255173309851) ∧
    -Real.log (62500000000 / 255173309851) ≤ (281355281 / 200000000) := by
  have h := checkLog_sound (w := (5173309851 / 505173309851)) (n := 12)
    (lo := (10241021 / 500000000)) (hi := (20482043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255173309851 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(255173309851 / 250000000000) = 1/(62500000000 / 255173309851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14810 : Bounds (703388201 / 500000000) (281355281 / 200000000) (Real.log (255173309851 / 62500000000)) := by
  have h := reflection_log_14810_neg
  have he : Real.log (255173309851 / 62500000000) = -Real.log (62500000000 / 255173309851) := by
    rw [show ((255173309851 / 62500000000) : ℝ) = ((62500000000 / 255173309851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14811_neg : (3917648177 / 1000000000) ≤ -Real.log (20000000000 / 1005641025641) ∧
    -Real.log (20000000000 / 1005641025641) ≤ (3917648183 / 1000000000) := by
  have h := checkLog_sound (w := (365641025641 / 1645641025641)) (n := 12)
    (lo := (451912277 / 1000000000)) (hi := (225956139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1005641025641 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1005641025641 / 640000000000) = 1/(20000000000 / 1005641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14811 : Bounds (3917648177 / 1000000000) (3917648183 / 1000000000) (Real.log (1005641025641 / 20000000000)) := by
  have h := reflection_log_14811_neg
  have he : Real.log (1005641025641 / 20000000000) = -Real.log (20000000000 / 1005641025641) := by
    rw [show ((1005641025641 / 20000000000) : ℝ) = ((20000000000 / 1005641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14812_neg : (3944133477 / 1000000000) ≤ -Real.log (100000000000 / 5163157894737) ∧
    -Real.log (100000000000 / 5163157894737) ≤ (3944133483 / 1000000000) := by
  have h := checkLog_sound (w := (1963157894737 / 8363157894737)) (n := 12)
    (lo := (478397577 / 1000000000)) (hi := (239198789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5163157894737 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5163157894737 / 3200000000000) = 1/(100000000000 / 5163157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14812 : Bounds (3944133477 / 1000000000) (3944133483 / 1000000000) (Real.log (5163157894737 / 100000000000)) := by
  have h := reflection_log_14812_neg
  have he : Real.log (5163157894737 / 100000000000) = -Real.log (100000000000 / 5163157894737) := by
    rw [show ((5163157894737 / 100000000000) : ℝ) = ((100000000000 / 5163157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14813_neg : (134894783 / 200000000) ≤ -Real.log (1000 / 1963) ∧
    -Real.log (1000 / 1963) ≤ (168618479 / 250000000) := by
  have h := checkLog_sound (w := (963 / 2963)) (n := 12)
    (lo := (134894783 / 200000000)) (hi := (168618479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1000) = 1/(1000 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14813 : Bounds (134894783 / 200000000) (168618479 / 250000000) (Real.log (1963 / 1000)) := by
  have h := reflection_log_14813_neg
  have he : Real.log (1963 / 1000) = -Real.log (1000 / 1963) := by
    rw [show ((1963 / 1000) : ℝ) = ((1000 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14814_neg : (824209341 / 250000000) ≤ -Real.log (37 / 1000) ∧
    -Real.log (37 / 1000) ≤ (3296837369 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 74) = 1/(37 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14814 : Bounds (-3296837369 / 1000000000) (-824209341 / 250000000) (Real.log (37 / 1000)) := by
  have h := reflection_log_14814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14815_neg : (120317 / 125000000) ≤ -Real.log (1000000 / 1000963) ∧
    -Real.log (1000000 / 1000963) ≤ (962537 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 2000963)) (n := 12)
    (lo := (120317 / 125000000)) (hi := (962537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000963 / 1000000) = 1/(1000000 / 1000963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14815 : Bounds (120317 / 125000000) (962537 / 1000000000) (Real.log (1000963 / 1000000)) := by
  have h := reflection_log_14815_neg
  have he : Real.log (1000963 / 1000000) = -Real.log (1000000 / 1000963) := by
    rw [show ((1000963 / 1000000) : ℝ) = ((1000000 / 1000963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14816_neg : (963463 / 1000000000) ≤ -Real.log (999037 / 1000000) ∧
    -Real.log (999037 / 1000000) ≤ (120433 / 125000000) := by
  have h := checkLog_sound (w := (963 / 1999037)) (n := 12)
    (lo := (963463 / 1000000000)) (hi := (120433 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999037) = 1/(999037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14816 : Bounds (-120433 / 125000000) (-963463 / 1000000000) (Real.log (999037 / 1000000)) := by
  have h := reflection_log_14816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14817_neg : (473660061 / 1000000000) ≤ -Real.log (1000000 / 1605861) ∧
    -Real.log (1000000 / 1605861) ≤ (236830031 / 500000000) := by
  have h := checkLog_sound (w := (605861 / 2605861)) (n := 12)
    (lo := (473660061 / 1000000000)) (hi := (236830031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1605861 / 1000000) = 1/(1000000 / 1605861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14817 : Bounds (473660061 / 1000000000) (236830031 / 500000000) (Real.log (1605861 / 1000000)) := by
  have h := reflection_log_14817_neg
  have he : Real.log (1605861 / 1000000) = -Real.log (1000000 / 1605861) := by
    rw [show ((1605861 / 1000000) : ℝ) = ((1000000 / 1605861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14818_neg : (931051639 / 1000000000) ≤ -Real.log (394139 / 1000000) ∧
    -Real.log (394139 / 1000000) ≤ (931051641 / 1000000000) := by
  have h := checkLog_sound (w := (105861 / 894139)) (n := 12)
    (lo := (237904459 / 1000000000)) (hi := (11895223 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 394139) = 1/(394139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14818 : Bounds (-931051641 / 1000000000) (-931051639 / 1000000000) (Real.log (394139 / 1000000)) := by
  have h := reflection_log_14818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14819_neg : (474787791 / 1000000000) ≤ -Real.log (1000000 / 1607673) ∧
    -Real.log (1000000 / 1607673) ≤ (29674237 / 62500000) := by
  have h := checkLog_sound (w := (607673 / 2607673)) (n := 12)
    (lo := (474787791 / 1000000000)) (hi := (29674237 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1607673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1607673 / 1000000) = 1/(1000000 / 1607673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14819 : Bounds (474787791 / 1000000000) (29674237 / 62500000) (Real.log (1607673 / 1000000)) := by
  have h := reflection_log_14819_neg
  have he : Real.log (1607673 / 1000000) = -Real.log (1000000 / 1607673) := by
    rw [show ((1607673 / 1000000) : ℝ) = ((1000000 / 1607673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14820_neg : (467829801 / 500000000) ≤ -Real.log (392327 / 1000000) ∧
    -Real.log (392327 / 1000000) ≤ (233914901 / 250000000) := by
  have h := checkLog_sound (w := (107673 / 892327)) (n := 12)
    (lo := (121256211 / 500000000)) (hi := (242512423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 392327) = 1/(392327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14820 : Bounds (-233914901 / 250000000) (-467829801 / 500000000) (Real.log (392327 / 1000000)) := by
  have h := reflection_log_14820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14821_neg : (460871811 / 1000000000) ≤ -Real.log (630733525071 / 1000000000000) ∧
    -Real.log (630733525071 / 1000000000000) ≤ (115217953 / 250000000) := by
  have h := checkLog_sound (w := (369266474929 / 1630733525071)) (n := 12)
    (lo := (460871811 / 1000000000)) (hi := (115217953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 630733525071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 630733525071) = 1/(630733525071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14821 : Bounds (-115217953 / 250000000) (-460871811 / 1000000000) (Real.log (630733525071 / 1000000000000)) := by
  have h := reflection_log_14821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14822_neg : (228695789 / 500000000) ≤ -Real.log (632932448679 / 1000000000000) ∧
    -Real.log (632932448679 / 1000000000000) ≤ (457391579 / 1000000000) := by
  have h := checkLog_sound (w := (367067551321 / 1632932448679)) (n := 12)
    (lo := (228695789 / 500000000)) (hi := (457391579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 632932448679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 632932448679) = 1/(632932448679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14822 : Bounds (-457391579 / 1000000000) (-228695789 / 500000000) (Real.log (632932448679 / 1000000000000)) := by
  have h := reflection_log_14822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14823_neg : (14047117 / 10000000) ≤ -Real.log (500000000000 / 2037175970913) ∧
    -Real.log (500000000000 / 2037175970913) ≤ (1404711703 / 1000000000) := by
  have h := checkLog_sound (w := (37175970913 / 4037175970913)) (n := 12)
    (lo := (920867 / 50000000)) (hi := (18417341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2037175970913 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2037175970913 / 2000000000000) = 1/(500000000000 / 2037175970913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14823 : Bounds (14047117 / 10000000) (1404711703 / 1000000000) (Real.log (2037175970913 / 500000000000)) := by
  have h := reflection_log_14823_neg
  have he : Real.log (2037175970913 / 500000000000) = -Real.log (500000000000 / 2037175970913) := by
    rw [show ((2037175970913 / 500000000000) : ℝ) = ((500000000000 / 2037175970913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14824_neg : (705223697 / 500000000) ≤ -Real.log (125000000000 / 512223540567) ∧
    -Real.log (125000000000 / 512223540567) ≤ (1410447397 / 1000000000) := by
  have h := checkLog_sound (w := (12223540567 / 1012223540567)) (n := 12)
    (lo := (12076517 / 500000000)) (hi := (4830607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512223540567 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(512223540567 / 500000000000) = 1/(125000000000 / 512223540567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14824 : Bounds (705223697 / 500000000) (1410447397 / 1000000000) (Real.log (512223540567 / 125000000000)) := by
  have h := reflection_log_14824_neg
  have he : Real.log (512223540567 / 125000000000) = -Real.log (125000000000 / 512223540567) := by
    rw [show ((512223540567 / 125000000000) : ℝ) = ((125000000000 / 512223540567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14825_neg : (3944133477 / 1000000000) ≤ -Real.log (125000000000 / 6453947368421) ∧
    -Real.log (125000000000 / 6453947368421) ≤ (3944133483 / 1000000000) := by
  have h := checkLog_sound (w := (2453947368421 / 10453947368421)) (n := 12)
    (lo := (478397577 / 1000000000)) (hi := (239198789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453947368421 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6453947368421 / 4000000000000) = 1/(125000000000 / 6453947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14825 : Bounds (3944133477 / 1000000000) (3944133483 / 1000000000) (Real.log (6453947368421 / 125000000000)) := by
  have h := reflection_log_14825_neg
  have he : Real.log (6453947368421 / 125000000000) = -Real.log (125000000000 / 6453947368421) := by
    rw [show ((6453947368421 / 125000000000) : ℝ) = ((125000000000 / 6453947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14826_neg : (1985655639 / 500000000) ≤ -Real.log (125000000000 / 6631756756757) ∧
    -Real.log (125000000000 / 6631756756757) ≤ (992827821 / 250000000) := by
  have h := checkLog_sound (w := (2631756756757 / 10631756756757)) (n := 12)
    (lo := (252787689 / 500000000)) (hi := (505575379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631756756757 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6631756756757 / 4000000000000) = 1/(125000000000 / 6631756756757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14826 : Bounds (1985655639 / 500000000) (992827821 / 250000000) (Real.log (6631756756757 / 125000000000)) := by
  have h := reflection_log_14826_neg
  have he : Real.log (6631756756757 / 125000000000) = -Real.log (125000000000 / 6631756756757) := by
    rw [show ((6631756756757 / 125000000000) : ℝ) = ((125000000000 / 6631756756757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14827_neg : (674983209 / 1000000000) ≤ -Real.log (250 / 491) ∧
    -Real.log (250 / 491) ≤ (67498321 / 100000000) := by
  have h := checkLog_sound (w := (241 / 741)) (n := 12)
    (lo := (674983209 / 1000000000)) (hi := (67498321 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 250) = 1/(250 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14827 : Bounds (674983209 / 1000000000) (67498321 / 100000000) (Real.log (491 / 250)) := by
  have h := reflection_log_14827_neg
  have he : Real.log (491 / 250) = -Real.log (250 / 491) := by
    rw [show ((491 / 250) : ℝ) = ((250 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14828_neg : (1662118169 / 500000000) ≤ -Real.log (9 / 250) ∧
    -Real.log (9 / 250) ≤ (3324236343 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 72) = 1/(9 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14828 : Bounds (-3324236343 / 1000000000) (-1662118169 / 500000000) (Real.log (9 / 250)) := by
  have h := reflection_log_14828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14829_neg : (192707 / 200000000) ≤ -Real.log (250000 / 250241) ∧
    -Real.log (250000 / 250241) ≤ (60221 / 62500000) := by
  have h := checkLog_sound (w := (241 / 500241)) (n := 12)
    (lo := (192707 / 200000000)) (hi := (60221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250241 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250241 / 250000) = 1/(250000 / 250241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14829 : Bounds (192707 / 200000000) (60221 / 62500000) (Real.log (250241 / 250000)) := by
  have h := reflection_log_14829_neg
  have he : Real.log (250241 / 250000) = -Real.log (250000 / 250241) := by
    rw [show ((250241 / 250000) : ℝ) = ((250000 / 250241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14830_neg : (60279 / 62500000) ≤ -Real.log (249759 / 250000) ∧
    -Real.log (249759 / 250000) ≤ (192893 / 200000000) := by
  have h := checkLog_sound (w := (241 / 499759)) (n := 12)
    (lo := (60279 / 62500000)) (hi := (192893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249759) = 1/(249759 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14830 : Bounds (-192893 / 200000000) (-60279 / 62500000) (Real.log (249759 / 250000)) := by
  have h := reflection_log_14830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14831_neg : (118595383 / 250000000) ≤ -Real.log (50000 / 80351) ∧
    -Real.log (50000 / 80351) ≤ (474381533 / 1000000000) := by
  have h := checkLog_sound (w := (30351 / 130351)) (n := 12)
    (lo := (118595383 / 250000000)) (hi := (474381533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80351 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80351 / 50000) = 1/(50000 / 80351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14831 : Bounds (118595383 / 250000000) (474381533 / 1000000000) (Real.log (80351 / 50000)) := by
  have h := reflection_log_14831_neg
  have he : Real.log (80351 / 50000) = -Real.log (50000 / 80351) := by
    rw [show ((80351 / 50000) : ℝ) = ((50000 / 80351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14832_neg : (466998279 / 500000000) ≤ -Real.log (19649 / 50000) ∧
    -Real.log (19649 / 50000) ≤ (11674957 / 12500000) := by
  have h := checkLog_sound (w := (5351 / 44649)) (n := 12)
    (lo := (120424689 / 500000000)) (hi := (240849379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19649) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 19649) = 1/(19649 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14832 : Bounds (-11674957 / 12500000) (-466998279 / 500000000) (Real.log (19649 / 50000)) := by
  have h := reflection_log_14832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14833_neg : (475512179 / 1000000000) ≤ -Real.log (500000 / 804419) ∧
    -Real.log (500000 / 804419) ≤ (23775609 / 50000000) := by
  have h := checkLog_sound (w := (304419 / 1304419)) (n := 12)
    (lo := (475512179 / 1000000000)) (hi := (23775609 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804419 / 500000) = 1/(500000 / 804419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14833 : Bounds (475512179 / 1000000000) (23775609 / 50000000) (Real.log (804419 / 500000)) := by
  have h := reflection_log_14833_neg
  have he : Real.log (804419 / 500000) = -Real.log (500000 / 804419) := by
    rw [show ((804419 / 500000) : ℝ) = ((500000 / 804419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14834_neg : (938633481 / 1000000000) ≤ -Real.log (195581 / 500000) ∧
    -Real.log (195581 / 500000) ≤ (938633483 / 1000000000) := by
  have h := checkLog_sound (w := (54419 / 445581)) (n := 12)
    (lo := (245486301 / 1000000000)) (hi := (122743151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195581) = 1/(195581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14834 : Bounds (-938633483 / 1000000000) (-938633481 / 1000000000) (Real.log (195581 / 500000)) := by
  have h := reflection_log_14834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14835_neg : (463121303 / 1000000000) ≤ -Real.log (157329072439 / 250000000000) ∧
    -Real.log (157329072439 / 250000000000) ≤ (57890163 / 125000000) := by
  have h := checkLog_sound (w := (92670927561 / 407329072439)) (n := 12)
    (lo := (463121303 / 1000000000)) (hi := (57890163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157329072439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157329072439) = 1/(157329072439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14835 : Bounds (-57890163 / 125000000) (-463121303 / 1000000000) (Real.log (157329072439 / 250000000000)) := by
  have h := reflection_log_14835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14836_neg : (229807513 / 500000000) ≤ -Real.log (1578816799 / 2500000000) ∧
    -Real.log (1578816799 / 2500000000) ≤ (459615027 / 1000000000) := by
  have h := checkLog_sound (w := (921183201 / 4078816799)) (n := 12)
    (lo := (229807513 / 500000000)) (hi := (459615027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1578816799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1578816799) = 1/(1578816799 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14836 : Bounds (-459615027 / 1000000000) (-229807513 / 500000000) (Real.log (1578816799 / 2500000000)) := by
  have h := reflection_log_14836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14837_neg : (140837809 / 100000000) ≤ -Real.log (25000000000 / 102232938063) ∧
    -Real.log (25000000000 / 102232938063) ≤ (1408378093 / 1000000000) := by
  have h := checkLog_sound (w := (2232938063 / 202232938063)) (n := 12)
    (lo := (2208373 / 100000000)) (hi := (22083731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102232938063 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(102232938063 / 100000000000) = 1/(25000000000 / 102232938063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14837 : Bounds (140837809 / 100000000) (1408378093 / 1000000000) (Real.log (102232938063 / 25000000000)) := by
  have h := reflection_log_14837_neg
  have he : Real.log (102232938063 / 25000000000) = -Real.log (25000000000 / 102232938063) := by
    rw [show ((102232938063 / 25000000000) : ℝ) = ((25000000000 / 102232938063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14838_neg : (70707283 / 50000000) ≤ -Real.log (125000000000 / 514121387047) ∧
    -Real.log (125000000000 / 514121387047) ≤ (1414145663 / 1000000000) := by
  have h := checkLog_sound (w := (14121387047 / 1014121387047)) (n := 12)
    (lo := (278513 / 10000000)) (hi := (27851301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514121387047 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(514121387047 / 500000000000) = 1/(125000000000 / 514121387047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14838 : Bounds (70707283 / 50000000) (1414145663 / 1000000000) (Real.log (514121387047 / 125000000000)) := by
  have h := reflection_log_14838_neg
  have he : Real.log (514121387047 / 125000000000) = -Real.log (125000000000 / 514121387047) := by
    rw [show ((514121387047 / 125000000000) : ℝ) = ((125000000000 / 514121387047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14839_neg : (1985655639 / 500000000) ≤ -Real.log (500000000000 / 26527027027027) ∧
    -Real.log (500000000000 / 26527027027027) ≤ (992827821 / 250000000) := by
  have h := checkLog_sound (w := (10527027027027 / 42527027027027)) (n := 12)
    (lo := (252787689 / 500000000)) (hi := (505575379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26527027027027 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26527027027027 / 16000000000000) = 1/(500000000000 / 26527027027027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14839 : Bounds (1985655639 / 500000000) (992827821 / 250000000) (Real.log (26527027027027 / 500000000000)) := by
  have h := reflection_log_14839_neg
  have he : Real.log (26527027027027 / 500000000000) = -Real.log (500000000000 / 26527027027027) := by
    rw [show ((26527027027027 / 500000000000) : ℝ) = ((500000000000 / 26527027027027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14840_neg : (3999219547 / 1000000000) ≤ -Real.log (250000000000 / 13638888888889) ∧
    -Real.log (250000000000 / 13638888888889) ≤ (3999219553 / 1000000000) := by
  have h := checkLog_sound (w := (5638888888889 / 21638888888889)) (n := 12)
    (lo := (533483647 / 1000000000)) (hi := (4167841 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13638888888889 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13638888888889 / 8000000000000) = 1/(250000000000 / 13638888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14840 : Bounds (3999219547 / 1000000000) (3999219553 / 1000000000) (Real.log (13638888888889 / 250000000000)) := by
  have h := reflection_log_14840_neg
  have he : Real.log (13638888888889 / 250000000000) = -Real.log (250000000000 / 13638888888889) := by
    rw [show ((13638888888889 / 250000000000) : ℝ) = ((250000000000 / 13638888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14841_neg : (135098449 / 200000000) ≤ -Real.log (200 / 393) ∧
    -Real.log (200 / 393) ≤ (337746123 / 500000000) := by
  have h := checkLog_sound (w := (193 / 593)) (n := 12)
    (lo := (135098449 / 200000000)) (hi := (337746123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 200) = 1/(200 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14841 : Bounds (135098449 / 200000000) (337746123 / 500000000) (Real.log (393 / 200)) := by
  have h := reflection_log_14841_neg
  have he : Real.log (393 / 200) = -Real.log (200 / 393) := by
    rw [show ((393 / 200) : ℝ) = ((200 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14842_neg : (670481443 / 200000000) ≤ -Real.log (7 / 200) ∧
    -Real.log (7 / 200) ≤ (167620361 / 50000000) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 14) = 1/(7 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14842 : Bounds (-167620361 / 50000000) (-670481443 / 200000000) (Real.log (7 / 200)) := by
  have h := reflection_log_14842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14843_neg : (482267 / 500000000) ≤ -Real.log (200000 / 200193) ∧
    -Real.log (200000 / 200193) ≤ (192907 / 200000000) := by
  have h := checkLog_sound (w := (193 / 400193)) (n := 12)
    (lo := (482267 / 500000000)) (hi := (192907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200193 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200193 / 200000) = 1/(200000 / 200193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14843 : Bounds (482267 / 500000000) (192907 / 200000000) (Real.log (200193 / 200000)) := by
  have h := reflection_log_14843_neg
  have he : Real.log (200193 / 200000) = -Real.log (200000 / 200193) := by
    rw [show ((200193 / 200000) : ℝ) = ((200000 / 200193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14844_neg : (193093 / 200000000) ≤ -Real.log (199807 / 200000) ∧
    -Real.log (199807 / 200000) ≤ (482733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 399807)) (n := 12)
    (lo := (193093 / 200000000)) (hi := (482733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199807) = 1/(199807 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14844 : Bounds (-482733 / 500000000) (-193093 / 200000000) (Real.log (199807 / 200000)) := by
  have h := reflection_log_14844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14845_neg : (95021367 / 200000000) ≤ -Real.log (500000 / 804093) ∧
    -Real.log (500000 / 804093) ≤ (118776709 / 250000000) := by
  have h := checkLog_sound (w := (304093 / 1304093)) (n := 12)
    (lo := (95021367 / 200000000)) (hi := (118776709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804093 / 500000) = 1/(500000 / 804093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14845 : Bounds (95021367 / 200000000) (118776709 / 250000000) (Real.log (804093 / 500000)) := by
  have h := reflection_log_14845_neg
  have he : Real.log (804093 / 500000) = -Real.log (500000 / 804093) := by
    rw [show ((804093 / 500000) : ℝ) = ((500000 / 804093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14846_neg : (936968041 / 1000000000) ≤ -Real.log (195907 / 500000) ∧
    -Real.log (195907 / 500000) ≤ (936968043 / 1000000000) := by
  have h := checkLog_sound (w := (54093 / 445907)) (n := 12)
    (lo := (243820861 / 1000000000)) (hi := (121910431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195907) = 1/(195907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14846 : Bounds (-936968043 / 1000000000) (-936968041 / 1000000000) (Real.log (195907 / 500000)) := by
  have h := reflection_log_14846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14847_neg : (476239769 / 1000000000) ≤ -Real.log (1000000 / 1610009) ∧
    -Real.log (1000000 / 1610009) ≤ (47623977 / 100000000) := by
  have h := checkLog_sound (w := (610009 / 2610009)) (n := 12)
    (lo := (476239769 / 1000000000)) (hi := (47623977 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1610009 / 1000000) = 1/(1000000 / 1610009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14847 : Bounds (476239769 / 1000000000) (47623977 / 100000000) (Real.log (1610009 / 1000000)) := by
  have h := reflection_log_14847_neg
  have he : Real.log (1610009 / 1000000) = -Real.log (1000000 / 1610009) := by
    rw [show ((1610009 / 1000000) : ℝ) = ((1000000 / 1610009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
