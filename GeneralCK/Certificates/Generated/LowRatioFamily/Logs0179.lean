import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11456_neg : (6159121 / 25000000) ≤ -Real.log (781637 / 1000000) ∧
    -Real.log (781637 / 1000000) ≤ (246364841 / 1000000000) := by
  have h := checkLog_sound (w := (218363 / 1781637)) (n := 12)
    (lo := (6159121 / 25000000)) (hi := (246364841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781637) = 1/(781637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11456 : Bounds (-246364841 / 1000000000) (-6159121 / 25000000) (Real.log (781637 / 1000000)) := by
  have h := reflection_log_11456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11457_neg : (24428343 / 500000000) ≤ -Real.log (952317600231 / 1000000000000) ∧
    -Real.log (952317600231 / 1000000000000) ≤ (48856687 / 1000000000) := by
  have h := checkLog_sound (w := (47682399769 / 1952317600231)) (n := 12)
    (lo := (24428343 / 500000000)) (hi := (48856687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952317600231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952317600231) = 1/(952317600231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11457 : Bounds (-48856687 / 1000000000) (-24428343 / 500000000) (Real.log (952317600231 / 1000000000000)) := by
  have h := reflection_log_11457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11458_neg : (12104261 / 250000000) ≤ -Real.log (238184092599 / 250000000000) ∧
    -Real.log (238184092599 / 250000000000) ≤ (9683409 / 200000000) := by
  have h := checkLog_sound (w := (11815907401 / 488184092599)) (n := 12)
    (lo := (12104261 / 250000000)) (hi := (9683409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238184092599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238184092599) = 1/(238184092599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11458 : Bounds (-9683409 / 200000000) (-12104261 / 250000000) (Real.log (238184092599 / 250000000000)) := by
  have h := reflection_log_11458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11459_neg : (110463801 / 250000000) ≤ -Real.log (500000000000 / 777795240979) ∧
    -Real.log (500000000000 / 777795240979) ≤ (88371041 / 200000000) := by
  have h := checkLog_sound (w := (277795240979 / 1277795240979)) (n := 12)
    (lo := (110463801 / 250000000)) (hi := (88371041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777795240979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777795240979 / 500000000000) = 1/(500000000000 / 777795240979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11459 : Bounds (110463801 / 250000000) (88371041 / 200000000) (Real.log (777795240979 / 500000000000)) := by
  have h := reflection_log_11459_neg
  have he : Real.log (777795240979 / 500000000000) = -Real.log (500000000000 / 777795240979) := by
    rw [show ((777795240979 / 500000000000) : ℝ) = ((500000000000 / 777795240979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11460_neg : (88774599 / 200000000) ≤ -Real.log (500000000000 / 779366253133) ∧
    -Real.log (500000000000 / 779366253133) ≤ (110968249 / 250000000) := by
  have h := checkLog_sound (w := (279366253133 / 1279366253133)) (n := 12)
    (lo := (88774599 / 200000000)) (hi := (110968249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779366253133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779366253133 / 500000000000) = 1/(500000000000 / 779366253133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11460 : Bounds (88774599 / 200000000) (110968249 / 250000000) (Real.log (779366253133 / 500000000000)) := by
  have h := reflection_log_11460_neg
  have he : Real.log (779366253133 / 500000000000) = -Real.log (500000000000 / 779366253133) := by
    rw [show ((779366253133 / 500000000000) : ℝ) = ((500000000000 / 779366253133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11461_neg : (897813649 / 1000000000) ≤ -Real.log (500000000000 / 1227115716753) ∧
    -Real.log (500000000000 / 1227115716753) ≤ (897813651 / 1000000000) := by
  have h := checkLog_sound (w := (227115716753 / 2227115716753)) (n := 12)
    (lo := (204666469 / 1000000000)) (hi := (20466647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227115716753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1227115716753 / 1000000000000) = 1/(500000000000 / 1227115716753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11461 : Bounds (897813649 / 1000000000) (897813651 / 1000000000) (Real.log (1227115716753 / 500000000000)) := by
  have h := reflection_log_11461_neg
  have he : Real.log (1227115716753 / 500000000000) = -Real.log (500000000000 / 1227115716753) := by
    rw [show ((1227115716753 / 500000000000) : ℝ) = ((500000000000 / 1227115716753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11462_neg : (900245741 / 1000000000) ≤ -Real.log (500000000000 / 1230103806229) ∧
    -Real.log (500000000000 / 1230103806229) ≤ (900245743 / 1000000000) := by
  have h := checkLog_sound (w := (230103806229 / 2230103806229)) (n := 12)
    (lo := (207098561 / 1000000000)) (hi := (103549281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230103806229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1230103806229 / 1000000000000) = 1/(500000000000 / 1230103806229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11462 : Bounds (900245741 / 1000000000) (900245743 / 1000000000) (Real.log (1230103806229 / 500000000000)) := by
  have h := reflection_log_11462_neg
  have he : Real.log (1230103806229 / 500000000000) = -Real.log (500000000000 / 1230103806229) := by
    rw [show ((1230103806229 / 500000000000) : ℝ) = ((500000000000 / 1230103806229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11463_neg : (352767319 / 1000000000) ≤ -Real.log (1000 / 1423) ∧
    -Real.log (1000 / 1423) ≤ (8819183 / 25000000) := by
  have h := checkLog_sound (w := (423 / 2423)) (n := 12)
    (lo := (352767319 / 1000000000)) (hi := (8819183 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1423 / 1000) = 1/(1000 / 1423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11463 : Bounds (352767319 / 1000000000) (8819183 / 25000000) (Real.log (1423 / 1000)) := by
  have h := reflection_log_11463_neg
  have he : Real.log (1423 / 1000) = -Real.log (1000 / 1423) := by
    rw [show ((1423 / 1000) : ℝ) = ((1000 / 1423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11464_neg : (137478253 / 250000000) ≤ -Real.log (577 / 1000) ∧
    -Real.log (577 / 1000) ≤ (549913013 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 1577)) (n := 12)
    (lo := (137478253 / 250000000)) (hi := (549913013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 577) = 1/(577 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11464 : Bounds (-549913013 / 1000000000) (-137478253 / 250000000) (Real.log (577 / 1000)) := by
  have h := reflection_log_11464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11465_neg : (42291 / 100000000) ≤ -Real.log (1000000 / 1000423) ∧
    -Real.log (1000000 / 1000423) ≤ (422911 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 2000423)) (n := 12)
    (lo := (42291 / 100000000)) (hi := (422911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000423 / 1000000) = 1/(1000000 / 1000423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11465 : Bounds (42291 / 100000000) (422911 / 1000000000) (Real.log (1000423 / 1000000)) := by
  have h := reflection_log_11465_neg
  have he : Real.log (1000423 / 1000000) = -Real.log (1000000 / 1000423) := by
    rw [show ((1000423 / 1000000) : ℝ) = ((1000000 / 1000423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11466_neg : (423089 / 1000000000) ≤ -Real.log (999577 / 1000000) ∧
    -Real.log (999577 / 1000000) ≤ (42309 / 100000000) := by
  have h := checkLog_sound (w := (423 / 1999577)) (n := 12)
    (lo := (423089 / 1000000000)) (hi := (42309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999577) = 1/(999577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11466 : Bounds (-42309 / 100000000) (-423089 / 1000000000) (Real.log (999577 / 1000000)) := by
  have h := reflection_log_11466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11467_neg : (98586611 / 500000000) ≤ -Real.log (200000 / 243591) ∧
    -Real.log (200000 / 243591) ≤ (197173223 / 1000000000) := by
  have h := checkLog_sound (w := (43591 / 443591)) (n := 12)
    (lo := (98586611 / 500000000)) (hi := (197173223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243591 / 200000) = 1/(200000 / 243591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11467 : Bounds (98586611 / 500000000) (197173223 / 1000000000) (Real.log (243591 / 200000)) := by
  have h := reflection_log_11467_neg
  have he : Real.log (243591 / 200000) = -Real.log (200000 / 243591) := by
    rw [show ((243591 / 200000) : ℝ) = ((200000 / 243591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11468_neg : (49168599 / 200000000) ≤ -Real.log (156409 / 200000) ∧
    -Real.log (156409 / 200000) ≤ (61460749 / 250000000) := by
  have h := checkLog_sound (w := (43591 / 356409)) (n := 12)
    (lo := (49168599 / 200000000)) (hi := (61460749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156409) = 1/(156409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11468 : Bounds (-61460749 / 250000000) (-49168599 / 200000000) (Real.log (156409 / 200000)) := by
  have h := reflection_log_11468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11469_neg : (197961939 / 1000000000) ≤ -Real.log (250000 / 304729) ∧
    -Real.log (250000 / 304729) ≤ (9898097 / 50000000) := by
  have h := checkLog_sound (w := (54729 / 554729)) (n := 12)
    (lo := (197961939 / 1000000000)) (hi := (9898097 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304729 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304729 / 250000) = 1/(250000 / 304729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11469 : Bounds (197961939 / 1000000000) (9898097 / 50000000) (Real.log (304729 / 250000)) := by
  have h := reflection_log_11469_neg
  have he : Real.log (304729 / 250000) = -Real.log (250000 / 304729) := by
    rw [show ((304729 / 250000) : ℝ) = ((250000 / 304729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11470_neg : (12353629 / 50000000) ≤ -Real.log (195271 / 250000) ∧
    -Real.log (195271 / 250000) ≤ (247072581 / 1000000000) := by
  have h := checkLog_sound (w := (54729 / 445271)) (n := 12)
    (lo := (12353629 / 50000000)) (hi := (247072581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195271) = 1/(195271 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11470 : Bounds (-247072581 / 1000000000) (-12353629 / 50000000) (Real.log (195271 / 250000)) := by
  have h := reflection_log_11470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11471_neg : (49110641 / 1000000000) ≤ -Real.log (59504736559 / 62500000000) ∧
    -Real.log (59504736559 / 62500000000) ≤ (24555321 / 500000000) := by
  have h := checkLog_sound (w := (2995263441 / 122004736559)) (n := 12)
    (lo := (49110641 / 1000000000)) (hi := (24555321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59504736559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59504736559) = 1/(59504736559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11471 : Bounds (-24555321 / 500000000) (-49110641 / 1000000000) (Real.log (59504736559 / 62500000000)) := by
  have h := reflection_log_11471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11472_neg : (12167443 / 250000000) ≤ -Real.log (38099824719 / 40000000000) ∧
    -Real.log (38099824719 / 40000000000) ≤ (48669773 / 1000000000) := by
  have h := checkLog_sound (w := (1900175281 / 78099824719)) (n := 12)
    (lo := (12167443 / 250000000)) (hi := (48669773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38099824719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38099824719) = 1/(38099824719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11472 : Bounds (-48669773 / 1000000000) (-12167443 / 250000000) (Real.log (38099824719 / 40000000000)) := by
  have h := reflection_log_11472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11473_neg : (221508109 / 500000000) ≤ -Real.log (100000000000 / 155739759221) ∧
    -Real.log (100000000000 / 155739759221) ≤ (443016219 / 1000000000) := by
  have h := checkLog_sound (w := (55739759221 / 255739759221)) (n := 12)
    (lo := (221508109 / 500000000)) (hi := (443016219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155739759221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155739759221 / 100000000000) = 1/(100000000000 / 155739759221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11473 : Bounds (221508109 / 500000000) (443016219 / 1000000000) (Real.log (155739759221 / 100000000000)) := by
  have h := reflection_log_11473_neg
  have he : Real.log (155739759221 / 100000000000) = -Real.log (100000000000 / 155739759221) := by
    rw [show ((155739759221 / 100000000000) : ℝ) = ((100000000000 / 155739759221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11474_neg : (445034519 / 1000000000) ≤ -Real.log (250000000000 / 390136016101) ∧
    -Real.log (250000000000 / 390136016101) ≤ (11125863 / 25000000) := by
  have h := checkLog_sound (w := (140136016101 / 640136016101)) (n := 12)
    (lo := (445034519 / 1000000000)) (hi := (11125863 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390136016101 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390136016101 / 250000000000) = 1/(250000000000 / 390136016101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11474 : Bounds (445034519 / 1000000000) (11125863 / 25000000) (Real.log (390136016101 / 250000000000)) := by
  have h := reflection_log_11474_neg
  have he : Real.log (390136016101 / 250000000000) = -Real.log (250000000000 / 390136016101) := by
    rw [show ((390136016101 / 250000000000) : ℝ) = ((250000000000 / 390136016101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11475_neg : (900245741 / 1000000000) ≤ -Real.log (125000000000 / 307525951557) ∧
    -Real.log (125000000000 / 307525951557) ≤ (900245743 / 1000000000) := by
  have h := checkLog_sound (w := (57525951557 / 557525951557)) (n := 12)
    (lo := (207098561 / 1000000000)) (hi := (103549281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307525951557 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307525951557 / 250000000000) = 1/(125000000000 / 307525951557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11475 : Bounds (900245741 / 1000000000) (900245743 / 1000000000) (Real.log (307525951557 / 125000000000)) := by
  have h := reflection_log_11475_neg
  have he : Real.log (307525951557 / 125000000000) = -Real.log (125000000000 / 307525951557) := by
    rw [show ((307525951557 / 125000000000) : ℝ) = ((125000000000 / 307525951557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11476_neg : (902680331 / 1000000000) ≤ -Real.log (500000000000 / 1233102253033) ∧
    -Real.log (500000000000 / 1233102253033) ≤ (902680333 / 1000000000) := by
  have h := checkLog_sound (w := (233102253033 / 2233102253033)) (n := 12)
    (lo := (209533151 / 1000000000)) (hi := (6547911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233102253033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1233102253033 / 1000000000000) = 1/(500000000000 / 1233102253033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11476 : Bounds (902680331 / 1000000000) (902680333 / 1000000000) (Real.log (1233102253033 / 500000000000)) := by
  have h := reflection_log_11476_neg
  have he : Real.log (1233102253033 / 500000000000) = -Real.log (500000000000 / 1233102253033) := by
    rw [show ((1233102253033 / 500000000000) : ℝ) = ((500000000000 / 1233102253033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11477_neg : (88367453 / 250000000) ≤ -Real.log (125 / 178) ∧
    -Real.log (125 / 178) ≤ (353469813 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 303)) (n := 12)
    (lo := (88367453 / 250000000)) (hi := (353469813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178 / 125) = 1/(125 / 178) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11477 : Bounds (88367453 / 250000000) (353469813 / 1000000000) (Real.log (178 / 125)) := by
  have h := reflection_log_11477_neg
  have he : Real.log (178 / 125) = -Real.log (125 / 178) := by
    rw [show ((178 / 125) : ℝ) = ((125 / 178) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11478_neg : (275823809 / 500000000) ≤ -Real.log (72 / 125) ∧
    -Real.log (72 / 125) ≤ (551647619 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 72) = 1/(72 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11478 : Bounds (-551647619 / 1000000000) (-275823809 / 500000000) (Real.log (72 / 125)) := by
  have h := reflection_log_11478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11479_neg : (42391 / 100000000) ≤ -Real.log (125000 / 125053) ∧
    -Real.log (125000 / 125053) ≤ (423911 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 250053)) (n := 12)
    (lo := (42391 / 100000000)) (hi := (423911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125053 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125053 / 125000) = 1/(125000 / 125053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11479 : Bounds (42391 / 100000000) (423911 / 1000000000) (Real.log (125053 / 125000)) := by
  have h := reflection_log_11479_neg
  have he : Real.log (125053 / 125000) = -Real.log (125000 / 125053) := by
    rw [show ((125053 / 125000) : ℝ) = ((125000 / 125053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11480_neg : (424089 / 1000000000) ≤ -Real.log (124947 / 125000) ∧
    -Real.log (124947 / 125000) ≤ (42409 / 100000000) := by
  have h := checkLog_sound (w := (53 / 249947)) (n := 12)
    (lo := (424089 / 1000000000)) (hi := (42409 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124947) = 1/(124947 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11480 : Bounds (-42409 / 100000000) (-424089 / 1000000000) (Real.log (124947 / 125000)) := by
  have h := reflection_log_11480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11481_neg : (98813169 / 500000000) ≤ -Real.log (1000000 / 1218507) ∧
    -Real.log (1000000 / 1218507) ≤ (197626339 / 1000000000) := by
  have h := checkLog_sound (w := (218507 / 2218507)) (n := 12)
    (lo := (98813169 / 500000000)) (hi := (197626339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218507 / 1000000) = 1/(1000000 / 1218507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11481 : Bounds (98813169 / 500000000) (197626339 / 1000000000) (Real.log (1218507 / 1000000)) := by
  have h := reflection_log_11481_neg
  have he : Real.log (1218507 / 1000000) = -Real.log (1000000 / 1218507) := by
    rw [show ((1218507 / 1000000) : ℝ) = ((1000000 / 1218507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11482_neg : (123274543 / 500000000) ≤ -Real.log (781493 / 1000000) ∧
    -Real.log (781493 / 1000000) ≤ (246549087 / 1000000000) := by
  have h := checkLog_sound (w := (218507 / 1781493)) (n := 12)
    (lo := (123274543 / 500000000)) (hi := (246549087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781493) = 1/(781493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11482 : Bounds (-246549087 / 1000000000) (-123274543 / 500000000) (Real.log (781493 / 1000000)) := by
  have h := reflection_log_11482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11483_neg : (99208169 / 500000000) ≤ -Real.log (100000 / 121947) ∧
    -Real.log (100000 / 121947) ≤ (198416339 / 1000000000) := by
  have h := checkLog_sound (w := (21947 / 221947)) (n := 12)
    (lo := (99208169 / 500000000)) (hi := (198416339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121947 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121947 / 100000) = 1/(100000 / 121947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11483 : Bounds (99208169 / 500000000) (198416339 / 1000000000) (Real.log (121947 / 100000)) := by
  have h := reflection_log_11483_neg
  have he : Real.log (121947 / 100000) = -Real.log (100000 / 121947) := by
    rw [show ((121947 / 100000) : ℝ) = ((100000 / 121947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11484_neg : (123891051 / 500000000) ≤ -Real.log (78053 / 100000) ∧
    -Real.log (78053 / 100000) ≤ (247782103 / 1000000000) := by
  have h := checkLog_sound (w := (21947 / 178053)) (n := 12)
    (lo := (123891051 / 500000000)) (hi := (247782103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78053) = 1/(78053 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11484 : Bounds (-247782103 / 1000000000) (-123891051 / 500000000) (Real.log (78053 / 100000)) := by
  have h := reflection_log_11484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11485_neg : (12341441 / 250000000) ≤ -Real.log (9518329191 / 10000000000) ∧
    -Real.log (9518329191 / 10000000000) ≤ (9873153 / 200000000) := by
  have h := checkLog_sound (w := (481670809 / 19518329191)) (n := 12)
    (lo := (12341441 / 250000000)) (hi := (9873153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9518329191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9518329191) = 1/(9518329191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11485 : Bounds (-9873153 / 200000000) (-12341441 / 250000000) (Real.log (9518329191 / 10000000000)) := by
  have h := reflection_log_11485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11486_neg : (48922747 / 1000000000) ≤ -Real.log (952254690951 / 1000000000000) ∧
    -Real.log (952254690951 / 1000000000000) ≤ (12230687 / 250000000) := by
  have h := checkLog_sound (w := (47745309049 / 1952254690951)) (n := 12)
    (lo := (48922747 / 1000000000)) (hi := (12230687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952254690951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952254690951) = 1/(952254690951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11486 : Bounds (-12230687 / 250000000) (-48922747 / 1000000000) (Real.log (952254690951 / 1000000000000)) := by
  have h := reflection_log_11486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11487_neg : (17767017 / 40000000) ≤ -Real.log (125000000000 / 194900498149) ∧
    -Real.log (125000000000 / 194900498149) ≤ (222087713 / 500000000) := by
  have h := checkLog_sound (w := (69900498149 / 319900498149)) (n := 12)
    (lo := (17767017 / 40000000)) (hi := (222087713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194900498149 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194900498149 / 125000000000) = 1/(125000000000 / 194900498149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11487 : Bounds (17767017 / 40000000) (222087713 / 500000000) (Real.log (194900498149 / 125000000000)) := by
  have h := reflection_log_11487_neg
  have he : Real.log (194900498149 / 125000000000) = -Real.log (125000000000 / 194900498149) := by
    rw [show ((194900498149 / 125000000000) : ℝ) = ((125000000000 / 194900498149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11488_neg : (11154961 / 25000000) ≤ -Real.log (500000000000 / 781180736167) ∧
    -Real.log (500000000000 / 781180736167) ≤ (446198441 / 1000000000) := by
  have h := checkLog_sound (w := (281180736167 / 1281180736167)) (n := 12)
    (lo := (11154961 / 25000000)) (hi := (446198441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781180736167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781180736167 / 500000000000) = 1/(500000000000 / 781180736167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11488 : Bounds (11154961 / 25000000) (446198441 / 1000000000) (Real.log (781180736167 / 500000000000)) := by
  have h := reflection_log_11488_neg
  have he : Real.log (781180736167 / 500000000000) = -Real.log (500000000000 / 781180736167) := by
    rw [show ((781180736167 / 500000000000) : ℝ) = ((500000000000 / 781180736167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11489_neg : (902680331 / 1000000000) ≤ -Real.log (62500000000 / 154137781629) ∧
    -Real.log (62500000000 / 154137781629) ≤ (902680333 / 1000000000) := by
  have h := checkLog_sound (w := (29137781629 / 279137781629)) (n := 12)
    (lo := (209533151 / 1000000000)) (hi := (6547911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154137781629 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154137781629 / 125000000000) = 1/(62500000000 / 154137781629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11489 : Bounds (902680331 / 1000000000) (902680333 / 1000000000) (Real.log (154137781629 / 62500000000)) := by
  have h := reflection_log_11489_neg
  have he : Real.log (154137781629 / 62500000000) = -Real.log (62500000000 / 154137781629) := by
    rw [show ((154137781629 / 62500000000) : ℝ) = ((62500000000 / 154137781629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11490_neg : (90511743 / 100000000) ≤ -Real.log (62500000000 / 154513888889) ∧
    -Real.log (62500000000 / 154513888889) ≤ (113139679 / 125000000) := by
  have h := checkLog_sound (w := (29513888889 / 279513888889)) (n := 12)
    (lo := (847881 / 4000000)) (hi := (211970251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154513888889 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154513888889 / 125000000000) = 1/(62500000000 / 154513888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11490 : Bounds (90511743 / 100000000) (113139679 / 125000000) (Real.log (154513888889 / 62500000000)) := by
  have h := reflection_log_11490_neg
  have he : Real.log (154513888889 / 62500000000) = -Real.log (62500000000 / 154513888889) := by
    rw [show ((154513888889 / 62500000000) : ℝ) = ((62500000000 / 154513888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11491_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
    -Real.log (40 / 57) ≤ (177085907 / 500000000) := by
  have h := checkLog_sound (w := (17 / 97)) (n := 12)
    (lo := (354171813 / 1000000000)) (hi := (177085907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57 / 40) = 1/(40 / 57) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11491 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_11491_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11492_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
    -Real.log (23 / 40) ≤ (553385239 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 63)) (n := 12)
    (lo := (276692619 / 500000000)) (hi := (553385239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 23) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 23) = 1/(23 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11492 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_11492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11493_neg : (424909 / 1000000000) ≤ -Real.log (40000 / 40017) ∧
    -Real.log (40000 / 40017) ≤ (42491 / 100000000) := by
  have h := checkLog_sound (w := (17 / 80017)) (n := 12)
    (lo := (424909 / 1000000000)) (hi := (42491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40017 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40017 / 40000) = 1/(40000 / 40017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11493 : Bounds (424909 / 1000000000) (42491 / 100000000) (Real.log (40017 / 40000)) := by
  have h := reflection_log_11493_neg
  have he : Real.log (40017 / 40000) = -Real.log (40000 / 40017) := by
    rw [show ((40017 / 40000) : ℝ) = ((40000 / 40017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11494_neg : (42509 / 100000000) ≤ -Real.log (39983 / 40000) ∧
    -Real.log (39983 / 40000) ≤ (425091 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 79983)) (n := 12)
    (lo := (42509 / 100000000)) (hi := (425091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39983) = 1/(39983 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11494 : Bounds (-425091 / 1000000000) (-42509 / 100000000) (Real.log (39983 / 40000)) := by
  have h := reflection_log_11494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11495_neg : (198080069 / 1000000000) ≤ -Real.log (50000 / 60953) ∧
    -Real.log (50000 / 60953) ≤ (19808007 / 100000000) := by
  have h := checkLog_sound (w := (10953 / 110953)) (n := 12)
    (lo := (198080069 / 1000000000)) (hi := (19808007 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60953 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60953 / 50000) = 1/(50000 / 60953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11495 : Bounds (198080069 / 1000000000) (19808007 / 100000000) (Real.log (60953 / 50000)) := by
  have h := reflection_log_11495_neg
  have he : Real.log (60953 / 50000) = -Real.log (50000 / 60953) := by
    rw [show ((60953 / 50000) : ℝ) = ((50000 / 60953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11496_neg : (61814239 / 250000000) ≤ -Real.log (39047 / 50000) ∧
    -Real.log (39047 / 50000) ≤ (247256957 / 1000000000) := by
  have h := checkLog_sound (w := (10953 / 89047)) (n := 12)
    (lo := (61814239 / 250000000)) (hi := (247256957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39047) = 1/(39047 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11496 : Bounds (-247256957 / 1000000000) (-61814239 / 250000000) (Real.log (39047 / 50000)) := by
  have h := reflection_log_11496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11497_neg : (19887053 / 100000000) ≤ -Real.log (125000 / 152503) ∧
    -Real.log (125000 / 152503) ≤ (198870531 / 1000000000) := by
  have h := checkLog_sound (w := (27503 / 277503)) (n := 12)
    (lo := (19887053 / 100000000)) (hi := (198870531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152503 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152503 / 125000) = 1/(125000 / 152503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11497 : Bounds (19887053 / 100000000) (198870531 / 1000000000) (Real.log (152503 / 125000)) := by
  have h := reflection_log_11497_neg
  have he : Real.log (152503 / 125000) = -Real.log (125000 / 152503) := by
    rw [show ((152503 / 125000) : ℝ) = ((125000 / 152503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11498_neg : (248492129 / 1000000000) ≤ -Real.log (97497 / 125000) ∧
    -Real.log (97497 / 125000) ≤ (24849213 / 100000000) := by
  have h := checkLog_sound (w := (27503 / 222497)) (n := 12)
    (lo := (248492129 / 1000000000)) (hi := (24849213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97497) = 1/(97497 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11498 : Bounds (-24849213 / 100000000) (-248492129 / 1000000000) (Real.log (97497 / 125000)) := by
  have h := reflection_log_11498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11499_neg : (24810799 / 500000000) ≤ -Real.log (14868584991 / 15625000000) ∧
    -Real.log (14868584991 / 15625000000) ≤ (49621599 / 1000000000) := by
  have h := checkLog_sound (w := (756415009 / 30493584991)) (n := 12)
    (lo := (24810799 / 500000000)) (hi := (49621599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14868584991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14868584991) = 1/(14868584991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11499 : Bounds (-49621599 / 1000000000) (-24810799 / 500000000) (Real.log (14868584991 / 15625000000)) := by
  have h := reflection_log_11499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11500_neg : (24588443 / 500000000) ≤ -Real.log (2380031791 / 2500000000) ∧
    -Real.log (2380031791 / 2500000000) ≤ (49176887 / 1000000000) := by
  have h := checkLog_sound (w := (119968209 / 4880031791)) (n := 12)
    (lo := (24588443 / 500000000)) (hi := (49176887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2380031791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2380031791) = 1/(2380031791 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11500 : Bounds (-49176887 / 1000000000) (-24588443 / 500000000) (Real.log (2380031791 / 2500000000)) := by
  have h := reflection_log_11500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11501_neg : (222668513 / 500000000) ≤ -Real.log (31250000000 / 48781756601) ∧
    -Real.log (31250000000 / 48781756601) ≤ (445337027 / 1000000000) := by
  have h := checkLog_sound (w := (17531756601 / 80031756601)) (n := 12)
    (lo := (222668513 / 500000000)) (hi := (445337027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48781756601 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48781756601 / 31250000000) = 1/(31250000000 / 48781756601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11501 : Bounds (222668513 / 500000000) (445337027 / 1000000000) (Real.log (48781756601 / 31250000000)) := by
  have h := reflection_log_11501_neg
  have he : Real.log (48781756601 / 31250000000) = -Real.log (31250000000 / 48781756601) := by
    rw [show ((48781756601 / 31250000000) : ℝ) = ((31250000000 / 48781756601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11502_neg : (447362659 / 1000000000) ≤ -Real.log (500000000000 / 782090730997) ∧
    -Real.log (500000000000 / 782090730997) ≤ (22368133 / 50000000) := by
  have h := checkLog_sound (w := (282090730997 / 1282090730997)) (n := 12)
    (lo := (447362659 / 1000000000)) (hi := (22368133 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782090730997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782090730997 / 500000000000) = 1/(500000000000 / 782090730997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11502 : Bounds (447362659 / 1000000000) (22368133 / 50000000) (Real.log (782090730997 / 500000000000)) := by
  have h := reflection_log_11502_neg
  have he : Real.log (782090730997 / 500000000000) = -Real.log (500000000000 / 782090730997) := by
    rw [show ((782090730997 / 500000000000) : ℝ) = ((500000000000 / 782090730997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11503_neg : (90511743 / 100000000) ≤ -Real.log (500000000000 / 1236111111111) ∧
    -Real.log (500000000000 / 1236111111111) ≤ (113139679 / 125000000) := by
  have h := checkLog_sound (w := (236111111111 / 2236111111111)) (n := 12)
    (lo := (847881 / 4000000)) (hi := (211970251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236111111111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1236111111111 / 1000000000000) = 1/(500000000000 / 1236111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11503 : Bounds (90511743 / 100000000) (113139679 / 125000000) (Real.log (1236111111111 / 500000000000)) := by
  have h := reflection_log_11503_neg
  have he : Real.log (1236111111111 / 500000000000) = -Real.log (500000000000 / 1236111111111) := by
    rw [show ((1236111111111 / 500000000000) : ℝ) = ((500000000000 / 1236111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11504_neg : (907557051 / 1000000000) ≤ -Real.log (500000000000 / 1239130434783) ∧
    -Real.log (500000000000 / 1239130434783) ≤ (907557053 / 1000000000) := by
  have h := checkLog_sound (w := (239130434783 / 2239130434783)) (n := 12)
    (lo := (214409871 / 1000000000)) (hi := (13400617 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239130434783 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1239130434783 / 1000000000000) = 1/(500000000000 / 1239130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11504 : Bounds (907557051 / 1000000000) (907557053 / 1000000000) (Real.log (1239130434783 / 500000000000)) := by
  have h := reflection_log_11504_neg
  have he : Real.log (1239130434783 / 500000000000) = -Real.log (500000000000 / 1239130434783) := by
    rw [show ((1239130434783 / 500000000000) : ℝ) = ((500000000000 / 1239130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11505_neg : (354873321 / 1000000000) ≤ -Real.log (500 / 713) ∧
    -Real.log (500 / 713) ≤ (177436661 / 500000000) := by
  have h := checkLog_sound (w := (213 / 1213)) (n := 12)
    (lo := (354873321 / 1000000000)) (hi := (177436661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713 / 500) = 1/(500 / 713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11505 : Bounds (354873321 / 1000000000) (177436661 / 500000000) (Real.log (713 / 500)) := by
  have h := reflection_log_11505_neg
  have he : Real.log (713 / 500) = -Real.log (500 / 713) := by
    rw [show ((713 / 500) : ℝ) = ((500 / 713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11506_neg : (277562941 / 500000000) ≤ -Real.log (287 / 500) ∧
    -Real.log (287 / 500) ≤ (555125883 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 287) = 1/(287 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11506 : Bounds (-555125883 / 1000000000) (-277562941 / 500000000) (Real.log (287 / 500)) := by
  have h := reflection_log_11506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11507_neg : (425909 / 1000000000) ≤ -Real.log (500000 / 500213) ∧
    -Real.log (500000 / 500213) ≤ (42591 / 100000000) := by
  have h := checkLog_sound (w := (213 / 1000213)) (n := 12)
    (lo := (425909 / 1000000000)) (hi := (42591 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500213 / 500000) = 1/(500000 / 500213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11507 : Bounds (425909 / 1000000000) (42591 / 100000000) (Real.log (500213 / 500000)) := by
  have h := reflection_log_11507_neg
  have he : Real.log (500213 / 500000) = -Real.log (500000 / 500213) := by
    rw [show ((500213 / 500000) : ℝ) = ((500000 / 500213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11508_neg : (42609 / 100000000) ≤ -Real.log (499787 / 500000) ∧
    -Real.log (499787 / 500000) ≤ (426091 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 999787)) (n := 12)
    (lo := (42609 / 100000000)) (hi := (426091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499787) = 1/(499787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11508 : Bounds (-426091 / 1000000000) (-42609 / 100000000) (Real.log (499787 / 500000)) := by
  have h := reflection_log_11508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11509_neg : (39706719 / 200000000) ≤ -Real.log (1000000 / 1219613) ∧
    -Real.log (1000000 / 1219613) ≤ (49633399 / 250000000) := by
  have h := checkLog_sound (w := (219613 / 2219613)) (n := 12)
    (lo := (39706719 / 200000000)) (hi := (49633399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219613 / 1000000) = 1/(1000000 / 1219613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11509 : Bounds (39706719 / 200000000) (49633399 / 250000000) (Real.log (1219613 / 1000000)) := by
  have h := reflection_log_11509_neg
  have he : Real.log (1219613 / 1000000) = -Real.log (1000000 / 1219613) := by
    rw [show ((1219613 / 1000000) : ℝ) = ((1000000 / 1219613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11510_neg : (15497833 / 62500000) ≤ -Real.log (780387 / 1000000) ∧
    -Real.log (780387 / 1000000) ≤ (247965329 / 1000000000) := by
  have h := checkLog_sound (w := (219613 / 1780387)) (n := 12)
    (lo := (15497833 / 62500000)) (hi := (247965329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780387) = 1/(780387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11510 : Bounds (-247965329 / 1000000000) (-15497833 / 62500000) (Real.log (780387 / 1000000)) := by
  have h := reflection_log_11510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11511_neg : (199324517 / 1000000000) ≤ -Real.log (500000 / 610289) ∧
    -Real.log (500000 / 610289) ≤ (99662259 / 500000000) := by
  have h := checkLog_sound (w := (110289 / 1110289)) (n := 12)
    (lo := (199324517 / 1000000000)) (hi := (99662259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610289 / 500000) = 1/(500000 / 610289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11511 : Bounds (199324517 / 1000000000) (99662259 / 500000000) (Real.log (610289 / 500000)) := by
  have h := reflection_log_11511_neg
  have he : Real.log (610289 / 500000) = -Real.log (500000 / 610289) := by
    rw [show ((610289 / 500000) : ℝ) = ((500000 / 610289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11512_neg : (249202659 / 1000000000) ≤ -Real.log (389711 / 500000) ∧
    -Real.log (389711 / 500000) ≤ (12460133 / 50000000) := by
  have h := checkLog_sound (w := (110289 / 889711)) (n := 12)
    (lo := (249202659 / 1000000000)) (hi := (12460133 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389711) = 1/(389711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11512 : Bounds (-12460133 / 50000000) (-249202659 / 1000000000) (Real.log (389711 / 500000)) := by
  have h := reflection_log_11512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11513_neg : (24939071 / 500000000) ≤ -Real.log (237836336479 / 250000000000) ∧
    -Real.log (237836336479 / 250000000000) ≤ (49878143 / 1000000000) := by
  have h := checkLog_sound (w := (12163663521 / 487836336479)) (n := 12)
    (lo := (24939071 / 500000000)) (hi := (49878143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237836336479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237836336479) = 1/(237836336479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11513 : Bounds (-49878143 / 1000000000) (-24939071 / 500000000) (Real.log (237836336479 / 250000000000)) := by
  have h := reflection_log_11513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11514_neg : (49431733 / 1000000000) ≤ -Real.log (951770130231 / 1000000000000) ∧
    -Real.log (951770130231 / 1000000000000) ≤ (24715867 / 500000000) := by
  have h := checkLog_sound (w := (48229869769 / 1951770130231)) (n := 12)
    (lo := (49431733 / 1000000000)) (hi := (24715867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951770130231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951770130231) = 1/(951770130231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11514 : Bounds (-24715867 / 500000000) (-49431733 / 1000000000) (Real.log (951770130231 / 1000000000000)) := by
  have h := reflection_log_11514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11515_neg : (446498923 / 1000000000) ≤ -Real.log (500000000000 / 781415502821) ∧
    -Real.log (500000000000 / 781415502821) ≤ (111624731 / 250000000) := by
  have h := checkLog_sound (w := (281415502821 / 1281415502821)) (n := 12)
    (lo := (446498923 / 1000000000)) (hi := (111624731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781415502821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781415502821 / 500000000000) = 1/(500000000000 / 781415502821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11515 : Bounds (446498923 / 1000000000) (111624731 / 250000000) (Real.log (781415502821 / 500000000000)) := by
  have h := reflection_log_11515_neg
  have he : Real.log (781415502821 / 500000000000) = -Real.log (500000000000 / 781415502821) := by
    rw [show ((781415502821 / 500000000000) : ℝ) = ((500000000000 / 781415502821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11516_neg : (56065897 / 125000000) ≤ -Real.log (250000000000 / 391501009723) ∧
    -Real.log (250000000000 / 391501009723) ≤ (448527177 / 1000000000) := by
  have h := checkLog_sound (w := (141501009723 / 641501009723)) (n := 12)
    (lo := (56065897 / 125000000)) (hi := (448527177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391501009723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391501009723 / 250000000000) = 1/(250000000000 / 391501009723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11516 : Bounds (56065897 / 125000000) (448527177 / 1000000000) (Real.log (391501009723 / 250000000000)) := by
  have h := reflection_log_11516_neg
  have he : Real.log (391501009723 / 250000000000) = -Real.log (250000000000 / 391501009723) := by
    rw [show ((391501009723 / 250000000000) : ℝ) = ((250000000000 / 391501009723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11517_neg : (907557051 / 1000000000) ≤ -Real.log (250000000000 / 619565217391) ∧
    -Real.log (250000000000 / 619565217391) ≤ (907557053 / 1000000000) := by
  have h := checkLog_sound (w := (119565217391 / 1119565217391)) (n := 12)
    (lo := (214409871 / 1000000000)) (hi := (13400617 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619565217391 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(619565217391 / 500000000000) = 1/(250000000000 / 619565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11517 : Bounds (907557051 / 1000000000) (907557053 / 1000000000) (Real.log (619565217391 / 250000000000)) := by
  have h := reflection_log_11517_neg
  have he : Real.log (619565217391 / 250000000000) = -Real.log (250000000000 / 619565217391) := by
    rw [show ((619565217391 / 250000000000) : ℝ) = ((250000000000 / 619565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11518_neg : (227499801 / 250000000) ≤ -Real.log (250000000000 / 621080139373) ∧
    -Real.log (250000000000 / 621080139373) ≤ (454999603 / 500000000) := by
  have h := checkLog_sound (w := (121080139373 / 1121080139373)) (n := 12)
    (lo := (27106503 / 125000000)) (hi := (8674081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621080139373 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(621080139373 / 500000000000) = 1/(250000000000 / 621080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11518 : Bounds (227499801 / 250000000) (454999603 / 500000000) (Real.log (621080139373 / 250000000000)) := by
  have h := reflection_log_11518_neg
  have he : Real.log (621080139373 / 250000000000) = -Real.log (250000000000 / 621080139373) := by
    rw [show ((621080139373 / 250000000000) : ℝ) = ((250000000000 / 621080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11519_neg : (177787169 / 500000000) ≤ -Real.log (1000 / 1427) ∧
    -Real.log (1000 / 1427) ≤ (355574339 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2427)) (n := 12)
    (lo := (177787169 / 500000000)) (hi := (355574339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1000) = 1/(1000 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11519 : Bounds (177787169 / 500000000) (355574339 / 1000000000) (Real.log (1427 / 1000)) := by
  have h := reflection_log_11519_neg
  have he : Real.log (1427 / 1000) = -Real.log (1000 / 1427) := by
    rw [show ((1427 / 1000) : ℝ) = ((1000 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
