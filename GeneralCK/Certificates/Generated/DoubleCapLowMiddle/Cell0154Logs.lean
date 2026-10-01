import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0154
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

theorem reflection_log_1_neg : (32516469 / 50000000) ≤ -Real.log (12800 / 24527) ∧
    -Real.log (12800 / 24527) ≤ (650329381 / 1000000000) := by
  have h := checkLog_sound (w := (11727 / 37327)) (n := 12)
    (lo := (32516469 / 50000000)) (hi := (650329381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24527 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24527 / 12800) = 1/(12800 / 24527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32516469 / 50000000) (650329381 / 1000000000) (Real.log (24527 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24527 / 12800) = -Real.log (12800 / 24527) := by
    rw [show ((24527 / 12800) : ℝ) = ((12800 / 24527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (495797341 / 200000000) ≤ -Real.log (1073 / 12800) ∧
    -Real.log (1073 / 12800) ≤ (2478986709 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1073) = 1/(1073 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2478986709 / 1000000000) (-495797341 / 200000000) (Real.log (1073 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (649554423 / 1000000000) ≤ -Real.log (3200 / 6127) ∧
    -Real.log (3200 / 6127) ≤ (81194303 / 125000000) := by
  have h := checkLog_sound (w := (2927 / 9327)) (n := 12)
    (lo := (649554423 / 1000000000)) (hi := (81194303 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6127 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6127 / 3200) = 1/(3200 / 6127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (649554423 / 1000000000) (81194303 / 125000000) (Real.log (6127 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6127 / 3200) = -Real.log (3200 / 6127) := by
    rw [show ((6127 / 3200) : ℝ) = ((3200 / 6127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2461434291 / 1000000000) ≤ -Real.log (273 / 3200) ∧
    -Real.log (273 / 3200) ≤ (492286859 / 200000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 273) = 1/(273 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-492286859 / 200000000) (-2461434291 / 1000000000) (Real.log (273 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121119177 / 200000000) ≤ -Real.log (6400 / 11727) ∧
    -Real.log (6400 / 11727) ≤ (302797943 / 500000000) := by
  have h := checkLog_sound (w := (5327 / 18127)) (n := 12)
    (lo := (121119177 / 200000000)) (hi := (302797943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11727 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11727 / 6400) = 1/(6400 / 11727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121119177 / 200000000) (302797943 / 500000000) (Real.log (11727 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11727 / 6400) = -Real.log (6400 / 11727) := by
    rw [show ((11727 / 6400) : ℝ) = ((6400 / 11727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71433581 / 40000000) ≤ -Real.log (1073 / 6400) ∧
    -Real.log (1073 / 6400) ≤ (223229941 / 125000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1073) = 1/(1073 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-223229941 / 125000000) (-71433581 / 40000000) (Real.log (1073 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (301987189 / 500000000) ≤ -Real.log (1600 / 2927) ∧
    -Real.log (1600 / 2927) ≤ (603974379 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 4527)) (n := 12)
    (lo := (301987189 / 500000000)) (hi := (603974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 1600) = 1/(1600 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (301987189 / 500000000) (603974379 / 1000000000) (Real.log (2927 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2927 / 1600) = -Real.log (1600 / 2927) := by
    rw [show ((2927 / 1600) : ℝ) = ((1600 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1768287111 / 1000000000) ≤ -Real.log (273 / 1600) ∧
    -Real.log (273 / 1600) ≤ (884143557 / 500000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 273) = 1/(273 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-884143557 / 500000000) (-1768287111 / 1000000000) (Real.log (273 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (659357691 / 1000000000) ≤ -Real.log (20000 / 38671) ∧
    -Real.log (20000 / 38671) ≤ (164839423 / 250000000) := by
  have h := checkLog_sound (w := (18671 / 58671)) (n := 12)
    (lo := (659357691 / 1000000000)) (hi := (164839423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38671 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38671 / 20000) = 1/(20000 / 38671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (659357691 / 1000000000) (164839423 / 250000000) (Real.log (38671 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (38671 / 20000) = -Real.log (20000 / 38671) := by
    rw [show ((38671 / 20000) : ℝ) = ((20000 / 38671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (677826373 / 250000000) ≤ -Real.log (1329 / 20000) ∧
    -Real.log (1329 / 20000) ≤ (338913187 / 125000000) := by
  have h := checkLog_sound (w := (1171 / 3829)) (n := 12)
    (lo := (39491497 / 62500000)) (hi := (631863953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2500 / 1329) = 1/(1329 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-338913187 / 125000000) (-677826373 / 250000000) (Real.log (1329 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20621861 / 31250000) ≤ -Real.log (500000 / 967299) ∧
    -Real.log (500000 / 967299) ≤ (659899553 / 1000000000) := by
  have h := checkLog_sound (w := (467299 / 1467299)) (n := 12)
    (lo := (20621861 / 31250000)) (hi := (659899553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967299 / 500000) = 1/(500000 / 967299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20621861 / 31250000) (659899553 / 1000000000) (Real.log (967299 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (967299 / 500000) = -Real.log (500000 / 967299) := by
    rw [show ((967299 / 500000) : ℝ) = ((500000 / 967299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1363601219 / 500000000) ≤ -Real.log (32701 / 500000) ∧
    -Real.log (32701 / 500000) ≤ (1363601221 / 500000000) := by
  have h := checkLog_sound (w := (29799 / 95201)) (n := 12)
    (lo := (323880449 / 500000000)) (hi := (647760899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32701) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 32701) = 1/(32701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1363601221 / 500000000) (-1363601219 / 500000000) (Real.log (32701 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (329255869 / 500000000) ≤ -Real.log (200000 / 386383) ∧
    -Real.log (200000 / 386383) ≤ (658511739 / 1000000000) := by
  have h := checkLog_sound (w := (186383 / 586383)) (n := 12)
    (lo := (329255869 / 500000000)) (hi := (658511739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386383 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386383 / 200000) = 1/(200000 / 386383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (329255869 / 500000000) (658511739 / 1000000000) (Real.log (386383 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (386383 / 200000) = -Real.log (200000 / 386383) := by
    rw [show ((386383 / 200000) : ℝ) = ((200000 / 386383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (167937397 / 62500000) ≤ -Real.log (13617 / 200000) ∧
    -Real.log (13617 / 200000) ≤ (671749589 / 250000000) := by
  have h := checkLog_sound (w := (11383 / 38617)) (n := 12)
    (lo := (151889203 / 250000000)) (hi := (607556813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 13617) = 1/(13617 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-671749589 / 250000000) (-167937397 / 62500000) (Real.log (13617 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131817537 / 200000000) ≤ -Real.log (250000 / 483257) ∧
    -Real.log (250000 / 483257) ≤ (329543843 / 500000000) := by
  have h := checkLog_sound (w := (233257 / 733257)) (n := 12)
    (lo := (131817537 / 200000000)) (hi := (329543843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483257 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483257 / 250000) = 1/(250000 / 483257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131817537 / 200000000) (329543843 / 500000000) (Real.log (483257 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (483257 / 250000) = -Real.log (250000 / 483257) := by
    rw [show ((483257 / 250000) : ℝ) = ((250000 / 483257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (540696131 / 200000000) ≤ -Real.log (16743 / 250000) ∧
    -Real.log (16743 / 250000) ≤ (2703480659 / 1000000000) := by
  have h := checkLog_sound (w := (14507 / 47993)) (n := 12)
    (lo := (124807823 / 200000000)) (hi := (156009779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16743) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 16743) = 1/(16743 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2703480659 / 1000000000) (-540696131 / 200000000) (Real.log (16743 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3370663183 / 1000000000) ≤ -Real.log (5000000000 / 145489089541) ∧
    -Real.log (5000000000 / 145489089541) ≤ (842665797 / 250000000) := by
  have h := checkLog_sound (w := (65489089541 / 225489089541)) (n := 12)
    (lo := (598074463 / 1000000000)) (hi := (18689827 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145489089541 / 80000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(145489089541 / 80000000000) = 1/(5000000000 / 145489089541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3370663183 / 1000000000) (842665797 / 250000000) (Real.log (145489089541 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145489089541 / 5000000000) = -Real.log (5000000000 / 145489089541) := by
    rw [show ((145489089541 / 5000000000) : ℝ) = ((5000000000 / 145489089541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338710199 / 100000000) ≤ -Real.log (500000000000 / 14790052291979) ∧
    -Real.log (500000000000 / 14790052291979) ≤ (677420399 / 200000000) := by
  have h := checkLog_sound (w := (6790052291979 / 22790052291979)) (n := 12)
    (lo := (61451327 / 100000000)) (hi := (614513271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14790052291979 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14790052291979 / 8000000000000) = 1/(500000000000 / 14790052291979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338710199 / 100000000) (677420399 / 200000000) (Real.log (14790052291979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14790052291979 / 500000000000) = -Real.log (500000000000 / 14790052291979) := by
    rw [show ((14790052291979 / 500000000000) : ℝ) = ((500000000000 / 14790052291979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3345510091 / 1000000000) ≤ -Real.log (250000000000 / 7093761474627) ∧
    -Real.log (250000000000 / 7093761474627) ≤ (209094381 / 62500000) := by
  have h := checkLog_sound (w := (3093761474627 / 11093761474627)) (n := 12)
    (lo := (572921371 / 1000000000)) (hi := (143230343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093761474627 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7093761474627 / 4000000000000) = 1/(250000000000 / 7093761474627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3345510091 / 1000000000) (209094381 / 62500000) (Real.log (7093761474627 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7093761474627 / 250000000000) = -Real.log (250000000000 / 7093761474627) := by
    rw [show ((7093761474627 / 250000000000) : ℝ) = ((250000000000 / 7093761474627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (168128417 / 50000000) ≤ -Real.log (125000000000 / 3607903302873) ∧
    -Real.log (125000000000 / 3607903302873) ≤ (672513669 / 200000000) := by
  have h := checkLog_sound (w := (1607903302873 / 5607903302873)) (n := 12)
    (lo := (29498981 / 50000000)) (hi := (589979621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3607903302873 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3607903302873 / 2000000000000) = 1/(125000000000 / 3607903302873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (168128417 / 50000000) (672513669 / 200000000) (Real.log (3607903302873 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3607903302873 / 125000000000) = -Real.log (125000000000 / 3607903302873) := by
    rw [show ((3607903302873 / 125000000000) : ℝ) = ((125000000000 / 3607903302873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0154
