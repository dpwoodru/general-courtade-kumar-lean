import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_384_neg : (40009937 / 500000000) ≤ -Real.log (461549 / 500000) ∧
    -Real.log (461549 / 500000) ≤ (640159 / 8000000) := by
  have h := checkLog_sound (w := (38451 / 961549)) (n := 12)
    (lo := (40009937 / 500000000)) (hi := (640159 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461549) = 1/(461549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_384 : Bounds (-640159 / 8000000) (-40009937 / 500000000) (Real.log (461549 / 500000)) := by
  have h := reflection_log_384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_385_neg : (2965737 / 500000000) ≤ -Real.log (248521520599 / 250000000000) ∧
    -Real.log (248521520599 / 250000000000) ≤ (237259 / 40000000) := by
  have h := checkLog_sound (w := (1478479401 / 498521520599)) (n := 12)
    (lo := (2965737 / 500000000)) (hi := (237259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248521520599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248521520599) = 1/(248521520599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_385 : Bounds (-237259 / 40000000) (-2965737 / 500000000) (Real.log (248521520599 / 250000000000)) := by
  have h := reflection_log_385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_386_neg : (5899953 / 1000000000) ≤ -Real.log (248529354199 / 250000000000) ∧
    -Real.log (248529354199 / 250000000000) ≤ (2949977 / 500000000) := by
  have h := checkLog_sound (w := (1470645801 / 498529354199)) (n := 12)
    (lo := (5899953 / 1000000000)) (hi := (2949977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248529354199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248529354199) = 1/(248529354199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_386 : Bounds (-2949977 / 500000000) (-5899953 / 1000000000) (Real.log (248529354199 / 250000000000)) := by
  have h := reflection_log_386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_387_neg : (76848927 / 500000000) ≤ -Real.log (500000000000 / 583069244949) ∧
    -Real.log (500000000000 / 583069244949) ≤ (30739571 / 200000000) := by
  have h := checkLog_sound (w := (83069244949 / 1083069244949)) (n := 12)
    (lo := (76848927 / 500000000)) (hi := (30739571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583069244949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583069244949 / 500000000000) = 1/(500000000000 / 583069244949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_387 : Bounds (76848927 / 500000000) (30739571 / 200000000) (Real.log (583069244949 / 500000000000)) := by
  have h := reflection_log_387_neg
  have he : Real.log (583069244949 / 500000000000) = -Real.log (500000000000 / 583069244949) := by
    rw [show ((583069244949 / 500000000000) : ℝ) = ((500000000000 / 583069244949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_388_neg : (6164331 / 40000000) ≤ -Real.log (125000000000 / 145827149447) ∧
    -Real.log (125000000000 / 145827149447) ≤ (38527069 / 250000000) := by
  have h := checkLog_sound (w := (20827149447 / 270827149447)) (n := 12)
    (lo := (6164331 / 40000000)) (hi := (38527069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145827149447 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145827149447 / 125000000000) = 1/(125000000000 / 145827149447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_388 : Bounds (6164331 / 40000000) (38527069 / 250000000) (Real.log (145827149447 / 125000000000)) := by
  have h := reflection_log_388_neg
  have he : Real.log (145827149447 / 125000000000) = -Real.log (125000000000 / 145827149447) := by
    rw [show ((145827149447 / 125000000000) : ℝ) = ((125000000000 / 145827149447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_389_neg : (154108517 / 500000000) ≤ -Real.log (500000000000 / 680498170227) ∧
    -Real.log (500000000000 / 680498170227) ≤ (61643407 / 200000000) := by
  have h := checkLog_sound (w := (180498170227 / 1180498170227)) (n := 12)
    (lo := (154108517 / 500000000)) (hi := (61643407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680498170227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680498170227 / 500000000000) = 1/(500000000000 / 680498170227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_389 : Bounds (154108517 / 500000000) (61643407 / 200000000) (Real.log (680498170227 / 500000000000)) := by
  have h := reflection_log_389_neg
  have he : Real.log (680498170227 / 500000000000) = -Real.log (500000000000 / 680498170227) := by
    rw [show ((680498170227 / 500000000000) : ℝ) = ((500000000000 / 680498170227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_390_neg : (12336873 / 40000000) ≤ -Real.log (250000000000 / 340318772137) ∧
    -Real.log (250000000000 / 340318772137) ≤ (154210913 / 500000000) := by
  have h := checkLog_sound (w := (90318772137 / 590318772137)) (n := 12)
    (lo := (12336873 / 40000000)) (hi := (154210913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340318772137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340318772137 / 250000000000) = 1/(250000000000 / 340318772137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_390 : Bounds (12336873 / 40000000) (154210913 / 500000000) (Real.log (340318772137 / 250000000000)) := by
  have h := reflection_log_390_neg
  have he : Real.log (340318772137 / 250000000000) = -Real.log (250000000000 / 340318772137) := by
    rw [show ((340318772137 / 250000000000) : ℝ) = ((250000000000 / 340318772137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_391_neg : (142453967 / 1000000000) ≤ -Real.log (10000 / 11531) ∧
    -Real.log (10000 / 11531) ≤ (8903373 / 62500000) := by
  have h := checkLog_sound (w := (1531 / 21531)) (n := 12)
    (lo := (142453967 / 1000000000)) (hi := (8903373 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11531 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11531 / 10000) = 1/(10000 / 11531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_391 : Bounds (142453967 / 1000000000) (8903373 / 62500000) (Real.log (11531 / 10000)) := by
  have h := reflection_log_391_neg
  have he : Real.log (11531 / 10000) = -Real.log (10000 / 11531) := by
    rw [show ((11531 / 10000) : ℝ) = ((10000 / 11531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_392_neg : (33234531 / 200000000) ≤ -Real.log (8469 / 10000) ∧
    -Real.log (8469 / 10000) ≤ (10385791 / 62500000) := by
  have h := checkLog_sound (w := (1531 / 18469)) (n := 12)
    (lo := (33234531 / 200000000)) (hi := (10385791 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8469) = 1/(8469 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_392 : Bounds (-10385791 / 62500000) (-33234531 / 200000000) (Real.log (8469 / 10000)) := by
  have h := reflection_log_392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_393_neg : (299 / 1953125) ≤ -Real.log (10000000 / 10001531) ∧
    -Real.log (10000000 / 10001531) ≤ (153089 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 20001531)) (n := 12)
    (lo := (299 / 1953125)) (hi := (153089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001531 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001531 / 10000000) = 1/(10000000 / 10001531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_393 : Bounds (299 / 1953125) (153089 / 1000000000) (Real.log (10001531 / 10000000)) := by
  have h := reflection_log_393_neg
  have he : Real.log (10001531 / 10000000) = -Real.log (10000000 / 10001531) := by
    rw [show ((10001531 / 10000000) : ℝ) = ((10000000 / 10001531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_394_neg : (153111 / 1000000000) ≤ -Real.log (9998469 / 10000000) ∧
    -Real.log (9998469 / 10000000) ≤ (19139 / 125000000) := by
  have h := checkLog_sound (w := (1531 / 19998469)) (n := 12)
    (lo := (153111 / 1000000000)) (hi := (19139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998469) = 1/(9998469 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_394 : Bounds (-19139 / 125000000) (-153111 / 1000000000) (Real.log (9998469 / 10000000)) := by
  have h := reflection_log_394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_395_neg : (73945387 / 1000000000) ≤ -Real.log (250000 / 269187) ∧
    -Real.log (250000 / 269187) ≤ (18486347 / 250000000) := by
  have h := checkLog_sound (w := (19187 / 519187)) (n := 12)
    (lo := (73945387 / 1000000000)) (hi := (18486347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269187 / 250000) = 1/(250000 / 269187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_395 : Bounds (73945387 / 1000000000) (18486347 / 250000000) (Real.log (269187 / 250000)) := by
  have h := reflection_log_395_neg
  have he : Real.log (269187 / 250000) = -Real.log (250000 / 269187) := by
    rw [show ((269187 / 250000) : ℝ) = ((250000 / 269187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_396_neg : (39926529 / 500000000) ≤ -Real.log (230813 / 250000) ∧
    -Real.log (230813 / 250000) ≤ (79853059 / 1000000000) := by
  have h := checkLog_sound (w := (19187 / 480813)) (n := 12)
    (lo := (39926529 / 500000000)) (hi := (79853059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230813) = 1/(230813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_396 : Bounds (-79853059 / 1000000000) (-39926529 / 500000000) (Real.log (230813 / 250000)) := by
  have h := reflection_log_396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_397_neg : (74135757 / 1000000000) ≤ -Real.log (1000000 / 1076953) ∧
    -Real.log (1000000 / 1076953) ≤ (37067879 / 500000000) := by
  have h := checkLog_sound (w := (76953 / 2076953)) (n := 12)
    (lo := (74135757 / 1000000000)) (hi := (37067879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076953 / 1000000) = 1/(1000000 / 1076953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_397 : Bounds (74135757 / 1000000000) (37067879 / 500000000) (Real.log (1076953 / 1000000)) := by
  have h := reflection_log_397_neg
  have he : Real.log (1076953 / 1000000) = -Real.log (1000000 / 1076953) := by
    rw [show ((1076953 / 1000000) : ℝ) = ((1000000 / 1076953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_398_neg : (20018781 / 250000000) ≤ -Real.log (923047 / 1000000) ∧
    -Real.log (923047 / 1000000) ≤ (640601 / 8000000) := by
  have h := checkLog_sound (w := (76953 / 1923047)) (n := 12)
    (lo := (20018781 / 250000000)) (hi := (640601 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923047) = 1/(923047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_398 : Bounds (-640601 / 8000000) (-20018781 / 250000000) (Real.log (923047 / 1000000)) := by
  have h := reflection_log_398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_399_neg : (5939367 / 1000000000) ≤ -Real.log (994078235791 / 1000000000000) ∧
    -Real.log (994078235791 / 1000000000000) ≤ (742421 / 125000000) := by
  have h := checkLog_sound (w := (5921764209 / 1994078235791)) (n := 12)
    (lo := (5939367 / 1000000000)) (hi := (742421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994078235791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994078235791) = 1/(994078235791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_399 : Bounds (-742421 / 125000000) (-5939367 / 1000000000) (Real.log (994078235791 / 1000000000000)) := by
  have h := reflection_log_399_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_400_neg : (5907671 / 1000000000) ≤ -Real.log (62131859031 / 62500000000) ∧
    -Real.log (62131859031 / 62500000000) ≤ (738459 / 125000000) := by
  have h := checkLog_sound (w := (368140969 / 124631859031)) (n := 12)
    (lo := (5907671 / 1000000000)) (hi := (738459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62131859031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62131859031) = 1/(62131859031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_400 : Bounds (-738459 / 125000000) (-5907671 / 1000000000) (Real.log (62131859031 / 62500000000)) := by
  have h := reflection_log_400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_401_neg : (76899223 / 500000000) ≤ -Real.log (250000000000 / 291563950037) ∧
    -Real.log (250000000000 / 291563950037) ≤ (153798447 / 1000000000) := by
  have h := checkLog_sound (w := (41563950037 / 541563950037)) (n := 12)
    (lo := (76899223 / 500000000)) (hi := (153798447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291563950037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291563950037 / 250000000000) = 1/(250000000000 / 291563950037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_401 : Bounds (76899223 / 500000000) (153798447 / 1000000000) (Real.log (291563950037 / 250000000000)) := by
  have h := reflection_log_401_neg
  have he : Real.log (291563950037 / 250000000000) = -Real.log (250000000000 / 291563950037) := by
    rw [show ((291563950037 / 250000000000) : ℝ) = ((250000000000 / 291563950037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_402_neg : (77105441 / 500000000) ≤ -Real.log (31250000000 / 36460528283) ∧
    -Real.log (31250000000 / 36460528283) ≤ (154210883 / 1000000000) := by
  have h := checkLog_sound (w := (5210528283 / 67710528283)) (n := 12)
    (lo := (77105441 / 500000000)) (hi := (154210883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36460528283 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36460528283 / 31250000000) = 1/(31250000000 / 36460528283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_402 : Bounds (77105441 / 500000000) (154210883 / 1000000000) (Real.log (36460528283 / 31250000000)) := by
  have h := reflection_log_402_neg
  have he : Real.log (36460528283 / 31250000000) = -Real.log (31250000000 / 36460528283) := by
    rw [show ((36460528283 / 31250000000) : ℝ) = ((31250000000 / 36460528283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_403_neg : (12336873 / 40000000) ≤ -Real.log (500000000000 / 680637544273) ∧
    -Real.log (500000000000 / 680637544273) ≤ (154210913 / 500000000) := by
  have h := checkLog_sound (w := (180637544273 / 1180637544273)) (n := 12)
    (lo := (12336873 / 40000000)) (hi := (154210913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680637544273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680637544273 / 500000000000) = 1/(500000000000 / 680637544273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_403 : Bounds (12336873 / 40000000) (154210913 / 500000000) (Real.log (680637544273 / 500000000000)) := by
  have h := reflection_log_403_neg
  have he : Real.log (680637544273 / 500000000000) = -Real.log (500000000000 / 680637544273) := by
    rw [show ((680637544273 / 500000000000) : ℝ) = ((500000000000 / 680637544273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_404_neg : (154313311 / 500000000) ≤ -Real.log (250000000000 / 340388475617) ∧
    -Real.log (250000000000 / 340388475617) ≤ (308626623 / 1000000000) := by
  have h := checkLog_sound (w := (90388475617 / 590388475617)) (n := 12)
    (lo := (154313311 / 500000000)) (hi := (308626623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340388475617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340388475617 / 250000000000) = 1/(250000000000 / 340388475617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_404 : Bounds (154313311 / 500000000) (308626623 / 1000000000) (Real.log (340388475617 / 250000000000)) := by
  have h := reflection_log_404_neg
  have he : Real.log (340388475617 / 250000000000) = -Real.log (250000000000 / 340388475617) := by
    rw [show ((340388475617 / 250000000000) : ℝ) = ((250000000000 / 340388475617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_405_neg : (71270343 / 500000000) ≤ -Real.log (2500 / 2883) ∧
    -Real.log (2500 / 2883) ≤ (142540687 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 5383)) (n := 12)
    (lo := (71270343 / 500000000)) (hi := (142540687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 2500) = 1/(2500 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_405 : Bounds (71270343 / 500000000) (142540687 / 1000000000) (Real.log (2883 / 2500)) := by
  have h := reflection_log_405_neg
  have he : Real.log (2883 / 2500) = -Real.log (2500 / 2883) := by
    rw [show ((2883 / 2500) : ℝ) = ((2500 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_406_neg : (166290739 / 1000000000) ≤ -Real.log (2117 / 2500) ∧
    -Real.log (2117 / 2500) ≤ (8314537 / 50000000) := by
  have h := checkLog_sound (w := (383 / 4617)) (n := 12)
    (lo := (166290739 / 1000000000)) (hi := (8314537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2117) = 1/(2117 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_406 : Bounds (-8314537 / 50000000) (-166290739 / 1000000000) (Real.log (2117 / 2500)) := by
  have h := reflection_log_406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_407_neg : (38297 / 250000000) ≤ -Real.log (2500000 / 2500383) ∧
    -Real.log (2500000 / 2500383) ≤ (153189 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 5000383)) (n := 12)
    (lo := (38297 / 250000000)) (hi := (153189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500383 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500383 / 2500000) = 1/(2500000 / 2500383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_407 : Bounds (38297 / 250000000) (153189 / 1000000000) (Real.log (2500383 / 2500000)) := by
  have h := reflection_log_407_neg
  have he : Real.log (2500383 / 2500000) = -Real.log (2500000 / 2500383) := by
    rw [show ((2500383 / 2500000) : ℝ) = ((2500000 / 2500383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_408_neg : (153211 / 1000000000) ≤ -Real.log (2499617 / 2500000) ∧
    -Real.log (2499617 / 2500000) ≤ (38303 / 250000000) := by
  have h := checkLog_sound (w := (383 / 4999617)) (n := 12)
    (lo := (153211 / 1000000000)) (hi := (38303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499617) = 1/(2499617 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_408 : Bounds (-38303 / 250000000) (-153211 / 1000000000) (Real.log (2499617 / 2500000)) := by
  have h := reflection_log_408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_409_neg : (73992751 / 1000000000) ≤ -Real.log (1000000 / 1076799) ∧
    -Real.log (1000000 / 1076799) ≤ (4624547 / 62500000) := by
  have h := checkLog_sound (w := (76799 / 2076799)) (n := 12)
    (lo := (73992751 / 1000000000)) (hi := (4624547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076799 / 1000000) = 1/(1000000 / 1076799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_409 : Bounds (73992751 / 1000000000) (4624547 / 62500000) (Real.log (1076799 / 1000000)) := by
  have h := reflection_log_409_neg
  have he : Real.log (1076799 / 1000000) = -Real.log (1000000 / 1076799) := by
    rw [show ((1076799 / 1000000) : ℝ) = ((1000000 / 1076799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_410_neg : (799083 / 10000000) ≤ -Real.log (923201 / 1000000) ∧
    -Real.log (923201 / 1000000) ≤ (79908301 / 1000000000) := by
  have h := checkLog_sound (w := (76799 / 1923201)) (n := 12)
    (lo := (799083 / 10000000)) (hi := (79908301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923201) = 1/(923201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_410 : Bounds (-79908301 / 1000000000) (-799083 / 10000000) (Real.log (923201 / 1000000)) := by
  have h := reflection_log_410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_411_neg : (74182183 / 1000000000) ≤ -Real.log (1000000 / 1077003) ∧
    -Real.log (1000000 / 1077003) ≤ (9272773 / 125000000) := by
  have h := checkLog_sound (w := (77003 / 2077003)) (n := 12)
    (lo := (74182183 / 1000000000)) (hi := (9272773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077003 / 1000000) = 1/(1000000 / 1077003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_411 : Bounds (74182183 / 1000000000) (9272773 / 125000000) (Real.log (1077003 / 1000000)) := by
  have h := reflection_log_411_neg
  have he : Real.log (1077003 / 1000000) = -Real.log (1000000 / 1077003) := by
    rw [show ((1077003 / 1000000) : ℝ) = ((1000000 / 1077003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_412_neg : (40064647 / 500000000) ≤ -Real.log (922997 / 1000000) ∧
    -Real.log (922997 / 1000000) ≤ (16025859 / 200000000) := by
  have h := checkLog_sound (w := (77003 / 1922997)) (n := 12)
    (lo := (40064647 / 500000000)) (hi := (16025859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922997) = 1/(922997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_412 : Bounds (-16025859 / 200000000) (-40064647 / 500000000) (Real.log (922997 / 1000000)) := by
  have h := reflection_log_412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_413_neg : (5947111 / 1000000000) ≤ -Real.log (994070537991 / 1000000000000) ∧
    -Real.log (994070537991 / 1000000000000) ≤ (743389 / 125000000) := by
  have h := checkLog_sound (w := (5929462009 / 1994070537991)) (n := 12)
    (lo := (5947111 / 1000000000)) (hi := (743389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994070537991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994070537991) = 1/(994070537991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_413 : Bounds (-743389 / 125000000) (-5947111 / 1000000000) (Real.log (994070537991 / 1000000000000)) := by
  have h := reflection_log_413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_414_neg : (1478887 / 250000000) ≤ -Real.log (994101913599 / 1000000000000) ∧
    -Real.log (994101913599 / 1000000000000) ≤ (5915549 / 1000000000) := by
  have h := checkLog_sound (w := (5898086401 / 1994101913599)) (n := 12)
    (lo := (1478887 / 250000000)) (hi := (5915549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994101913599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994101913599) = 1/(994101913599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_414 : Bounds (-5915549 / 1000000000) (-1478887 / 250000000) (Real.log (994101913599 / 1000000000000)) := by
  have h := reflection_log_414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_415_neg : (153901051 / 1000000000) ≤ -Real.log (7812500000 / 9112308357) ∧
    -Real.log (7812500000 / 9112308357) ≤ (38475263 / 250000000) := by
  have h := checkLog_sound (w := (1299808357 / 16924808357)) (n := 12)
    (lo := (153901051 / 1000000000)) (hi := (38475263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9112308357 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9112308357 / 7812500000) = 1/(7812500000 / 9112308357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_415 : Bounds (153901051 / 1000000000) (38475263 / 250000000) (Real.log (9112308357 / 7812500000)) := by
  have h := reflection_log_415_neg
  have he : Real.log (9112308357 / 7812500000) = -Real.log (7812500000 / 9112308357) := by
    rw [show ((9112308357 / 7812500000) : ℝ) = ((7812500000 / 9112308357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_416_neg : (77155739 / 500000000) ≤ -Real.log (500000000000 / 583427140067) ∧
    -Real.log (500000000000 / 583427140067) ≤ (154311479 / 1000000000) := by
  have h := checkLog_sound (w := (83427140067 / 1083427140067)) (n := 12)
    (lo := (77155739 / 500000000)) (hi := (154311479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583427140067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583427140067 / 500000000000) = 1/(500000000000 / 583427140067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_416 : Bounds (77155739 / 500000000) (154311479 / 1000000000) (Real.log (583427140067 / 500000000000)) := by
  have h := reflection_log_416_neg
  have he : Real.log (583427140067 / 500000000000) = -Real.log (500000000000 / 583427140067) := by
    rw [show ((583427140067 / 500000000000) : ℝ) = ((500000000000 / 583427140067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_417_neg : (154313311 / 500000000) ≤ -Real.log (500000000000 / 680776951233) ∧
    -Real.log (500000000000 / 680776951233) ≤ (308626623 / 1000000000) := by
  have h := checkLog_sound (w := (180776951233 / 1180776951233)) (n := 12)
    (lo := (154313311 / 500000000)) (hi := (308626623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680776951233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680776951233 / 500000000000) = 1/(500000000000 / 680776951233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_417 : Bounds (154313311 / 500000000) (308626623 / 1000000000) (Real.log (680776951233 / 500000000000)) := by
  have h := reflection_log_417_neg
  have he : Real.log (680776951233 / 500000000000) = -Real.log (500000000000 / 680776951233) := by
    rw [show ((680776951233 / 500000000000) : ℝ) = ((500000000000 / 680776951233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_418_neg : (154415713 / 500000000) ≤ -Real.log (6250000000 / 8511454889) ∧
    -Real.log (6250000000 / 8511454889) ≤ (308831427 / 1000000000) := by
  have h := checkLog_sound (w := (2261454889 / 14761454889)) (n := 12)
    (lo := (154415713 / 500000000)) (hi := (308831427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8511454889 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8511454889 / 6250000000) = 1/(6250000000 / 8511454889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_418 : Bounds (154415713 / 500000000) (308831427 / 1000000000) (Real.log (8511454889 / 6250000000)) := by
  have h := reflection_log_418_neg
  have he : Real.log (8511454889 / 6250000000) = -Real.log (6250000000 / 8511454889) := by
    rw [show ((8511454889 / 6250000000) : ℝ) = ((6250000000 / 8511454889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_419_neg : (71313699 / 500000000) ≤ -Real.log (10000 / 11533) ∧
    -Real.log (10000 / 11533) ≤ (142627399 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 21533)) (n := 12)
    (lo := (71313699 / 500000000)) (hi := (142627399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11533 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11533 / 10000) = 1/(10000 / 11533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_419 : Bounds (71313699 / 500000000) (142627399 / 1000000000) (Real.log (11533 / 10000)) := by
  have h := reflection_log_419_neg
  have he : Real.log (11533 / 10000) = -Real.log (10000 / 11533) := by
    rw [show ((11533 / 10000) : ℝ) = ((10000 / 11533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_420_neg : (83204419 / 500000000) ≤ -Real.log (8467 / 10000) ∧
    -Real.log (8467 / 10000) ≤ (166408839 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 18467)) (n := 12)
    (lo := (83204419 / 500000000)) (hi := (166408839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8467) = 1/(8467 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_420 : Bounds (-166408839 / 1000000000) (-83204419 / 500000000) (Real.log (8467 / 10000)) := by
  have h := reflection_log_420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_421_neg : (19161 / 125000000) ≤ -Real.log (10000000 / 10001533) ∧
    -Real.log (10000000 / 10001533) ≤ (153289 / 1000000000) := by
  have h := checkLog_sound (w := (1533 / 20001533)) (n := 12)
    (lo := (19161 / 125000000)) (hi := (153289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001533 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001533 / 10000000) = 1/(10000000 / 10001533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_421 : Bounds (19161 / 125000000) (153289 / 1000000000) (Real.log (10001533 / 10000000)) := by
  have h := reflection_log_421_neg
  have he : Real.log (10001533 / 10000000) = -Real.log (10000000 / 10001533) := by
    rw [show ((10001533 / 10000000) : ℝ) = ((10000000 / 10001533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_422_neg : (153311 / 1000000000) ≤ -Real.log (9998467 / 10000000) ∧
    -Real.log (9998467 / 10000000) ≤ (4791 / 31250000) := by
  have h := checkLog_sound (w := (1533 / 19998467)) (n := 12)
    (lo := (153311 / 1000000000)) (hi := (4791 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998467) = 1/(9998467 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_422 : Bounds (-4791 / 31250000) (-153311 / 1000000000) (Real.log (9998467 / 10000000)) := by
  have h := reflection_log_422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_423_neg : (4627507 / 62500000) ≤ -Real.log (20000 / 21537) ∧
    -Real.log (20000 / 21537) ≤ (74040113 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 41537)) (n := 12)
    (lo := (4627507 / 62500000)) (hi := (74040113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21537 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21537 / 20000) = 1/(20000 / 21537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_423 : Bounds (4627507 / 62500000) (74040113 / 1000000000) (Real.log (21537 / 20000)) := by
  have h := reflection_log_423_neg
  have he : Real.log (21537 / 20000) = -Real.log (20000 / 21537) := by
    rw [show ((21537 / 20000) : ℝ) = ((20000 / 21537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_424_neg : (9995443 / 125000000) ≤ -Real.log (18463 / 20000) ∧
    -Real.log (18463 / 20000) ≤ (15992709 / 200000000) := by
  have h := checkLog_sound (w := (1537 / 38463)) (n := 12)
    (lo := (9995443 / 125000000)) (hi := (15992709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18463) = 1/(18463 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_424 : Bounds (-15992709 / 200000000) (-9995443 / 125000000) (Real.log (18463 / 20000)) := by
  have h := reflection_log_424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_425_neg : (2319673 / 31250000) ≤ -Real.log (500000 / 538527) ∧
    -Real.log (500000 / 538527) ≤ (74229537 / 1000000000) := by
  have h := checkLog_sound (w := (38527 / 1038527)) (n := 12)
    (lo := (2319673 / 31250000)) (hi := (74229537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538527 / 500000) = 1/(500000 / 538527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_425 : Bounds (2319673 / 31250000) (74229537 / 1000000000) (Real.log (538527 / 500000)) := by
  have h := reflection_log_425_neg
  have he : Real.log (538527 / 500000) = -Real.log (500000 / 538527) := by
    rw [show ((538527 / 500000) : ℝ) = ((500000 / 538527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_426_neg : (80184551 / 1000000000) ≤ -Real.log (461473 / 500000) ∧
    -Real.log (461473 / 500000) ≤ (10023069 / 125000000) := by
  have h := checkLog_sound (w := (38527 / 961473)) (n := 12)
    (lo := (80184551 / 1000000000)) (hi := (10023069 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461473) = 1/(461473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_426 : Bounds (-10023069 / 125000000) (-80184551 / 1000000000) (Real.log (461473 / 500000)) := by
  have h := reflection_log_426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_427_neg : (2977507 / 500000000) ≤ -Real.log (248515670271 / 250000000000) ∧
    -Real.log (248515670271 / 250000000000) ≤ (1191003 / 200000000) := by
  have h := checkLog_sound (w := (1484329729 / 498515670271)) (n := 12)
    (lo := (2977507 / 500000000)) (hi := (1191003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248515670271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248515670271) = 1/(248515670271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_427 : Bounds (-1191003 / 200000000) (-2977507 / 500000000) (Real.log (248515670271 / 250000000000)) := by
  have h := reflection_log_427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_428_neg : (5923431 / 1000000000) ≤ -Real.log (397637631 / 400000000) ∧
    -Real.log (397637631 / 400000000) ≤ (740429 / 125000000) := by
  have h := checkLog_sound (w := (2362369 / 797637631)) (n := 12)
    (lo := (5923431 / 1000000000)) (hi := (740429 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397637631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397637631) = 1/(397637631 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_428 : Bounds (-740429 / 125000000) (-5923431 / 1000000000) (Real.log (397637631 / 400000000)) := by
  have h := reflection_log_428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_429_neg : (19250457 / 125000000) ≤ -Real.log (500000000000 / 583247576233) ∧
    -Real.log (500000000000 / 583247576233) ≤ (154003657 / 1000000000) := by
  have h := checkLog_sound (w := (83247576233 / 1083247576233)) (n := 12)
    (lo := (19250457 / 125000000)) (hi := (154003657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583247576233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583247576233 / 500000000000) = 1/(500000000000 / 583247576233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_429 : Bounds (19250457 / 125000000) (154003657 / 1000000000) (Real.log (583247576233 / 500000000000)) := by
  have h := reflection_log_429_neg
  have he : Real.log (583247576233 / 500000000000) = -Real.log (500000000000 / 583247576233) := by
    rw [show ((583247576233 / 500000000000) : ℝ) = ((500000000000 / 583247576233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_430_neg : (154414087 / 1000000000) ≤ -Real.log (125000000000 / 145871751977) ∧
    -Real.log (125000000000 / 145871751977) ≤ (19301761 / 125000000) := by
  have h := checkLog_sound (w := (20871751977 / 270871751977)) (n := 12)
    (lo := (154414087 / 1000000000)) (hi := (19301761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145871751977 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145871751977 / 125000000000) = 1/(125000000000 / 145871751977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_430 : Bounds (154414087 / 1000000000) (19301761 / 125000000) (Real.log (145871751977 / 125000000000)) := by
  have h := reflection_log_430_neg
  have he : Real.log (145871751977 / 125000000000) = -Real.log (125000000000 / 145871751977) := by
    rw [show ((145871751977 / 125000000000) : ℝ) = ((125000000000 / 145871751977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_431_neg : (154415713 / 500000000) ≤ -Real.log (500000000000 / 680916391119) ∧
    -Real.log (500000000000 / 680916391119) ≤ (308831427 / 1000000000) := by
  have h := checkLog_sound (w := (180916391119 / 1180916391119)) (n := 12)
    (lo := (154415713 / 500000000)) (hi := (308831427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680916391119 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680916391119 / 500000000000) = 1/(500000000000 / 680916391119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_431 : Bounds (154415713 / 500000000) (308831427 / 1000000000) (Real.log (680916391119 / 500000000000)) := by
  have h := reflection_log_431_neg
  have he : Real.log (680916391119 / 500000000000) = -Real.log (500000000000 / 680916391119) := by
    rw [show ((680916391119 / 500000000000) : ℝ) = ((500000000000 / 680916391119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_432_neg : (77259059 / 250000000) ≤ -Real.log (500000000000 / 681055863943) ∧
    -Real.log (500000000000 / 681055863943) ≤ (309036237 / 1000000000) := by
  have h := checkLog_sound (w := (181055863943 / 1181055863943)) (n := 12)
    (lo := (77259059 / 250000000)) (hi := (309036237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681055863943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681055863943 / 500000000000) = 1/(500000000000 / 681055863943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_432 : Bounds (77259059 / 250000000) (309036237 / 1000000000) (Real.log (681055863943 / 500000000000)) := by
  have h := reflection_log_432_neg
  have he : Real.log (681055863943 / 500000000000) = -Real.log (500000000000 / 681055863943) := by
    rw [show ((681055863943 / 500000000000) : ℝ) = ((500000000000 / 681055863943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_433_neg : (71357051 / 500000000) ≤ -Real.log (5000 / 5767) ∧
    -Real.log (5000 / 5767) ≤ (142714103 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 10767)) (n := 12)
    (lo := (71357051 / 500000000)) (hi := (142714103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5767 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5767 / 5000) = 1/(5000 / 5767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_433 : Bounds (71357051 / 500000000) (142714103 / 1000000000) (Real.log (5767 / 5000)) := by
  have h := reflection_log_433_neg
  have he : Real.log (5767 / 5000) = -Real.log (5000 / 5767) := by
    rw [show ((5767 / 5000) : ℝ) = ((5000 / 5767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_434_neg : (3330539 / 20000000) ≤ -Real.log (4233 / 5000) ∧
    -Real.log (4233 / 5000) ≤ (166526951 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 9233)) (n := 12)
    (lo := (3330539 / 20000000)) (hi := (166526951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4233) = 1/(4233 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_434 : Bounds (-166526951 / 1000000000) (-3330539 / 20000000) (Real.log (4233 / 5000)) := by
  have h := reflection_log_434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_435_neg : (38347 / 250000000) ≤ -Real.log (5000000 / 5000767) ∧
    -Real.log (5000000 / 5000767) ≤ (153389 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 10000767)) (n := 12)
    (lo := (38347 / 250000000)) (hi := (153389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000767 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000767 / 5000000) = 1/(5000000 / 5000767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_435 : Bounds (38347 / 250000000) (153389 / 1000000000) (Real.log (5000767 / 5000000)) := by
  have h := reflection_log_435_neg
  have he : Real.log (5000767 / 5000000) = -Real.log (5000000 / 5000767) := by
    rw [show ((5000767 / 5000000) : ℝ) = ((5000000 / 5000767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_436_neg : (153411 / 1000000000) ≤ -Real.log (4999233 / 5000000) ∧
    -Real.log (4999233 / 5000000) ≤ (38353 / 250000000) := by
  have h := checkLog_sound (w := (767 / 9999233)) (n := 12)
    (lo := (153411 / 1000000000)) (hi := (38353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999233) = 1/(4999233 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_436 : Bounds (-38353 / 250000000) (-153411 / 1000000000) (Real.log (4999233 / 5000000)) := by
  have h := reflection_log_436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_437_neg : (74086543 / 1000000000) ≤ -Real.log (10000 / 10769) ∧
    -Real.log (10000 / 10769) ≤ (4630409 / 62500000) := by
  have h := checkLog_sound (w := (769 / 20769)) (n := 12)
    (lo := (74086543 / 1000000000)) (hi := (4630409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10769 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10769 / 10000) = 1/(10000 / 10769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_437 : Bounds (74086543 / 1000000000) (4630409 / 62500000) (Real.log (10769 / 10000)) := by
  have h := reflection_log_437_neg
  have he : Real.log (10769 / 10000) = -Real.log (10000 / 10769) := by
    rw [show ((10769 / 10000) : ℝ) = ((10000 / 10769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_438_neg : (80017707 / 1000000000) ≤ -Real.log (9231 / 10000) ∧
    -Real.log (9231 / 10000) ≤ (20004427 / 250000000) := by
  have h := checkLog_sound (w := (769 / 19231)) (n := 12)
    (lo := (80017707 / 1000000000)) (hi := (20004427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9231) = 1/(9231 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_438 : Bounds (-20004427 / 250000000) (-80017707 / 1000000000) (Real.log (9231 / 10000)) := by
  have h := reflection_log_438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_439_neg : (37138443 / 500000000) ≤ -Real.log (200000 / 215421) ∧
    -Real.log (200000 / 215421) ≤ (74276887 / 1000000000) := by
  have h := checkLog_sound (w := (15421 / 415421)) (n := 12)
    (lo := (37138443 / 500000000)) (hi := (74276887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215421 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215421 / 200000) = 1/(200000 / 215421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_439 : Bounds (37138443 / 500000000) (74276887 / 1000000000) (Real.log (215421 / 200000)) := by
  have h := reflection_log_439_neg
  have he : Real.log (215421 / 200000) = -Real.log (200000 / 215421) := by
    rw [show ((215421 / 200000) : ℝ) = ((200000 / 215421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_440_neg : (8023981 / 100000000) ≤ -Real.log (184579 / 200000) ∧
    -Real.log (184579 / 200000) ≤ (80239811 / 1000000000) := by
  have h := checkLog_sound (w := (15421 / 384579)) (n := 12)
    (lo := (8023981 / 100000000)) (hi := (80239811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184579) = 1/(184579 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_440 : Bounds (-80239811 / 1000000000) (-8023981 / 100000000) (Real.log (184579 / 200000)) := by
  have h := reflection_log_440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_441_neg : (5962923 / 1000000000) ≤ -Real.log (39762192759 / 40000000000) ∧
    -Real.log (39762192759 / 40000000000) ≤ (1490731 / 250000000) := by
  have h := checkLog_sound (w := (237807241 / 79762192759)) (n := 12)
    (lo := (5962923 / 1000000000)) (hi := (1490731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39762192759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39762192759) = 1/(39762192759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_441 : Bounds (-1490731 / 250000000) (-5962923 / 1000000000) (Real.log (39762192759 / 40000000000)) := by
  have h := reflection_log_441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_442_neg : (1482791 / 250000000) ≤ -Real.log (99408639 / 100000000) ∧
    -Real.log (99408639 / 100000000) ≤ (1186233 / 200000000) := by
  have h := checkLog_sound (w := (591361 / 199408639)) (n := 12)
    (lo := (1482791 / 250000000)) (hi := (1186233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99408639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99408639) = 1/(99408639 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_442 : Bounds (-1186233 / 200000000) (-1482791 / 250000000) (Real.log (99408639 / 100000000)) := by
  have h := reflection_log_442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_443_neg : (154104251 / 1000000000) ≤ -Real.log (500000000000 / 583306250677) ∧
    -Real.log (500000000000 / 583306250677) ≤ (38526063 / 250000000) := by
  have h := checkLog_sound (w := (83306250677 / 1083306250677)) (n := 12)
    (lo := (154104251 / 1000000000)) (hi := (38526063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583306250677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583306250677 / 500000000000) = 1/(500000000000 / 583306250677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_443 : Bounds (154104251 / 1000000000) (38526063 / 250000000) (Real.log (583306250677 / 500000000000)) := by
  have h := reflection_log_443_neg
  have he : Real.log (583306250677 / 500000000000) = -Real.log (500000000000 / 583306250677) := by
    rw [show ((583306250677 / 500000000000) : ℝ) = ((500000000000 / 583306250677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_444_neg : (19314587 / 125000000) ≤ -Real.log (100000000000 / 116709376473) ∧
    -Real.log (100000000000 / 116709376473) ≤ (154516697 / 1000000000) := by
  have h := checkLog_sound (w := (16709376473 / 216709376473)) (n := 12)
    (lo := (19314587 / 125000000)) (hi := (154516697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116709376473 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116709376473 / 100000000000) = 1/(100000000000 / 116709376473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_444 : Bounds (19314587 / 125000000) (154516697 / 1000000000) (Real.log (116709376473 / 100000000000)) := by
  have h := reflection_log_444_neg
  have he : Real.log (116709376473 / 100000000000) = -Real.log (100000000000 / 116709376473) := by
    rw [show ((116709376473 / 100000000000) : ℝ) = ((100000000000 / 116709376473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_445_neg : (77259059 / 250000000) ≤ -Real.log (250000000000 / 340527931971) ∧
    -Real.log (250000000000 / 340527931971) ≤ (309036237 / 1000000000) := by
  have h := checkLog_sound (w := (90527931971 / 590527931971)) (n := 12)
    (lo := (77259059 / 250000000)) (hi := (309036237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340527931971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340527931971 / 250000000000) = 1/(250000000000 / 340527931971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_445 : Bounds (77259059 / 250000000) (309036237 / 1000000000) (Real.log (340527931971 / 250000000000)) := by
  have h := reflection_log_445_neg
  have he : Real.log (340527931971 / 250000000000) = -Real.log (250000000000 / 340527931971) := by
    rw [show ((340527931971 / 250000000000) : ℝ) = ((250000000000 / 340527931971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_446_neg : (309241053 / 1000000000) ≤ -Real.log (100000000000 / 136239073943) ∧
    -Real.log (100000000000 / 136239073943) ≤ (154620527 / 500000000) := by
  have h := checkLog_sound (w := (36239073943 / 236239073943)) (n := 12)
    (lo := (309241053 / 1000000000)) (hi := (154620527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136239073943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136239073943 / 100000000000) = 1/(100000000000 / 136239073943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_446 : Bounds (309241053 / 1000000000) (154620527 / 500000000) (Real.log (136239073943 / 100000000000)) := by
  have h := reflection_log_446_neg
  have he : Real.log (136239073943 / 100000000000) = -Real.log (100000000000 / 136239073943) := by
    rw [show ((136239073943 / 100000000000) : ℝ) = ((100000000000 / 136239073943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_447_neg : (71400399 / 500000000) ≤ -Real.log (2000 / 2307) ∧
    -Real.log (2000 / 2307) ≤ (142800799 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 4307)) (n := 12)
    (lo := (71400399 / 500000000)) (hi := (142800799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2307 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2307 / 2000) = 1/(2000 / 2307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_447 : Bounds (71400399 / 500000000) (142800799 / 1000000000) (Real.log (2307 / 2000)) := by
  have h := reflection_log_447_neg
  have he : Real.log (2307 / 2000) = -Real.log (2000 / 2307) := by
    rw [show ((2307 / 2000) : ℝ) = ((2000 / 2307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
