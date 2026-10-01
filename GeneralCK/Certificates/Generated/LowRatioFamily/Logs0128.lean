import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8192_neg : (32798959 / 250000000) ≤ -Real.log (438523 / 500000) ∧
    -Real.log (438523 / 500000) ≤ (131195837 / 1000000000) := by
  have h := checkLog_sound (w := (61477 / 938523)) (n := 12)
    (lo := (32798959 / 250000000)) (hi := (131195837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438523) = 1/(438523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8192 : Bounds (-131195837 / 1000000000) (-32798959 / 250000000) (Real.log (438523 / 500000)) := by
  have h := reflection_log_8192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8193_neg : (29101967 / 250000000) ≤ -Real.log (500000 / 561727) ∧
    -Real.log (500000 / 561727) ≤ (116407869 / 1000000000) := by
  have h := checkLog_sound (w := (61727 / 1061727)) (n := 12)
    (lo := (29101967 / 250000000)) (hi := (116407869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561727 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561727 / 500000) = 1/(500000 / 561727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8193 : Bounds (29101967 / 250000000) (116407869 / 1000000000) (Real.log (561727 / 500000)) := by
  have h := reflection_log_8193_neg
  have he : Real.log (561727 / 500000) = -Real.log (500000 / 561727) := by
    rw [show ((561727 / 500000) : ℝ) = ((500000 / 561727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8194_neg : (65883047 / 500000000) ≤ -Real.log (438273 / 500000) ∧
    -Real.log (438273 / 500000) ≤ (26353219 / 200000000) := by
  have h := checkLog_sound (w := (61727 / 938273)) (n := 12)
    (lo := (65883047 / 500000000)) (hi := (26353219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438273) = 1/(438273 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8194 : Bounds (-26353219 / 200000000) (-65883047 / 500000000) (Real.log (438273 / 500000)) := by
  have h := reflection_log_8194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8195_neg : (7679113 / 500000000) ≤ -Real.log (246189777471 / 250000000000) ∧
    -Real.log (246189777471 / 250000000000) ≤ (15358227 / 1000000000) := by
  have h := checkLog_sound (w := (3810222529 / 496189777471)) (n := 12)
    (lo := (7679113 / 500000000)) (hi := (15358227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246189777471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246189777471) = 1/(246189777471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8195 : Bounds (-15358227 / 1000000000) (-7679113 / 500000000) (Real.log (246189777471 / 250000000000)) := by
  have h := reflection_log_8195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8196_neg : (15233123 / 1000000000) ≤ -Real.log (246220578471 / 250000000000) ∧
    -Real.log (246220578471 / 250000000000) ≤ (3808281 / 250000000) := by
  have h := checkLog_sound (w := (3779421529 / 496220578471)) (n := 12)
    (lo := (15233123 / 1000000000)) (hi := (3808281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246220578471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246220578471) = 1/(246220578471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8196 : Bounds (-3808281 / 250000000) (-15233123 / 1000000000) (Real.log (246220578471 / 250000000000)) := by
  have h := reflection_log_8196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8197_neg : (247158549 / 1000000000) ≤ -Real.log (125000000000 / 160047762603) ∧
    -Real.log (125000000000 / 160047762603) ≤ (4943171 / 20000000) := by
  have h := checkLog_sound (w := (35047762603 / 285047762603)) (n := 12)
    (lo := (247158549 / 1000000000)) (hi := (4943171 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160047762603 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160047762603 / 125000000000) = 1/(125000000000 / 160047762603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8197 : Bounds (247158549 / 1000000000) (4943171 / 20000000) (Real.log (160047762603 / 125000000000)) := by
  have h := reflection_log_8197_neg
  have he : Real.log (160047762603 / 125000000000) = -Real.log (125000000000 / 160047762603) := by
    rw [show ((160047762603 / 125000000000) : ℝ) = ((125000000000 / 160047762603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8198_neg : (124086981 / 500000000) ≤ -Real.log (125000000000 / 160210359753) ∧
    -Real.log (125000000000 / 160210359753) ≤ (248173963 / 1000000000) := by
  have h := checkLog_sound (w := (35210359753 / 285210359753)) (n := 12)
    (lo := (124086981 / 500000000)) (hi := (248173963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160210359753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160210359753 / 125000000000) = 1/(125000000000 / 160210359753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8198 : Bounds (124086981 / 500000000) (248173963 / 1000000000) (Real.log (160210359753 / 125000000000)) := by
  have h := reflection_log_8198_neg
  have he : Real.log (160210359753 / 125000000000) = -Real.log (125000000000 / 160210359753) := by
    rw [show ((160210359753 / 125000000000) : ℝ) = ((125000000000 / 160210359753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8199_neg : (49698273 / 100000000) ≤ -Real.log (62500000000 / 102734633179) ∧
    -Real.log (62500000000 / 102734633179) ≤ (496982731 / 1000000000) := by
  have h := checkLog_sound (w := (40234633179 / 165234633179)) (n := 12)
    (lo := (49698273 / 100000000)) (hi := (496982731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102734633179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102734633179 / 62500000000) = 1/(62500000000 / 102734633179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8199 : Bounds (49698273 / 100000000) (496982731 / 1000000000) (Real.log (102734633179 / 62500000000)) := by
  have h := reflection_log_8199_neg
  have he : Real.log (102734633179 / 62500000000) = -Real.log (62500000000 / 102734633179) := by
    rw [show ((102734633179 / 62500000000) : ℝ) = ((62500000000 / 102734633179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8200_neg : (498045897 / 1000000000) ≤ -Real.log (3906250000 / 6427744709) ∧
    -Real.log (3906250000 / 6427744709) ≤ (249022949 / 500000000) := by
  have h := checkLog_sound (w := (2521494709 / 10333994709)) (n := 12)
    (lo := (498045897 / 1000000000)) (hi := (249022949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427744709 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427744709 / 3906250000) = 1/(3906250000 / 6427744709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8200 : Bounds (498045897 / 1000000000) (249022949 / 500000000) (Real.log (6427744709 / 3906250000)) := by
  have h := reflection_log_8200_neg
  have he : Real.log (6427744709 / 3906250000) = -Real.log (3906250000 / 6427744709) := by
    rw [show ((6427744709 / 3906250000) : ℝ) = ((3906250000 / 6427744709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8201_neg : (109366921 / 500000000) ≤ -Real.log (2000 / 2489) ∧
    -Real.log (2000 / 2489) ≤ (218733843 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 4489)) (n := 12)
    (lo := (109366921 / 500000000)) (hi := (218733843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2489 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2489 / 2000) = 1/(2000 / 2489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8201 : Bounds (109366921 / 500000000) (218733843 / 1000000000) (Real.log (2489 / 2000)) := by
  have h := reflection_log_8201_neg
  have he : Real.log (2489 / 2000) = -Real.log (2000 / 2489) := by
    rw [show ((2489 / 2000) : ℝ) = ((2000 / 2489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8202_neg : (280375497 / 1000000000) ≤ -Real.log (1511 / 2000) ∧
    -Real.log (1511 / 2000) ≤ (140187749 / 500000000) := by
  have h := checkLog_sound (w := (489 / 3511)) (n := 12)
    (lo := (280375497 / 1000000000)) (hi := (140187749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1511) = 1/(1511 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8202 : Bounds (-140187749 / 500000000) (-280375497 / 1000000000) (Real.log (1511 / 2000)) := by
  have h := reflection_log_8202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8203_neg : (24447 / 100000000) ≤ -Real.log (2000000 / 2000489) ∧
    -Real.log (2000000 / 2000489) ≤ (244471 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 4000489)) (n := 12)
    (lo := (24447 / 100000000)) (hi := (244471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000489 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000489 / 2000000) = 1/(2000000 / 2000489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8203 : Bounds (24447 / 100000000) (244471 / 1000000000) (Real.log (2000489 / 2000000)) := by
  have h := reflection_log_8203_neg
  have he : Real.log (2000489 / 2000000) = -Real.log (2000000 / 2000489) := by
    rw [show ((2000489 / 2000000) : ℝ) = ((2000000 / 2000489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8204_neg : (244529 / 1000000000) ≤ -Real.log (1999511 / 2000000) ∧
    -Real.log (1999511 / 2000000) ≤ (24453 / 100000000) := by
  have h := checkLog_sound (w := (489 / 3999511)) (n := 12)
    (lo := (244529 / 1000000000)) (hi := (24453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999511) = 1/(1999511 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8204 : Bounds (-24453 / 100000000) (-244529 / 1000000000) (Real.log (1999511 / 2000000)) := by
  have h := reflection_log_8204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8205_neg : (116192437 / 1000000000) ≤ -Real.log (250000 / 280803) ∧
    -Real.log (250000 / 280803) ≤ (58096219 / 500000000) := by
  have h := checkLog_sound (w := (30803 / 530803)) (n := 12)
    (lo := (116192437 / 1000000000)) (hi := (58096219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280803 / 250000) = 1/(250000 / 280803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8205 : Bounds (116192437 / 1000000000) (58096219 / 500000000) (Real.log (280803 / 250000)) := by
  have h := reflection_log_8205_neg
  have he : Real.log (280803 / 250000) = -Real.log (250000 / 280803) := by
    rw [show ((280803 / 250000) : ℝ) = ((250000 / 280803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8206_neg : (131490049 / 1000000000) ≤ -Real.log (219197 / 250000) ∧
    -Real.log (219197 / 250000) ≤ (2629801 / 20000000) := by
  have h := checkLog_sound (w := (30803 / 469197)) (n := 12)
    (lo := (131490049 / 1000000000)) (hi := (2629801 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 219197) = 1/(219197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8206 : Bounds (-2629801 / 20000000) (-131490049 / 1000000000) (Real.log (219197 / 250000)) := by
  have h := reflection_log_8206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8207_neg : (5831919 / 50000000) ≤ -Real.log (1000000 / 1123713) ∧
    -Real.log (1000000 / 1123713) ≤ (116638381 / 1000000000) := by
  have h := checkLog_sound (w := (123713 / 2123713)) (n := 12)
    (lo := (5831919 / 50000000)) (hi := (116638381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1123713 / 1000000) = 1/(1000000 / 1123713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8207 : Bounds (5831919 / 50000000) (116638381 / 1000000000) (Real.log (1123713 / 1000000)) := by
  have h := reflection_log_8207_neg
  have he : Real.log (1123713 / 1000000) = -Real.log (1000000 / 1123713) := by
    rw [show ((1123713 / 1000000) : ℝ) = ((1000000 / 1123713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8208_neg : (8253851 / 62500000) ≤ -Real.log (876287 / 1000000) ∧
    -Real.log (876287 / 1000000) ≤ (132061617 / 1000000000) := by
  have h := checkLog_sound (w := (123713 / 1876287)) (n := 12)
    (lo := (8253851 / 62500000)) (hi := (132061617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 876287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 876287) = 1/(876287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8208 : Bounds (-132061617 / 1000000000) (-8253851 / 62500000) (Real.log (876287 / 1000000)) := by
  have h := reflection_log_8208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8209_neg : (3084647 / 200000000) ≤ -Real.log (984695093631 / 1000000000000) ∧
    -Real.log (984695093631 / 1000000000000) ≤ (3855809 / 250000000) := by
  have h := checkLog_sound (w := (15304906369 / 1984695093631)) (n := 12)
    (lo := (3084647 / 200000000)) (hi := (3855809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984695093631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984695093631) = 1/(984695093631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8209 : Bounds (-3855809 / 250000000) (-3084647 / 200000000) (Real.log (984695093631 / 1000000000000)) := by
  have h := reflection_log_8209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8210_neg : (15297611 / 1000000000) ≤ -Real.log (61551175191 / 62500000000) ∧
    -Real.log (61551175191 / 62500000000) ≤ (3824403 / 250000000) := by
  have h := checkLog_sound (w := (948824809 / 124051175191)) (n := 12)
    (lo := (15297611 / 1000000000)) (hi := (3824403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61551175191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61551175191) = 1/(61551175191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8210 : Bounds (-3824403 / 250000000) (-15297611 / 1000000000) (Real.log (61551175191 / 62500000000)) := by
  have h := reflection_log_8210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8211_neg : (247682487 / 1000000000) ≤ -Real.log (500000000000 / 640526558301) ∧
    -Real.log (500000000000 / 640526558301) ≤ (30960311 / 125000000) := by
  have h := checkLog_sound (w := (140526558301 / 1140526558301)) (n := 12)
    (lo := (247682487 / 1000000000)) (hi := (30960311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640526558301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640526558301 / 500000000000) = 1/(500000000000 / 640526558301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8211 : Bounds (247682487 / 1000000000) (30960311 / 125000000) (Real.log (640526558301 / 500000000000)) := by
  have h := reflection_log_8211_neg
  have he : Real.log (640526558301 / 500000000000) = -Real.log (500000000000 / 640526558301) := by
    rw [show ((640526558301 / 500000000000) : ℝ) = ((500000000000 / 640526558301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8212_neg : (62174999 / 250000000) ≤ -Real.log (100000000000 / 128235726423) ∧
    -Real.log (100000000000 / 128235726423) ≤ (248699997 / 1000000000) := by
  have h := checkLog_sound (w := (28235726423 / 228235726423)) (n := 12)
    (lo := (62174999 / 250000000)) (hi := (248699997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128235726423 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128235726423 / 100000000000) = 1/(100000000000 / 128235726423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8212 : Bounds (62174999 / 250000000) (248699997 / 1000000000) (Real.log (128235726423 / 100000000000)) := by
  have h := reflection_log_8212_neg
  have he : Real.log (128235726423 / 100000000000) = -Real.log (100000000000 / 128235726423) := by
    rw [show ((128235726423 / 100000000000) : ℝ) = ((100000000000 / 128235726423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8213_neg : (498045897 / 1000000000) ≤ -Real.log (500000000000 / 822751322751) ∧
    -Real.log (500000000000 / 822751322751) ≤ (249022949 / 500000000) := by
  have h := checkLog_sound (w := (322751322751 / 1322751322751)) (n := 12)
    (lo := (498045897 / 1000000000)) (hi := (249022949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822751322751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822751322751 / 500000000000) = 1/(500000000000 / 822751322751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8213 : Bounds (498045897 / 1000000000) (249022949 / 500000000) (Real.log (822751322751 / 500000000000)) := by
  have h := reflection_log_8213_neg
  have he : Real.log (822751322751 / 500000000000) = -Real.log (500000000000 / 822751322751) := by
    rw [show ((822751322751 / 500000000000) : ℝ) = ((500000000000 / 822751322751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8214_neg : (24955467 / 50000000) ≤ -Real.log (500000000000 / 823626737261) ∧
    -Real.log (500000000000 / 823626737261) ≤ (499109341 / 1000000000) := by
  have h := checkLog_sound (w := (323626737261 / 1323626737261)) (n := 12)
    (lo := (24955467 / 50000000)) (hi := (499109341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823626737261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823626737261 / 500000000000) = 1/(500000000000 / 823626737261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8214 : Bounds (24955467 / 50000000) (499109341 / 1000000000) (Real.log (823626737261 / 500000000000)) := by
  have h := reflection_log_8214_neg
  have he : Real.log (823626737261 / 500000000000) = -Real.log (500000000000 / 823626737261) := by
    rw [show ((823626737261 / 500000000000) : ℝ) = ((500000000000 / 823626737261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8215_neg : (219135529 / 1000000000) ≤ -Real.log (200 / 249) ∧
    -Real.log (200 / 249) ≤ (21913553 / 100000000) := by
  have h := checkLog_sound (w := (49 / 449)) (n := 12)
    (lo := (219135529 / 1000000000)) (hi := (21913553 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 200) = 1/(200 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8215 : Bounds (219135529 / 1000000000) (21913553 / 100000000) (Real.log (249 / 200)) := by
  have h := reflection_log_8215_neg
  have he : Real.log (249 / 200) = -Real.log (200 / 249) := by
    rw [show ((249 / 200) : ℝ) = ((200 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8216_neg : (281037529 / 1000000000) ≤ -Real.log (151 / 200) ∧
    -Real.log (151 / 200) ≤ (28103753 / 100000000) := by
  have h := checkLog_sound (w := (49 / 351)) (n := 12)
    (lo := (281037529 / 1000000000)) (hi := (28103753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 151) = 1/(151 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8216 : Bounds (-28103753 / 100000000) (-281037529 / 1000000000) (Real.log (151 / 200)) := by
  have h := reflection_log_8216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8217_neg : (244969 / 1000000000) ≤ -Real.log (200000 / 200049) ∧
    -Real.log (200000 / 200049) ≤ (24497 / 100000000) := by
  have h := checkLog_sound (w := (49 / 400049)) (n := 12)
    (lo := (244969 / 1000000000)) (hi := (24497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200049 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200049 / 200000) = 1/(200000 / 200049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8217 : Bounds (244969 / 1000000000) (24497 / 100000000) (Real.log (200049 / 200000)) := by
  have h := reflection_log_8217_neg
  have he : Real.log (200049 / 200000) = -Real.log (200000 / 200049) := by
    rw [show ((200049 / 200000) : ℝ) = ((200000 / 200049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8218_neg : (24503 / 100000000) ≤ -Real.log (199951 / 200000) ∧
    -Real.log (199951 / 200000) ≤ (245031 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 399951)) (n := 12)
    (lo := (24503 / 100000000)) (hi := (245031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199951) = 1/(199951 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8218 : Bounds (-245031 / 1000000000) (-24503 / 100000000) (Real.log (199951 / 200000)) := by
  have h := reflection_log_8218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8219_neg : (11642211 / 100000000) ≤ -Real.log (100000 / 112347) ∧
    -Real.log (100000 / 112347) ≤ (116422111 / 1000000000) := by
  have h := checkLog_sound (w := (12347 / 212347)) (n := 12)
    (lo := (11642211 / 100000000)) (hi := (116422111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112347 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112347 / 100000) = 1/(100000 / 112347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8219 : Bounds (11642211 / 100000000) (116422111 / 1000000000) (Real.log (112347 / 100000)) := by
  have h := reflection_log_8219_neg
  have he : Real.log (112347 / 100000) = -Real.log (100000 / 112347) := by
    rw [show ((112347 / 100000) : ℝ) = ((100000 / 112347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8220_neg : (32946087 / 250000000) ≤ -Real.log (87653 / 100000) ∧
    -Real.log (87653 / 100000) ≤ (131784349 / 1000000000) := by
  have h := checkLog_sound (w := (12347 / 187653)) (n := 12)
    (lo := (32946087 / 250000000)) (hi := (131784349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87653) = 1/(87653 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8220 : Bounds (-131784349 / 1000000000) (-32946087 / 250000000) (Real.log (87653 / 100000)) := by
  have h := reflection_log_8220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8221_neg : (2337359 / 20000000) ≤ -Real.log (1000000 / 1123971) ∧
    -Real.log (1000000 / 1123971) ≤ (116867951 / 1000000000) := by
  have h := checkLog_sound (w := (123971 / 2123971)) (n := 12)
    (lo := (2337359 / 20000000)) (hi := (116867951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1123971 / 1000000) = 1/(1000000 / 1123971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8221 : Bounds (2337359 / 20000000) (116867951 / 1000000000) (Real.log (1123971 / 1000000)) := by
  have h := reflection_log_8221_neg
  have he : Real.log (1123971 / 1000000) = -Real.log (1000000 / 1123971) := by
    rw [show ((1123971 / 1000000) : ℝ) = ((1000000 / 1123971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8222_neg : (132356083 / 1000000000) ≤ -Real.log (876029 / 1000000) ∧
    -Real.log (876029 / 1000000) ≤ (33089021 / 250000000) := by
  have h := checkLog_sound (w := (123971 / 1876029)) (n := 12)
    (lo := (132356083 / 1000000000)) (hi := (33089021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 876029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 876029) = 1/(876029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8222 : Bounds (-33089021 / 250000000) (-132356083 / 1000000000) (Real.log (876029 / 1000000)) := by
  have h := reflection_log_8222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8223_neg : (15488133 / 1000000000) ≤ -Real.log (984631191159 / 1000000000000) ∧
    -Real.log (984631191159 / 1000000000000) ≤ (7744067 / 500000000) := by
  have h := checkLog_sound (w := (15368808841 / 1984631191159)) (n := 12)
    (lo := (15488133 / 1000000000)) (hi := (7744067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984631191159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984631191159) = 1/(984631191159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8223 : Bounds (-7744067 / 500000000) (-15488133 / 1000000000) (Real.log (984631191159 / 1000000000000)) := by
  have h := reflection_log_8223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8224_neg : (7681119 / 500000000) ≤ -Real.log (9847551591 / 10000000000) ∧
    -Real.log (9847551591 / 10000000000) ≤ (15362239 / 1000000000) := by
  have h := checkLog_sound (w := (152448409 / 19847551591)) (n := 12)
    (lo := (7681119 / 500000000)) (hi := (15362239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9847551591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9847551591) = 1/(9847551591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8224 : Bounds (-15362239 / 1000000000) (-7681119 / 500000000) (Real.log (9847551591 / 10000000000)) := by
  have h := reflection_log_8224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8225_neg : (124103229 / 500000000) ≤ -Real.log (250000000000 / 320431131849) ∧
    -Real.log (250000000000 / 320431131849) ≤ (248206459 / 1000000000) := by
  have h := checkLog_sound (w := (70431131849 / 570431131849)) (n := 12)
    (lo := (124103229 / 500000000)) (hi := (248206459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320431131849 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320431131849 / 250000000000) = 1/(250000000000 / 320431131849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8225 : Bounds (124103229 / 500000000) (248206459 / 1000000000) (Real.log (320431131849 / 250000000000)) := by
  have h := reflection_log_8225_neg
  have he : Real.log (320431131849 / 250000000000) = -Real.log (250000000000 / 320431131849) := by
    rw [show ((320431131849 / 250000000000) : ℝ) = ((250000000000 / 320431131849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8226_neg : (249224033 / 1000000000) ≤ -Real.log (100000000000 / 128302944309) ∧
    -Real.log (100000000000 / 128302944309) ≤ (124612017 / 500000000) := by
  have h := checkLog_sound (w := (28302944309 / 228302944309)) (n := 12)
    (lo := (249224033 / 1000000000)) (hi := (124612017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128302944309 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128302944309 / 100000000000) = 1/(100000000000 / 128302944309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8226 : Bounds (249224033 / 1000000000) (124612017 / 500000000) (Real.log (128302944309 / 100000000000)) := by
  have h := reflection_log_8226_neg
  have he : Real.log (128302944309 / 100000000000) = -Real.log (100000000000 / 128302944309) := by
    rw [show ((128302944309 / 100000000000) : ℝ) = ((100000000000 / 128302944309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8227_neg : (24955467 / 50000000) ≤ -Real.log (25000000000 / 41181336863) ∧
    -Real.log (25000000000 / 41181336863) ≤ (499109341 / 1000000000) := by
  have h := checkLog_sound (w := (16181336863 / 66181336863)) (n := 12)
    (lo := (24955467 / 50000000)) (hi := (499109341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41181336863 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41181336863 / 25000000000) = 1/(25000000000 / 41181336863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8227 : Bounds (24955467 / 50000000) (499109341 / 1000000000) (Real.log (41181336863 / 25000000000)) := by
  have h := reflection_log_8227_neg
  have he : Real.log (41181336863 / 25000000000) = -Real.log (25000000000 / 41181336863) := by
    rw [show ((41181336863 / 25000000000) : ℝ) = ((25000000000 / 41181336863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8228_neg : (500173059 / 1000000000) ≤ -Real.log (500000000000 / 824503311259) ∧
    -Real.log (500000000000 / 824503311259) ≤ (25008653 / 50000000) := by
  have h := checkLog_sound (w := (324503311259 / 1324503311259)) (n := 12)
    (lo := (500173059 / 1000000000)) (hi := (25008653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824503311259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824503311259 / 500000000000) = 1/(500000000000 / 824503311259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8228 : Bounds (500173059 / 1000000000) (25008653 / 50000000) (Real.log (824503311259 / 500000000000)) := by
  have h := reflection_log_8228_neg
  have he : Real.log (824503311259 / 500000000000) = -Real.log (500000000000 / 824503311259) := by
    rw [show ((824503311259 / 500000000000) : ℝ) = ((500000000000 / 824503311259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8229_neg : (43907411 / 200000000) ≤ -Real.log (2000 / 2491) ∧
    -Real.log (2000 / 2491) ≤ (6860533 / 31250000) := by
  have h := checkLog_sound (w := (491 / 4491)) (n := 12)
    (lo := (43907411 / 200000000)) (hi := (6860533 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 2000) = 1/(2000 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8229 : Bounds (43907411 / 200000000) (6860533 / 31250000) (Real.log (2491 / 2000)) := by
  have h := reflection_log_8229_neg
  have he : Real.log (2491 / 2000) = -Real.log (2000 / 2491) := by
    rw [show ((2491 / 2000) : ℝ) = ((2000 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8230_neg : (2817 / 10000) ≤ -Real.log (1509 / 2000) ∧
    -Real.log (1509 / 2000) ≤ (281700001 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3509)) (n := 12)
    (lo := (2817 / 10000)) (hi := (281700001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1509) = 1/(1509 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8230 : Bounds (-281700001 / 1000000000) (-2817 / 10000) (Real.log (1509 / 2000)) := by
  have h := reflection_log_8230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8231_neg : (245469 / 1000000000) ≤ -Real.log (2000000 / 2000491) ∧
    -Real.log (2000000 / 2000491) ≤ (24547 / 100000000) := by
  have h := checkLog_sound (w := (491 / 4000491)) (n := 12)
    (lo := (245469 / 1000000000)) (hi := (24547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000491 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000491 / 2000000) = 1/(2000000 / 2000491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8231 : Bounds (245469 / 1000000000) (24547 / 100000000) (Real.log (2000491 / 2000000)) := by
  have h := reflection_log_8231_neg
  have he : Real.log (2000491 / 2000000) = -Real.log (2000000 / 2000491) := by
    rw [show ((2000491 / 2000000) : ℝ) = ((2000000 / 2000491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8232_neg : (24553 / 100000000) ≤ -Real.log (1999509 / 2000000) ∧
    -Real.log (1999509 / 2000000) ≤ (245531 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3999509)) (n := 12)
    (lo := (24553 / 100000000)) (hi := (245531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999509) = 1/(1999509 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8232 : Bounds (-245531 / 1000000000) (-24553 / 100000000) (Real.log (1999509 / 2000000)) := by
  have h := reflection_log_8232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8233_neg : (116651729 / 1000000000) ≤ -Real.log (62500 / 70233) ∧
    -Real.log (62500 / 70233) ≤ (11665173 / 100000000) := by
  have h := checkLog_sound (w := (7733 / 132733)) (n := 12)
    (lo := (116651729 / 1000000000)) (hi := (11665173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70233 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70233 / 62500) = 1/(62500 / 70233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8233 : Bounds (116651729 / 1000000000) (11665173 / 100000000) (Real.log (70233 / 62500)) := by
  have h := reflection_log_8233_neg
  have he : Real.log (70233 / 62500) = -Real.log (62500 / 70233) := by
    rw [show ((70233 / 62500) : ℝ) = ((62500 / 70233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8234_neg : (132078733 / 1000000000) ≤ -Real.log (54767 / 62500) ∧
    -Real.log (54767 / 62500) ≤ (66039367 / 500000000) := by
  have h := checkLog_sound (w := (7733 / 117267)) (n := 12)
    (lo := (132078733 / 1000000000)) (hi := (66039367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54767) = 1/(54767 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8234 : Bounds (-66039367 / 500000000) (-132078733 / 1000000000) (Real.log (54767 / 62500)) := by
  have h := reflection_log_8234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8235_neg : (29274589 / 250000000) ≤ -Real.log (100000 / 112423) ∧
    -Real.log (100000 / 112423) ≤ (117098357 / 1000000000) := by
  have h := checkLog_sound (w := (12423 / 212423)) (n := 12)
    (lo := (29274589 / 250000000)) (hi := (117098357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112423 / 100000) = 1/(100000 / 112423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8235 : Bounds (29274589 / 250000000) (117098357 / 1000000000) (Real.log (112423 / 100000)) := by
  have h := reflection_log_8235_neg
  have he : Real.log (112423 / 100000) = -Real.log (100000 / 112423) := by
    rw [show ((112423 / 100000) : ℝ) = ((100000 / 112423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8236_neg : (132651779 / 1000000000) ≤ -Real.log (87577 / 100000) ∧
    -Real.log (87577 / 100000) ≤ (6632589 / 50000000) := by
  have h := checkLog_sound (w := (12423 / 187577)) (n := 12)
    (lo := (132651779 / 1000000000)) (hi := (6632589 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87577) = 1/(87577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8236 : Bounds (-6632589 / 50000000) (-132651779 / 1000000000) (Real.log (87577 / 100000)) := by
  have h := reflection_log_8236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8237_neg : (7776711 / 500000000) ≤ -Real.log (9845669071 / 10000000000) ∧
    -Real.log (9845669071 / 10000000000) ≤ (15553423 / 1000000000) := by
  have h := checkLog_sound (w := (154330929 / 19845669071)) (n := 12)
    (lo := (7776711 / 500000000)) (hi := (15553423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9845669071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9845669071) = 1/(9845669071 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8237 : Bounds (-15553423 / 1000000000) (-7776711 / 500000000) (Real.log (9845669071 / 10000000000)) := by
  have h := reflection_log_8237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8238_neg : (3856751 / 250000000) ≤ -Real.log (3846450711 / 3906250000) ∧
    -Real.log (3846450711 / 3906250000) ≤ (3085401 / 200000000) := by
  have h := checkLog_sound (w := (59799289 / 7752700711)) (n := 12)
    (lo := (3856751 / 250000000)) (hi := (3085401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3846450711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3846450711) = 1/(3846450711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8238 : Bounds (-3085401 / 200000000) (-3856751 / 250000000) (Real.log (3846450711 / 3906250000)) := by
  have h := reflection_log_8238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8239_neg : (248730463 / 1000000000) ≤ -Real.log (500000000000 / 641198166779) ∧
    -Real.log (500000000000 / 641198166779) ≤ (7772827 / 31250000) := by
  have h := checkLog_sound (w := (141198166779 / 1141198166779)) (n := 12)
    (lo := (248730463 / 1000000000)) (hi := (7772827 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641198166779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641198166779 / 500000000000) = 1/(500000000000 / 641198166779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8239 : Bounds (248730463 / 1000000000) (7772827 / 31250000) (Real.log (641198166779 / 500000000000)) := by
  have h := reflection_log_8239_neg
  have he : Real.log (641198166779 / 500000000000) = -Real.log (500000000000 / 641198166779) := by
    rw [show ((641198166779 / 500000000000) : ℝ) = ((500000000000 / 641198166779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8240_neg : (31218767 / 125000000) ≤ -Real.log (250000000000 / 320926156411) ∧
    -Real.log (250000000000 / 320926156411) ≤ (249750137 / 1000000000) := by
  have h := checkLog_sound (w := (70926156411 / 570926156411)) (n := 12)
    (lo := (31218767 / 125000000)) (hi := (249750137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320926156411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320926156411 / 250000000000) = 1/(250000000000 / 320926156411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8240 : Bounds (31218767 / 125000000) (249750137 / 1000000000) (Real.log (320926156411 / 250000000000)) := by
  have h := reflection_log_8240_neg
  have he : Real.log (320926156411 / 250000000000) = -Real.log (250000000000 / 320926156411) := by
    rw [show ((320926156411 / 250000000000) : ℝ) = ((250000000000 / 320926156411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8241_neg : (500173059 / 1000000000) ≤ -Real.log (250000000000 / 412251655629) ∧
    -Real.log (250000000000 / 412251655629) ≤ (25008653 / 50000000) := by
  have h := checkLog_sound (w := (162251655629 / 662251655629)) (n := 12)
    (lo := (500173059 / 1000000000)) (hi := (25008653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412251655629 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412251655629 / 250000000000) = 1/(250000000000 / 412251655629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8241 : Bounds (500173059 / 1000000000) (25008653 / 50000000) (Real.log (412251655629 / 250000000000)) := by
  have h := reflection_log_8241_neg
  have he : Real.log (412251655629 / 250000000000) = -Real.log (250000000000 / 412251655629) := by
    rw [show ((412251655629 / 250000000000) : ℝ) = ((250000000000 / 412251655629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8242_neg : (7831829 / 15625000) ≤ -Real.log (125000000000 / 206345261763) ∧
    -Real.log (125000000000 / 206345261763) ≤ (501237057 / 1000000000) := by
  have h := checkLog_sound (w := (81345261763 / 331345261763)) (n := 12)
    (lo := (7831829 / 15625000)) (hi := (501237057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206345261763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206345261763 / 125000000000) = 1/(125000000000 / 206345261763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8242 : Bounds (7831829 / 15625000) (501237057 / 1000000000) (Real.log (206345261763 / 125000000000)) := by
  have h := reflection_log_8242_neg
  have he : Real.log (206345261763 / 125000000000) = -Real.log (125000000000 / 206345261763) := by
    rw [show ((206345261763 / 125000000000) : ℝ) = ((125000000000 / 206345261763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8243_neg : (10996921 / 50000000) ≤ -Real.log (500 / 623) ∧
    -Real.log (500 / 623) ≤ (219938421 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1123)) (n := 12)
    (lo := (10996921 / 50000000)) (hi := (219938421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623 / 500) = 1/(500 / 623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8243 : Bounds (10996921 / 50000000) (219938421 / 1000000000) (Real.log (623 / 500)) := by
  have h := reflection_log_8243_neg
  have he : Real.log (623 / 500) = -Real.log (500 / 623) := by
    rw [show ((623 / 500) : ℝ) = ((500 / 623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8244_neg : (28236291 / 100000000) ≤ -Real.log (377 / 500) ∧
    -Real.log (377 / 500) ≤ (282362911 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 877)) (n := 12)
    (lo := (28236291 / 100000000)) (hi := (282362911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 377) = 1/(377 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8244 : Bounds (-282362911 / 1000000000) (-28236291 / 100000000) (Real.log (377 / 500)) := by
  have h := reflection_log_8244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8245_neg : (245969 / 1000000000) ≤ -Real.log (500000 / 500123) ∧
    -Real.log (500000 / 500123) ≤ (24597 / 100000000) := by
  have h := checkLog_sound (w := (123 / 1000123)) (n := 12)
    (lo := (245969 / 1000000000)) (hi := (24597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500123 / 500000) = 1/(500000 / 500123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8245 : Bounds (245969 / 1000000000) (24597 / 100000000) (Real.log (500123 / 500000)) := by
  have h := reflection_log_8245_neg
  have he : Real.log (500123 / 500000) = -Real.log (500000 / 500123) := by
    rw [show ((500123 / 500000) : ℝ) = ((500000 / 500123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8246_neg : (24603 / 100000000) ≤ -Real.log (499877 / 500000) ∧
    -Real.log (499877 / 500000) ≤ (246031 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 999877)) (n := 12)
    (lo := (24603 / 100000000)) (hi := (246031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499877) = 1/(499877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8246 : Bounds (-246031 / 1000000000) (-24603 / 100000000) (Real.log (499877 / 500000)) := by
  have h := reflection_log_8246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8247_neg : (23376259 / 200000000) ≤ -Real.log (500000 / 561993) ∧
    -Real.log (500000 / 561993) ≤ (7305081 / 62500000) := by
  have h := checkLog_sound (w := (61993 / 1061993)) (n := 12)
    (lo := (23376259 / 200000000)) (hi := (7305081 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561993 / 500000) = 1/(500000 / 561993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8247 : Bounds (23376259 / 200000000) (7305081 / 62500000) (Real.log (561993 / 500000)) := by
  have h := reflection_log_8247_neg
  have he : Real.log (561993 / 500000) = -Real.log (500000 / 561993) := by
    rw [show ((561993 / 500000) : ℝ) = ((500000 / 561993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8248_neg : (66186603 / 500000000) ≤ -Real.log (438007 / 500000) ∧
    -Real.log (438007 / 500000) ≤ (132373207 / 1000000000) := by
  have h := checkLog_sound (w := (61993 / 938007)) (n := 12)
    (lo := (66186603 / 500000000)) (hi := (132373207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438007) = 1/(438007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8248 : Bounds (-132373207 / 1000000000) (-66186603 / 500000000) (Real.log (438007 / 500000)) := by
  have h := reflection_log_8248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8249_neg : (11732871 / 100000000) ≤ -Real.log (1000000 / 1124489) ∧
    -Real.log (1000000 / 1124489) ≤ (117328711 / 1000000000) := by
  have h := checkLog_sound (w := (124489 / 2124489)) (n := 12)
    (lo := (11732871 / 100000000)) (hi := (117328711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124489 / 1000000) = 1/(1000000 / 1124489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8249 : Bounds (11732871 / 100000000) (117328711 / 1000000000) (Real.log (1124489 / 1000000)) := by
  have h := reflection_log_8249_neg
  have he : Real.log (1124489 / 1000000) = -Real.log (1000000 / 1124489) := by
    rw [show ((1124489 / 1000000) : ℝ) = ((1000000 / 1124489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8250_neg : (132947563 / 1000000000) ≤ -Real.log (875511 / 1000000) ∧
    -Real.log (875511 / 1000000) ≤ (33236891 / 250000000) := by
  have h := checkLog_sound (w := (124489 / 1875511)) (n := 12)
    (lo := (132947563 / 1000000000)) (hi := (33236891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875511) = 1/(875511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8250 : Bounds (-33236891 / 250000000) (-132947563 / 1000000000) (Real.log (875511 / 1000000)) := by
  have h := reflection_log_8250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8251_neg : (3904713 / 250000000) ≤ -Real.log (984502488879 / 1000000000000) ∧
    -Real.log (984502488879 / 1000000000000) ≤ (15618853 / 1000000000) := by
  have h := checkLog_sound (w := (15497511121 / 1984502488879)) (n := 12)
    (lo := (3904713 / 250000000)) (hi := (15618853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984502488879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984502488879) = 1/(984502488879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8251 : Bounds (-15618853 / 1000000000) (-3904713 / 250000000) (Real.log (984502488879 / 1000000000000)) := by
  have h := reflection_log_8251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8252_neg : (1549191 / 100000000) ≤ -Real.log (246156867951 / 250000000000) ∧
    -Real.log (246156867951 / 250000000000) ≤ (15491911 / 1000000000) := by
  have h := checkLog_sound (w := (3843132049 / 496156867951)) (n := 12)
    (lo := (1549191 / 100000000)) (hi := (15491911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246156867951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246156867951) = 1/(246156867951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8252 : Bounds (-15491911 / 1000000000) (-1549191 / 100000000) (Real.log (246156867951 / 250000000000)) := by
  have h := reflection_log_8252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8253_neg : (124627251 / 500000000) ≤ -Real.log (500000000000 / 641534267717) ∧
    -Real.log (500000000000 / 641534267717) ≤ (249254503 / 1000000000) := by
  have h := checkLog_sound (w := (141534267717 / 1141534267717)) (n := 12)
    (lo := (124627251 / 500000000)) (hi := (249254503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641534267717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641534267717 / 500000000000) = 1/(500000000000 / 641534267717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8253 : Bounds (124627251 / 500000000) (249254503 / 1000000000) (Real.log (641534267717 / 500000000000)) := by
  have h := reflection_log_8253_neg
  have he : Real.log (641534267717 / 500000000000) = -Real.log (500000000000 / 641534267717) := by
    rw [show ((641534267717 / 500000000000) : ℝ) = ((500000000000 / 641534267717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8254_neg : (250276273 / 1000000000) ≤ -Real.log (500000000000 / 642190103837) ∧
    -Real.log (500000000000 / 642190103837) ≤ (125138137 / 500000000) := by
  have h := checkLog_sound (w := (142190103837 / 1142190103837)) (n := 12)
    (lo := (250276273 / 1000000000)) (hi := (125138137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642190103837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642190103837 / 500000000000) = 1/(500000000000 / 642190103837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8254 : Bounds (250276273 / 1000000000) (125138137 / 500000000) (Real.log (642190103837 / 500000000000)) := by
  have h := reflection_log_8254_neg
  have he : Real.log (642190103837 / 500000000000) = -Real.log (500000000000 / 642190103837) := by
    rw [show ((642190103837 / 500000000000) : ℝ) = ((500000000000 / 642190103837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8255_neg : (7831829 / 15625000) ≤ -Real.log (500000000000 / 825381047051) ∧
    -Real.log (500000000000 / 825381047051) ≤ (501237057 / 1000000000) := by
  have h := checkLog_sound (w := (325381047051 / 1325381047051)) (n := 12)
    (lo := (7831829 / 15625000)) (hi := (501237057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825381047051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825381047051 / 500000000000) = 1/(500000000000 / 825381047051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8255 : Bounds (7831829 / 15625000) (501237057 / 1000000000) (Real.log (825381047051 / 500000000000)) := by
  have h := reflection_log_8255_neg
  have he : Real.log (825381047051 / 500000000000) = -Real.log (500000000000 / 825381047051) := by
    rw [show ((825381047051 / 500000000000) : ℝ) = ((500000000000 / 825381047051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
