import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14272_neg : (313503689 / 500000000) ≤ -Real.log (125 / 234) ∧
    -Real.log (125 / 234) ≤ (627007379 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 359)) (n := 12)
    (lo := (313503689 / 500000000)) (hi := (627007379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234 / 125) = 1/(125 / 234) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14272 : Bounds (313503689 / 500000000) (627007379 / 1000000000) (Real.log (234 / 125)) := by
  have h := reflection_log_14272_neg
  have he : Real.log (234 / 125) = -Real.log (125 / 234) := by
    rw [show ((234 / 125) : ℝ) = ((125 / 234) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14273_neg : (2055725013 / 1000000000) ≤ -Real.log (16 / 125) ∧
    -Real.log (16 / 125) ≤ (256965627 / 125000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 64) = 1/(16 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14273 : Bounds (-256965627 / 125000000) (-2055725013 / 1000000000) (Real.log (16 / 125)) := by
  have h := reflection_log_14273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14274_neg : (43581 / 50000000) ≤ -Real.log (125000 / 125109) ∧
    -Real.log (125000 / 125109) ≤ (871621 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 250109)) (n := 12)
    (lo := (43581 / 50000000)) (hi := (871621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125109 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125109 / 125000) = 1/(125000 / 125109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14274 : Bounds (43581 / 50000000) (871621 / 1000000000) (Real.log (125109 / 125000)) := by
  have h := reflection_log_14274_neg
  have he : Real.log (125109 / 125000) = -Real.log (125000 / 125109) := by
    rw [show ((125109 / 125000) : ℝ) = ((125000 / 125109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14275_neg : (43619 / 50000000) ≤ -Real.log (124891 / 125000) ∧
    -Real.log (124891 / 125000) ≤ (872381 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 249891)) (n := 12)
    (lo := (43619 / 50000000)) (hi := (872381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124891) = 1/(124891 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14275 : Bounds (-872381 / 1000000000) (-43619 / 50000000) (Real.log (124891 / 125000)) := by
  have h := reflection_log_14275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14276_neg : (51890951 / 125000000) ≤ -Real.log (250000 / 378641) ∧
    -Real.log (250000 / 378641) ≤ (415127609 / 1000000000) := by
  have h := checkLog_sound (w := (128641 / 628641)) (n := 12)
    (lo := (51890951 / 125000000)) (hi := (415127609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((378641 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(378641 / 250000) = 1/(250000 / 378641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14276 : Bounds (51890951 / 125000000) (415127609 / 1000000000) (Real.log (378641 / 250000)) := by
  have h := reflection_log_14276_neg
  have he : Real.log (378641 / 250000) = -Real.log (250000 / 378641) := by
    rw [show ((378641 / 250000) : ℝ) = ((250000 / 378641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14277_neg : (361353911 / 500000000) ≤ -Real.log (121359 / 250000) ∧
    -Real.log (121359 / 250000) ≤ (45169239 / 62500000) := by
  have h := checkLog_sound (w := (3641 / 246359)) (n := 12)
    (lo := (14780321 / 500000000)) (hi := (29560643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 121359) = 1/(121359 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14277 : Bounds (-45169239 / 62500000) (-361353911 / 500000000) (Real.log (121359 / 250000)) := by
  have h := reflection_log_14277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14278_neg : (83458313 / 200000000) ≤ -Real.log (200000 / 303569) ∧
    -Real.log (200000 / 303569) ≤ (208645783 / 500000000) := by
  have h := checkLog_sound (w := (103569 / 503569)) (n := 12)
    (lo := (83458313 / 200000000)) (hi := (208645783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303569 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303569 / 200000) = 1/(200000 / 303569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14278 : Bounds (83458313 / 200000000) (208645783 / 500000000) (Real.log (303569 / 200000)) := by
  have h := reflection_log_14278_neg
  have he : Real.log (303569 / 200000) = -Real.log (200000 / 303569) := by
    rw [show ((303569 / 200000) : ℝ) = ((200000 / 303569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14279_neg : (729489639 / 1000000000) ≤ -Real.log (96431 / 200000) ∧
    -Real.log (96431 / 200000) ≤ (729489641 / 1000000000) := by
  have h := checkLog_sound (w := (3569 / 196431)) (n := 12)
    (lo := (36342459 / 1000000000)) (hi := (1817123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 96431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 96431) = 1/(96431 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14279 : Bounds (-729489641 / 1000000000) (-729489639 / 1000000000) (Real.log (96431 / 200000)) := by
  have h := reflection_log_14279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14280_neg : (156099037 / 500000000) ≤ -Real.log (29273462239 / 40000000000) ∧
    -Real.log (29273462239 / 40000000000) ≤ (12487923 / 40000000) := by
  have h := checkLog_sound (w := (10726537761 / 69273462239)) (n := 12)
    (lo := (156099037 / 500000000)) (hi := (12487923 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29273462239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29273462239) = 1/(29273462239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14280 : Bounds (-12487923 / 40000000) (-156099037 / 500000000) (Real.log (29273462239 / 40000000000)) := by
  have h := reflection_log_14280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14281_neg : (153790107 / 500000000) ≤ -Real.log (45951493119 / 62500000000) ∧
    -Real.log (45951493119 / 62500000000) ≤ (61516043 / 200000000) := by
  have h := checkLog_sound (w := (16548506881 / 108451493119)) (n := 12)
    (lo := (153790107 / 500000000)) (hi := (61516043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45951493119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45951493119) = 1/(45951493119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14281 : Bounds (-61516043 / 200000000) (-153790107 / 500000000) (Real.log (45951493119 / 62500000000)) := by
  have h := reflection_log_14281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14282_neg : (1137835431 / 1000000000) ≤ -Real.log (250000000000 / 780001895203) ∧
    -Real.log (250000000000 / 780001895203) ≤ (1137835433 / 1000000000) := by
  have h := checkLog_sound (w := (280001895203 / 1280001895203)) (n := 12)
    (lo := (444688251 / 1000000000)) (hi := (111172063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780001895203 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(780001895203 / 500000000000) = 1/(250000000000 / 780001895203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14282 : Bounds (1137835431 / 1000000000) (1137835433 / 1000000000) (Real.log (780001895203 / 250000000000)) := by
  have h := reflection_log_14282_neg
  have he : Real.log (780001895203 / 250000000000) = -Real.log (250000000000 / 780001895203) := by
    rw [show ((780001895203 / 250000000000) : ℝ) = ((250000000000 / 780001895203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14283_neg : (229356241 / 200000000) ≤ -Real.log (10000000000 / 31480436789) ∧
    -Real.log (10000000000 / 31480436789) ≤ (1146781207 / 1000000000) := by
  have h := checkLog_sound (w := (11480436789 / 51480436789)) (n := 12)
    (lo := (18145361 / 40000000)) (hi := (226817013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31480436789 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31480436789 / 20000000000) = 1/(10000000000 / 31480436789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14283 : Bounds (229356241 / 200000000) (1146781207 / 1000000000) (Real.log (31480436789 / 10000000000)) := by
  have h := reflection_log_14283_neg
  have he : Real.log (31480436789 / 10000000000) = -Real.log (10000000000 / 31480436789) := by
    rw [show ((31480436789 / 10000000000) : ℝ) = ((10000000000 / 31480436789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14284_neg : (1328980741 / 500000000) ≤ -Real.log (500000000000 / 7133587786259) ∧
    -Real.log (500000000000 / 7133587786259) ≤ (1328980743 / 500000000) := by
  have h := checkLog_sound (w := (3133587786259 / 11133587786259)) (n := 12)
    (lo := (289259971 / 500000000)) (hi := (578519943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7133587786259 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7133587786259 / 4000000000000) = 1/(500000000000 / 7133587786259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14284 : Bounds (1328980741 / 500000000) (1328980743 / 500000000) (Real.log (7133587786259 / 500000000000)) := by
  have h := reflection_log_14284_neg
  have he : Real.log (7133587786259 / 500000000000) = -Real.log (500000000000 / 7133587786259) := by
    rw [show ((7133587786259 / 500000000000) : ℝ) = ((500000000000 / 7133587786259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14285_neg : (2682732391 / 1000000000) ≤ -Real.log (8 / 117) ∧
    -Real.log (8 / 117) ≤ (536546479 / 200000000) := by
  have h := checkLog_sound (w := (53 / 181)) (n := 12)
    (lo := (603290851 / 1000000000)) (hi := (150822713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 64) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(117 / 64) = 1/(8 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14285 : Bounds (2682732391 / 1000000000) (536546479 / 200000000) (Real.log (117 / 8)) := by
  have h := reflection_log_14285_neg
  have he : Real.log (117 / 8) = -Real.log (8 / 117) := by
    rw [show ((117 / 8) : ℝ) = ((8 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14286_neg : (628608659 / 1000000000) ≤ -Real.log (8 / 15) ∧
    -Real.log (8 / 15) ≤ (31430433 / 50000000) := by
  have h := checkLog_sound (w := (7 / 23)) (n := 12)
    (lo := (628608659 / 1000000000)) (hi := (31430433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15 / 8) = 1/(8 / 15) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14286 : Bounds (628608659 / 1000000000) (31430433 / 50000000) (Real.log (15 / 8)) := by
  have h := reflection_log_14286_neg
  have he : Real.log (15 / 8) = -Real.log (8 / 15) := by
    rw [show ((15 / 8) : ℝ) = ((8 / 15) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14287_neg : (103972077 / 50000000) ≤ -Real.log (1 / 8) ∧
    -Real.log (1 / 8) ≤ (2079441543 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2 / 1) = 1/(1 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14287 : Bounds (-2079441543 / 1000000000) (-103972077 / 50000000) (Real.log (1 / 8)) := by
  have h := reflection_log_14287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14288_neg : (874617 / 1000000000) ≤ -Real.log (8000 / 8007) ∧
    -Real.log (8000 / 8007) ≤ (437309 / 500000000) := by
  have h := checkLog_sound (w := (7 / 16007)) (n := 12)
    (lo := (874617 / 1000000000)) (hi := (437309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8007 / 8000) = 1/(8000 / 8007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14288 : Bounds (874617 / 1000000000) (437309 / 500000000) (Real.log (8007 / 8000)) := by
  have h := reflection_log_14288_neg
  have he : Real.log (8007 / 8000) = -Real.log (8000 / 8007) := by
    rw [show ((8007 / 8000) : ℝ) = ((8000 / 8007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14289_neg : (875383 / 1000000000) ≤ -Real.log (7993 / 8000) ∧
    -Real.log (7993 / 8000) ≤ (109423 / 125000000) := by
  have h := checkLog_sound (w := (7 / 15993)) (n := 12)
    (lo := (875383 / 1000000000)) (hi := (109423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7993) = 1/(7993 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14289 : Bounds (-109423 / 125000000) (-875383 / 1000000000) (Real.log (7993 / 8000)) := by
  have h := reflection_log_14289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14290_neg : (416846757 / 1000000000) ≤ -Real.log (100000 / 151717) ∧
    -Real.log (100000 / 151717) ≤ (208423379 / 500000000) := by
  have h := checkLog_sound (w := (51717 / 251717)) (n := 12)
    (lo := (416846757 / 1000000000)) (hi := (208423379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151717 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151717 / 100000) = 1/(100000 / 151717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14290 : Bounds (416846757 / 1000000000) (208423379 / 500000000) (Real.log (151717 / 100000)) := by
  have h := reflection_log_14290_neg
  have he : Real.log (151717 / 100000) = -Real.log (100000 / 151717) := by
    rw [show ((151717 / 100000) : ℝ) = ((100000 / 151717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14291_neg : (728090653 / 1000000000) ≤ -Real.log (48283 / 100000) ∧
    -Real.log (48283 / 100000) ≤ (145618131 / 200000000) := by
  have h := checkLog_sound (w := (1717 / 98283)) (n := 12)
    (lo := (34943473 / 1000000000)) (hi := (17471737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 48283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 48283) = 1/(48283 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14291 : Bounds (-145618131 / 200000000) (-728090653 / 1000000000) (Real.log (48283 / 100000)) := by
  have h := reflection_log_14291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14292_neg : (209509091 / 500000000) ≤ -Real.log (250000 / 380117) ∧
    -Real.log (250000 / 380117) ≤ (419018183 / 1000000000) := by
  have h := checkLog_sound (w := (130117 / 630117)) (n := 12)
    (lo := (209509091 / 500000000)) (hi := (419018183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380117 / 250000) = 1/(250000 / 380117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14292 : Bounds (209509091 / 500000000) (419018183 / 1000000000) (Real.log (380117 / 250000)) := by
  have h := reflection_log_14292_neg
  have he : Real.log (380117 / 250000) = -Real.log (250000 / 380117) := by
    rw [show ((380117 / 250000) : ℝ) = ((250000 / 380117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14293_neg : (14698893 / 20000000) ≤ -Real.log (119883 / 250000) ∧
    -Real.log (119883 / 250000) ≤ (183736163 / 250000000) := by
  have h := checkLog_sound (w := (5117 / 244883)) (n := 12)
    (lo := (4179747 / 100000000)) (hi := (41797471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 119883) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 119883) = 1/(119883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14293 : Bounds (-183736163 / 250000000) (-14698893 / 20000000) (Real.log (119883 / 250000)) := by
  have h := reflection_log_14293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14294_neg : (78981617 / 250000000) ≤ -Real.log (45569566311 / 62500000000) ∧
    -Real.log (45569566311 / 62500000000) ≤ (315926469 / 1000000000) := by
  have h := checkLog_sound (w := (16930433689 / 108069566311)) (n := 12)
    (lo := (78981617 / 250000000)) (hi := (315926469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45569566311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45569566311) = 1/(45569566311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14294 : Bounds (-315926469 / 1000000000) (-78981617 / 250000000) (Real.log (45569566311 / 62500000000)) := by
  have h := reflection_log_14294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14295_neg : (38905487 / 125000000) ≤ -Real.log (7325351911 / 10000000000) ∧
    -Real.log (7325351911 / 10000000000) ≤ (311243897 / 1000000000) := by
  have h := checkLog_sound (w := (2674648089 / 17325351911)) (n := 12)
    (lo := (38905487 / 125000000)) (hi := (311243897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7325351911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7325351911) = 1/(7325351911 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14295 : Bounds (-311243897 / 1000000000) (-38905487 / 125000000) (Real.log (7325351911 / 10000000000)) := by
  have h := reflection_log_14295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14296_neg : (114493741 / 100000000) ≤ -Real.log (125000000000 / 392780585299) ∧
    -Real.log (125000000000 / 392780585299) ≤ (286234353 / 250000000) := by
  have h := checkLog_sound (w := (142780585299 / 642780585299)) (n := 12)
    (lo := (45179023 / 100000000)) (hi := (451790231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392780585299 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392780585299 / 250000000000) = 1/(125000000000 / 392780585299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14296 : Bounds (114493741 / 100000000) (286234353 / 250000000) (Real.log (392780585299 / 125000000000)) := by
  have h := reflection_log_14296_neg
  have he : Real.log (392780585299 / 125000000000) = -Real.log (125000000000 / 392780585299) := by
    rw [show ((392780585299 / 125000000000) : ℝ) = ((125000000000 / 392780585299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14297_neg : (72122677 / 62500000) ≤ -Real.log (100000000000 / 317073313147) ∧
    -Real.log (100000000000 / 317073313147) ≤ (576981417 / 500000000) := by
  have h := checkLog_sound (w := (117073313147 / 517073313147)) (n := 12)
    (lo := (115203913 / 250000000)) (hi := (460815653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317073313147 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(317073313147 / 200000000000) = 1/(100000000000 / 317073313147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14297 : Bounds (72122677 / 62500000) (576981417 / 500000000) (Real.log (317073313147 / 100000000000)) := by
  have h := reflection_log_14297_neg
  have he : Real.log (317073313147 / 100000000000) = -Real.log (100000000000 / 317073313147) := by
    rw [show ((317073313147 / 100000000000) : ℝ) = ((100000000000 / 317073313147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14298_neg : (2708050199 / 1000000000) ≤ -Real.log (1 / 15) ∧
    -Real.log (1 / 15) ≤ (2708050203 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 23)) (n := 12)
    (lo := (628608659 / 1000000000)) (hi := (31430433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15 / 8) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15 / 8) = 1/(1 / 15) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14298 : Bounds (2708050199 / 1000000000) (2708050203 / 1000000000) (Real.log (15 / 1)) := by
  have h := reflection_log_14298_neg
  have he : Real.log (15 / 1) = -Real.log (1 / 15) := by
    rw [show ((15 / 1) : ℝ) = ((1 / 15) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14299_neg : (31510369 / 50000000) ≤ -Real.log (500 / 939) ∧
    -Real.log (500 / 939) ≤ (630207381 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1439)) (n := 12)
    (lo := (31510369 / 50000000)) (hi := (630207381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 500) = 1/(500 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14299 : Bounds (31510369 / 50000000) (630207381 / 1000000000) (Real.log (939 / 500)) := by
  have h := reflection_log_14299_neg
  have he : Real.log (939 / 500) = -Real.log (500 / 939) := by
    rw [show ((939 / 500) : ℝ) = ((500 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14300_neg : (262966779 / 125000000) ≤ -Real.log (61 / 500) ∧
    -Real.log (61 / 500) ≤ (525933559 / 250000000) := by
  have h := checkLog_sound (w := (3 / 247)) (n := 12)
    (lo := (6073173 / 250000000)) (hi := (24292693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 122) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 122) = 1/(61 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14300 : Bounds (-525933559 / 250000000) (-262966779 / 125000000) (Real.log (61 / 500)) := by
  have h := reflection_log_14300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14301_neg : (438807 / 500000000) ≤ -Real.log (500000 / 500439) ∧
    -Real.log (500000 / 500439) ≤ (175523 / 200000000) := by
  have h := checkLog_sound (w := (439 / 1000439)) (n := 12)
    (lo := (438807 / 500000000)) (hi := (175523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500439 / 500000) = 1/(500000 / 500439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14301 : Bounds (438807 / 500000000) (175523 / 200000000) (Real.log (500439 / 500000)) := by
  have h := reflection_log_14301_neg
  have he : Real.log (500439 / 500000) = -Real.log (500000 / 500439) := by
    rw [show ((500439 / 500000) : ℝ) = ((500000 / 500439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14302_neg : (175677 / 200000000) ≤ -Real.log (499561 / 500000) ∧
    -Real.log (499561 / 500000) ≤ (439193 / 500000000) := by
  have h := checkLog_sound (w := (439 / 999561)) (n := 12)
    (lo := (175677 / 200000000)) (hi := (439193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499561) = 1/(499561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14302 : Bounds (-439193 / 500000000) (-175677 / 200000000) (Real.log (499561 / 500000)) := by
  have h := reflection_log_14302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14303_neg : (418574141 / 1000000000) ≤ -Real.log (1000000 / 1519793) ∧
    -Real.log (1000000 / 1519793) ≤ (209287071 / 500000000) := by
  have h := checkLog_sound (w := (519793 / 2519793)) (n := 12)
    (lo := (418574141 / 1000000000)) (hi := (209287071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1519793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1519793 / 1000000) = 1/(1000000 / 1519793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14303 : Bounds (418574141 / 1000000000) (209287071 / 500000000) (Real.log (1519793 / 1000000)) := by
  have h := reflection_log_14303_neg
  have he : Real.log (1519793 / 1000000) = -Real.log (1000000 / 1519793) := by
    rw [show ((1519793 / 1000000) : ℝ) = ((1000000 / 1519793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14304_neg : (733538017 / 1000000000) ≤ -Real.log (480207 / 1000000) ∧
    -Real.log (480207 / 1000000) ≤ (733538019 / 1000000000) := by
  have h := checkLog_sound (w := (19793 / 980207)) (n := 12)
    (lo := (40390837 / 1000000000)) (hi := (20195419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 480207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 480207) = 1/(480207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14304 : Bounds (-733538019 / 1000000000) (-733538017 / 1000000000) (Real.log (480207 / 1000000)) := by
  have h := reflection_log_14304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14305_neg : (420752327 / 1000000000) ≤ -Real.log (1000000 / 1523107) ∧
    -Real.log (1000000 / 1523107) ≤ (52594041 / 125000000) := by
  have h := checkLog_sound (w := (523107 / 2523107)) (n := 12)
    (lo := (420752327 / 1000000000)) (hi := (52594041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523107 / 1000000) = 1/(1000000 / 1523107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14305 : Bounds (420752327 / 1000000000) (52594041 / 125000000) (Real.log (1523107 / 1000000)) := by
  have h := reflection_log_14305_neg
  have he : Real.log (1523107 / 1000000) = -Real.log (1000000 / 1523107) := by
    rw [show ((1523107 / 1000000) : ℝ) = ((1000000 / 1523107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14306_neg : (740463131 / 1000000000) ≤ -Real.log (476893 / 1000000) ∧
    -Real.log (476893 / 1000000) ≤ (740463133 / 1000000000) := by
  have h := checkLog_sound (w := (23107 / 976893)) (n := 12)
    (lo := (47315951 / 1000000000)) (hi := (2957247 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 476893) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 476893) = 1/(476893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14306 : Bounds (-740463133 / 1000000000) (-740463131 / 1000000000) (Real.log (476893 / 1000000)) := by
  have h := reflection_log_14306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14307_neg : (79927701 / 250000000) ≤ -Real.log (726359066551 / 1000000000000) ∧
    -Real.log (726359066551 / 1000000000000) ≤ (63942161 / 200000000) := by
  have h := checkLog_sound (w := (273640933449 / 1726359066551)) (n := 12)
    (lo := (79927701 / 250000000)) (hi := (63942161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 726359066551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 726359066551) = 1/(726359066551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14307 : Bounds (-63942161 / 200000000) (-79927701 / 250000000) (Real.log (726359066551 / 1000000000000)) := by
  have h := reflection_log_14307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14308_neg : (78740969 / 250000000) ≤ -Real.log (729815237151 / 1000000000000) ∧
    -Real.log (729815237151 / 1000000000000) ≤ (314963877 / 1000000000) := by
  have h := checkLog_sound (w := (270184762849 / 1729815237151)) (n := 12)
    (lo := (78740969 / 250000000)) (hi := (314963877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 729815237151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 729815237151) = 1/(729815237151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14308 : Bounds (-314963877 / 1000000000) (-78740969 / 250000000) (Real.log (729815237151 / 1000000000000)) := by
  have h := reflection_log_14308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14309_neg : (576056079 / 500000000) ≤ -Real.log (500000000000 / 1582435283117) ∧
    -Real.log (500000000000 / 1582435283117) ≤ (7200701 / 6250000) := by
  have h := checkLog_sound (w := (582435283117 / 2582435283117)) (n := 12)
    (lo := (229482489 / 500000000)) (hi := (458964979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1582435283117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1582435283117 / 1000000000000) = 1/(500000000000 / 1582435283117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14309 : Bounds (576056079 / 500000000) (7200701 / 6250000) (Real.log (1582435283117 / 500000000000)) := by
  have h := reflection_log_14309_neg
  have he : Real.log (1582435283117 / 500000000000) = -Real.log (500000000000 / 1582435283117) := by
    rw [show ((1582435283117 / 500000000000) : ℝ) = ((500000000000 / 1582435283117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14310_neg : (580607729 / 500000000) ≤ -Real.log (500000000000 / 1596906433939) ∧
    -Real.log (500000000000 / 1596906433939) ≤ (58060773 / 50000000) := by
  have h := checkLog_sound (w := (596906433939 / 2596906433939)) (n := 12)
    (lo := (234034139 / 500000000)) (hi := (468068279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1596906433939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1596906433939 / 1000000000000) = 1/(500000000000 / 1596906433939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14310 : Bounds (580607729 / 500000000) (58060773 / 50000000) (Real.log (1596906433939 / 500000000000)) := by
  have h := reflection_log_14310_neg
  have he : Real.log (1596906433939 / 500000000000) = -Real.log (500000000000 / 1596906433939) := by
    rw [show ((1596906433939 / 500000000000) : ℝ) = ((500000000000 / 1596906433939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14311_neg : (2733941613 / 1000000000) ≤ -Real.log (125000000000 / 1924180327869) ∧
    -Real.log (125000000000 / 1924180327869) ≤ (2733941617 / 1000000000) := by
  have h := checkLog_sound (w := (924180327869 / 2924180327869)) (n := 12)
    (lo := (654500073 / 1000000000)) (hi := (327250037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924180327869 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1924180327869 / 1000000000000) = 1/(125000000000 / 1924180327869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14311 : Bounds (2733941613 / 1000000000) (2733941617 / 1000000000) (Real.log (1924180327869 / 125000000000)) := by
  have h := reflection_log_14311_neg
  have he : Real.log (1924180327869 / 125000000000) = -Real.log (125000000000 / 1924180327869) := by
    rw [show ((1924180327869 / 125000000000) : ℝ) = ((125000000000 / 1924180327869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14312_neg : (12636071 / 20000000) ≤ -Real.log (1000 / 1881) ∧
    -Real.log (1000 / 1881) ≤ (631803551 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 2881)) (n := 12)
    (lo := (12636071 / 20000000)) (hi := (631803551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1000) = 1/(1000 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14312 : Bounds (12636071 / 20000000) (631803551 / 1000000000) (Real.log (1881 / 1000)) := by
  have h := reflection_log_14312_neg
  have he : Real.log (1881 / 1000) = -Real.log (1000 / 1881) := by
    rw [show ((1881 / 1000) : ℝ) = ((1000 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14313_neg : (266078973 / 125000000) ≤ -Real.log (119 / 1000) ∧
    -Real.log (119 / 1000) ≤ (532157947 / 250000000) := by
  have h := checkLog_sound (w := (3 / 122)) (n := 12)
    (lo := (12297561 / 250000000)) (hi := (9838049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 119) = 1/(119 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14313 : Bounds (-532157947 / 250000000) (-266078973 / 125000000) (Real.log (119 / 1000)) := by
  have h := reflection_log_14313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14314_neg : (220153 / 250000000) ≤ -Real.log (1000000 / 1000881) ∧
    -Real.log (1000000 / 1000881) ≤ (880613 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 2000881)) (n := 12)
    (lo := (220153 / 250000000)) (hi := (880613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000881 / 1000000) = 1/(1000000 / 1000881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14314 : Bounds (220153 / 250000000) (880613 / 1000000000) (Real.log (1000881 / 1000000)) := by
  have h := reflection_log_14314_neg
  have he : Real.log (1000881 / 1000000) = -Real.log (1000000 / 1000881) := by
    rw [show ((1000881 / 1000000) : ℝ) = ((1000000 / 1000881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14315_neg : (220347 / 250000000) ≤ -Real.log (999119 / 1000000) ∧
    -Real.log (999119 / 1000000) ≤ (881389 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 1999119)) (n := 12)
    (lo := (220347 / 250000000)) (hi := (881389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999119) = 1/(999119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14315 : Bounds (-881389 / 1000000000) (-220347 / 250000000) (Real.log (999119 / 1000000)) := by
  have h := reflection_log_14315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14316_neg : (6567329 / 15625000) ≤ -Real.log (15625 / 23788) ∧
    -Real.log (15625 / 23788) ≤ (420309057 / 1000000000) := by
  have h := checkLog_sound (w := (8163 / 39413)) (n := 12)
    (lo := (6567329 / 15625000)) (hi := (420309057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23788 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23788 / 15625) = 1/(15625 / 23788) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14316 : Bounds (6567329 / 15625000) (420309057 / 1000000000) (Real.log (23788 / 15625)) := by
  have h := reflection_log_14316_neg
  have he : Real.log (23788 / 15625) = -Real.log (15625 / 23788) := by
    rw [show ((23788 / 15625) : ℝ) = ((15625 / 23788) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14317_neg : (9238109 / 12500000) ≤ -Real.log (7462 / 15625) ∧
    -Real.log (7462 / 15625) ≤ (369524361 / 500000000) := by
  have h := checkLog_sound (w := (701 / 30549)) (n := 12)
    (lo := (2295077 / 50000000)) (hi := (45901541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14924) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14924) = 1/(7462 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14317 : Bounds (-369524361 / 500000000) (-9238109 / 12500000) (Real.log (7462 / 15625)) := by
  have h := reflection_log_14317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14318_neg : (105623817 / 250000000) ≤ -Real.log (250000 / 381441) ∧
    -Real.log (250000 / 381441) ≤ (422495269 / 1000000000) := by
  have h := checkLog_sound (w := (131441 / 631441)) (n := 12)
    (lo := (105623817 / 250000000)) (hi := (422495269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381441 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381441 / 250000) = 1/(250000 / 381441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14318 : Bounds (105623817 / 250000000) (422495269 / 1000000000) (Real.log (381441 / 250000)) := by
  have h := reflection_log_14318_neg
  have he : Real.log (381441 / 250000) = -Real.log (250000 / 381441) := by
    rw [show ((381441 / 250000) : ℝ) = ((250000 / 381441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14319_neg : (74605019 / 100000000) ≤ -Real.log (118559 / 250000) ∧
    -Real.log (118559 / 250000) ≤ (46628137 / 62500000) := by
  have h := checkLog_sound (w := (6441 / 243559)) (n := 12)
    (lo := (5290301 / 100000000)) (hi := (52903011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118559) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 118559) = 1/(118559 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14319 : Bounds (-46628137 / 62500000) (-74605019 / 100000000) (Real.log (118559 / 250000)) := by
  have h := reflection_log_14319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14320_neg : (161777461 / 500000000) ≤ -Real.log (45223263519 / 62500000000) ∧
    -Real.log (45223263519 / 62500000000) ≤ (323554923 / 1000000000) := by
  have h := checkLog_sound (w := (17276736481 / 107723263519)) (n := 12)
    (lo := (161777461 / 500000000)) (hi := (323554923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 45223263519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 45223263519) = 1/(45223263519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14320 : Bounds (-323554923 / 1000000000) (-161777461 / 500000000) (Real.log (45223263519 / 62500000000)) := by
  have h := reflection_log_14320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14321_neg : (19921229 / 62500000) ≤ -Real.log (177506056 / 244140625) ∧
    -Real.log (177506056 / 244140625) ≤ (63747933 / 200000000) := by
  have h := checkLog_sound (w := (66634569 / 421646681)) (n := 12)
    (lo := (19921229 / 62500000)) (hi := (63747933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 177506056) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 177506056) = 1/(177506056 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14321 : Bounds (-63747933 / 200000000) (-19921229 / 62500000) (Real.log (177506056 / 244140625)) := by
  have h := reflection_log_14321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14322_neg : (72459861 / 62500000) ≤ -Real.log (500000000000 / 1593942642723) ∧
    -Real.log (500000000000 / 1593942642723) ≤ (579678889 / 500000000) := by
  have h := checkLog_sound (w := (593942642723 / 2593942642723)) (n := 12)
    (lo := (116552649 / 250000000)) (hi := (466210597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593942642723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1593942642723 / 1000000000000) = 1/(500000000000 / 1593942642723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14322 : Bounds (72459861 / 62500000) (579678889 / 500000000) (Real.log (1593942642723 / 500000000000)) := by
  have h := reflection_log_14322_neg
  have he : Real.log (1593942642723 / 500000000000) = -Real.log (500000000000 / 1593942642723) := by
    rw [show ((1593942642723 / 500000000000) : ℝ) = ((500000000000 / 1593942642723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14323_neg : (584272729 / 500000000) ≤ -Real.log (31250000000 / 100540922663) ∧
    -Real.log (31250000000 / 100540922663) ≤ (58427273 / 50000000) := by
  have h := checkLog_sound (w := (38040922663 / 163040922663)) (n := 12)
    (lo := (237699139 / 500000000)) (hi := (475398279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100540922663 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100540922663 / 62500000000) = 1/(31250000000 / 100540922663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14323 : Bounds (584272729 / 500000000) (58427273 / 50000000) (Real.log (100540922663 / 31250000000)) := by
  have h := reflection_log_14323_neg
  have he : Real.log (100540922663 / 31250000000) = -Real.log (31250000000 / 100540922663) := by
    rw [show ((100540922663 / 31250000000) : ℝ) = ((31250000000 / 100540922663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14324_neg : (2733941613 / 1000000000) ≤ -Real.log (20000000000 / 307868852459) ∧
    -Real.log (20000000000 / 307868852459) ≤ (2733941617 / 1000000000) := by
  have h := checkLog_sound (w := (147868852459 / 467868852459)) (n := 12)
    (lo := (654500073 / 1000000000)) (hi := (327250037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307868852459 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(307868852459 / 160000000000) = 1/(20000000000 / 307868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14324 : Bounds (2733941613 / 1000000000) (2733941617 / 1000000000) (Real.log (307868852459 / 20000000000)) := by
  have h := reflection_log_14324_neg
  have he : Real.log (307868852459 / 20000000000) = -Real.log (20000000000 / 307868852459) := by
    rw [show ((307868852459 / 20000000000) : ℝ) = ((20000000000 / 307868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14325_neg : (1380217667 / 500000000) ≤ -Real.log (250000000000 / 3951680672269) ∧
    -Real.log (250000000000 / 3951680672269) ≤ (1380217669 / 500000000) := by
  have h := checkLog_sound (w := (1951680672269 / 5951680672269)) (n := 12)
    (lo := (340496897 / 500000000)) (hi := (136198759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3951680672269 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3951680672269 / 2000000000000) = 1/(250000000000 / 3951680672269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14325 : Bounds (1380217667 / 500000000) (1380217669 / 500000000) (Real.log (3951680672269 / 250000000000)) := by
  have h := reflection_log_14325_neg
  have he : Real.log (3951680672269 / 250000000000) = -Real.log (250000000000 / 3951680672269) := by
    rw [show ((3951680672269 / 250000000000) : ℝ) = ((250000000000 / 3951680672269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14326_neg : (79174647 / 125000000) ≤ -Real.log (250 / 471) ∧
    -Real.log (250 / 471) ≤ (633397177 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 721)) (n := 12)
    (lo := (79174647 / 125000000)) (hi := (633397177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 250) = 1/(250 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14326 : Bounds (79174647 / 125000000) (633397177 / 1000000000) (Real.log (471 / 250)) := by
  have h := reflection_log_14326_neg
  have he : Real.log (471 / 250) = -Real.log (250 / 471) := by
    rw [show ((471 / 250) : ℝ) = ((250 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14327_neg : (1077082543 / 500000000) ≤ -Real.log (29 / 250) ∧
    -Real.log (29 / 250) ≤ (215416509 / 100000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 116) = 1/(29 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14327 : Bounds (-215416509 / 100000000) (-1077082543 / 500000000) (Real.log (29 / 250)) := by
  have h := reflection_log_14327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14328_neg : (883609 / 1000000000) ≤ -Real.log (250000 / 250221) ∧
    -Real.log (250000 / 250221) ≤ (88361 / 100000000) := by
  have h := checkLog_sound (w := (221 / 500221)) (n := 12)
    (lo := (883609 / 1000000000)) (hi := (88361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250221 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250221 / 250000) = 1/(250000 / 250221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14328 : Bounds (883609 / 1000000000) (88361 / 100000000) (Real.log (250221 / 250000)) := by
  have h := reflection_log_14328_neg
  have he : Real.log (250221 / 250000) = -Real.log (250000 / 250221) := by
    rw [show ((250221 / 250000) : ℝ) = ((250000 / 250221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14329_neg : (88439 / 100000000) ≤ -Real.log (249779 / 250000) ∧
    -Real.log (249779 / 250000) ≤ (884391 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 499779)) (n := 12)
    (lo := (88439 / 100000000)) (hi := (884391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249779) = 1/(249779 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14329 : Bounds (-884391 / 1000000000) (-88439 / 100000000) (Real.log (249779 / 250000)) := by
  have h := reflection_log_14329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14330_neg : (422052769 / 1000000000) ≤ -Real.log (1000000 / 1525089) ∧
    -Real.log (1000000 / 1525089) ≤ (42205277 / 100000000) := by
  have h := checkLog_sound (w := (525089 / 2525089)) (n := 12)
    (lo := (422052769 / 1000000000)) (hi := (42205277 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1525089 / 1000000) = 1/(1000000 / 1525089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14330 : Bounds (422052769 / 1000000000) (42205277 / 100000000) (Real.log (1525089 / 1000000)) := by
  have h := reflection_log_14330_neg
  have he : Real.log (1525089 / 1000000) = -Real.log (1000000 / 1525089) := by
    rw [show ((1525089 / 1000000) : ℝ) = ((1000000 / 1525089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14331_neg : (37231393 / 50000000) ≤ -Real.log (474911 / 1000000) ∧
    -Real.log (474911 / 1000000) ≤ (372313931 / 500000000) := by
  have h := checkLog_sound (w := (25089 / 974911)) (n := 12)
    (lo := (1287017 / 25000000)) (hi := (51480681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 474911) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 474911) = 1/(474911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14331 : Bounds (-372313931 / 500000000) (-37231393 / 50000000) (Real.log (474911 / 1000000)) := by
  have h := reflection_log_14331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14332_neg : (212123149 / 500000000) ≤ -Real.log (500000 / 764219) ∧
    -Real.log (500000 / 764219) ≤ (424246299 / 1000000000) := by
  have h := checkLog_sound (w := (264219 / 1264219)) (n := 12)
    (lo := (212123149 / 500000000)) (hi := (424246299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764219 / 500000) = 1/(500000 / 764219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14332 : Bounds (212123149 / 500000000) (424246299 / 1000000000) (Real.log (764219 / 500000)) := by
  have h := reflection_log_14332_neg
  have he : Real.log (764219 / 500000) = -Real.log (500000 / 764219) := by
    rw [show ((764219 / 500000) : ℝ) = ((500000 / 764219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14333_neg : (751704689 / 1000000000) ≤ -Real.log (235781 / 500000) ∧
    -Real.log (235781 / 500000) ≤ (751704691 / 1000000000) := by
  have h := checkLog_sound (w := (14219 / 485781)) (n := 12)
    (lo := (58557509 / 1000000000)) (hi := (5855751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235781) = 1/(235781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14333 : Bounds (-751704691 / 1000000000) (-751704689 / 1000000000) (Real.log (235781 / 500000)) := by
  have h := reflection_log_14333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14334_neg : (327458391 / 1000000000) ≤ -Real.log (180188320039 / 250000000000) ∧
    -Real.log (180188320039 / 250000000000) ≤ (40932299 / 125000000) := by
  have h := checkLog_sound (w := (69811679961 / 430188320039)) (n := 12)
    (lo := (327458391 / 1000000000)) (hi := (40932299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 180188320039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 180188320039) = 1/(180188320039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14334 : Bounds (-40932299 / 125000000) (-327458391 / 1000000000) (Real.log (180188320039 / 250000000000)) := by
  have h := reflection_log_14334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14335_neg : (322575091 / 1000000000) ≤ -Real.log (724281542079 / 1000000000000) ∧
    -Real.log (724281542079 / 1000000000000) ≤ (80643773 / 250000000) := by
  have h := checkLog_sound (w := (275718457921 / 1724281542079)) (n := 12)
    (lo := (322575091 / 1000000000)) (hi := (80643773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 724281542079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 724281542079) = 1/(724281542079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14335 : Bounds (-80643773 / 250000000) (-322575091 / 1000000000) (Real.log (724281542079 / 1000000000000)) := by
  have h := reflection_log_14335_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
