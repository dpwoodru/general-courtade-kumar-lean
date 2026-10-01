import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7552_neg : (2484949 / 200000000) ≤ -Real.log (987652123359 / 1000000000000) ∧
    -Real.log (987652123359 / 1000000000000) ≤ (6212373 / 500000000) := by
  have h := checkLog_sound (w := (12347876641 / 1987652123359)) (n := 12)
    (lo := (2484949 / 200000000)) (hi := (6212373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987652123359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987652123359) = 1/(987652123359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7552 : Bounds (-6212373 / 500000000) (-2484949 / 200000000) (Real.log (987652123359 / 1000000000000)) := by
  have h := reflection_log_7552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7553_neg : (27895447 / 125000000) ≤ -Real.log (125000000000 / 156253128941) ∧
    -Real.log (125000000000 / 156253128941) ≤ (223163577 / 1000000000) := by
  have h := checkLog_sound (w := (31253128941 / 281253128941)) (n := 12)
    (lo := (27895447 / 125000000)) (hi := (223163577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156253128941 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156253128941 / 125000000000) = 1/(125000000000 / 156253128941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7553 : Bounds (27895447 / 125000000) (223163577 / 1000000000) (Real.log (156253128941 / 125000000000)) := by
  have h := reflection_log_7553_neg
  have he : Real.log (156253128941 / 125000000000) = -Real.log (125000000000 / 156253128941) := by
    rw [show ((156253128941 / 125000000000) : ℝ) = ((125000000000 / 156253128941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7554_neg : (22412753 / 100000000) ≤ -Real.log (250000000000 / 312807644729) ∧
    -Real.log (250000000000 / 312807644729) ≤ (224127531 / 1000000000) := by
  have h := checkLog_sound (w := (62807644729 / 562807644729)) (n := 12)
    (lo := (22412753 / 100000000)) (hi := (224127531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312807644729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312807644729 / 250000000000) = 1/(250000000000 / 312807644729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7554 : Bounds (22412753 / 100000000) (224127531 / 1000000000) (Real.log (312807644729 / 250000000000)) := by
  have h := reflection_log_7554_neg
  have he : Real.log (312807644729 / 250000000000) = -Real.log (250000000000 / 312807644729) := by
    rw [show ((312807644729 / 250000000000) : ℝ) = ((250000000000 / 312807644729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7555_neg : (448363201 / 1000000000) ≤ -Real.log (250000000000 / 391436818473) ∧
    -Real.log (250000000000 / 391436818473) ≤ (224181601 / 500000000) := by
  have h := checkLog_sound (w := (141436818473 / 641436818473)) (n := 12)
    (lo := (448363201 / 1000000000)) (hi := (224181601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391436818473 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391436818473 / 250000000000) = 1/(250000000000 / 391436818473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7555 : Bounds (448363201 / 1000000000) (224181601 / 500000000) (Real.log (391436818473 / 250000000000)) := by
  have h := reflection_log_7555_neg
  have he : Real.log (391436818473 / 250000000000) = -Real.log (250000000000 / 391436818473) := by
    rw [show ((391436818473 / 250000000000) : ℝ) = ((250000000000 / 391436818473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7556_neg : (112353607 / 250000000) ≤ -Real.log (500000000000 / 783697047497) ∧
    -Real.log (500000000000 / 783697047497) ≤ (449414429 / 1000000000) := by
  have h := checkLog_sound (w := (283697047497 / 1283697047497)) (n := 12)
    (lo := (112353607 / 250000000)) (hi := (449414429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783697047497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783697047497 / 500000000000) = 1/(500000000000 / 783697047497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7556 : Bounds (112353607 / 250000000) (449414429 / 1000000000) (Real.log (783697047497 / 500000000000)) := by
  have h := reflection_log_7556_neg
  have he : Real.log (783697047497 / 500000000000) = -Real.log (500000000000 / 783697047497) := by
    rw [show ((783697047497 / 500000000000) : ℝ) = ((500000000000 / 783697047497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7557_neg : (200079611 / 1000000000) ≤ -Real.log (2000 / 2443) ∧
    -Real.log (2000 / 2443) ≤ (50019903 / 250000000) := by
  have h := checkLog_sound (w := (443 / 4443)) (n := 12)
    (lo := (200079611 / 1000000000)) (hi := (50019903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 2000) = 1/(2000 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7557 : Bounds (200079611 / 1000000000) (50019903 / 250000000) (Real.log (2443 / 2000)) := by
  have h := reflection_log_7557_neg
  have he : Real.log (2443 / 2000) = -Real.log (2000 / 2443) := by
    rw [show ((2443 / 2000) : ℝ) = ((2000 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7558_neg : (250386287 / 1000000000) ≤ -Real.log (1557 / 2000) ∧
    -Real.log (1557 / 2000) ≤ (15649143 / 62500000) := by
  have h := checkLog_sound (w := (443 / 3557)) (n := 12)
    (lo := (250386287 / 1000000000)) (hi := (15649143 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1557) = 1/(1557 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7558 : Bounds (-15649143 / 62500000) (-250386287 / 1000000000) (Real.log (1557 / 2000)) := by
  have h := reflection_log_7558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7559_neg : (8859 / 40000000) ≤ -Real.log (2000000 / 2000443) ∧
    -Real.log (2000000 / 2000443) ≤ (55369 / 250000000) := by
  have h := checkLog_sound (w := (443 / 4000443)) (n := 12)
    (lo := (8859 / 40000000)) (hi := (55369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000443 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000443 / 2000000) = 1/(2000000 / 2000443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7559 : Bounds (8859 / 40000000) (55369 / 250000000) (Real.log (2000443 / 2000000)) := by
  have h := reflection_log_7559_neg
  have he : Real.log (2000443 / 2000000) = -Real.log (2000000 / 2000443) := by
    rw [show ((2000443 / 2000000) : ℝ) = ((2000000 / 2000443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7560_neg : (55381 / 250000000) ≤ -Real.log (1999557 / 2000000) ∧
    -Real.log (1999557 / 2000000) ≤ (8861 / 40000000) := by
  have h := checkLog_sound (w := (443 / 3999557)) (n := 12)
    (lo := (55381 / 250000000)) (hi := (8861 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999557) = 1/(1999557 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7560 : Bounds (-8861 / 40000000) (-55381 / 250000000) (Real.log (1999557 / 2000000)) := by
  have h := reflection_log_7560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7561_neg : (105599787 / 1000000000) ≤ -Real.log (1000000 / 1111377) ∧
    -Real.log (1000000 / 1111377) ≤ (26399947 / 250000000) := by
  have h := checkLog_sound (w := (111377 / 2111377)) (n := 12)
    (lo := (105599787 / 1000000000)) (hi := (26399947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111377 / 1000000) = 1/(1000000 / 1111377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7561 : Bounds (105599787 / 1000000000) (26399947 / 250000000) (Real.log (1111377 / 1000000)) := by
  have h := reflection_log_7561_neg
  have he : Real.log (1111377 / 1000000) = -Real.log (1000000 / 1111377) := by
    rw [show ((1111377 / 1000000) : ℝ) = ((1000000 / 1111377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7562_neg : (23616441 / 200000000) ≤ -Real.log (888623 / 1000000) ∧
    -Real.log (888623 / 1000000) ≤ (59041103 / 500000000) := by
  have h := checkLog_sound (w := (111377 / 1888623)) (n := 12)
    (lo := (23616441 / 200000000)) (hi := (59041103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888623) = 1/(888623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7562 : Bounds (-59041103 / 500000000) (-23616441 / 200000000) (Real.log (888623 / 1000000)) := by
  have h := reflection_log_7562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7563_neg : (26507223 / 250000000) ≤ -Real.log (500000 / 555927) ∧
    -Real.log (500000 / 555927) ≤ (106028893 / 1000000000) := by
  have h := checkLog_sound (w := (55927 / 1055927)) (n := 12)
    (lo := (26507223 / 250000000)) (hi := (106028893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(555927 / 500000) = 1/(500000 / 555927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7563 : Bounds (26507223 / 250000000) (106028893 / 1000000000) (Real.log (555927 / 500000)) := by
  have h := reflection_log_7563_neg
  have he : Real.log (555927 / 500000) = -Real.log (500000 / 555927) := by
    rw [show ((555927 / 500000) : ℝ) = ((500000 / 555927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7564_neg : (23723827 / 200000000) ≤ -Real.log (444073 / 500000) ∧
    -Real.log (444073 / 500000) ≤ (231678 / 1953125) := by
  have h := checkLog_sound (w := (55927 / 944073)) (n := 12)
    (lo := (23723827 / 200000000)) (hi := (231678 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 444073) = 1/(444073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7564 : Bounds (-231678 / 1953125) (-23723827 / 200000000) (Real.log (444073 / 500000)) := by
  have h := reflection_log_7564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7565_neg : (6295121 / 500000000) ≤ -Real.log (246872170671 / 250000000000) ∧
    -Real.log (246872170671 / 250000000000) ≤ (12590243 / 1000000000) := by
  have h := checkLog_sound (w := (3127829329 / 496872170671)) (n := 12)
    (lo := (6295121 / 500000000)) (hi := (12590243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246872170671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246872170671) = 1/(246872170671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7565 : Bounds (-12590243 / 1000000000) (-6295121 / 500000000) (Real.log (246872170671 / 250000000000)) := by
  have h := reflection_log_7565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7566_neg : (6241209 / 500000000) ≤ -Real.log (987595163871 / 1000000000000) ∧
    -Real.log (987595163871 / 1000000000000) ≤ (12482419 / 1000000000) := by
  have h := checkLog_sound (w := (12404836129 / 1987595163871)) (n := 12)
    (lo := (6241209 / 500000000)) (hi := (12482419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987595163871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987595163871) = 1/(987595163871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7566 : Bounds (-12482419 / 1000000000) (-6241209 / 500000000) (Real.log (987595163871 / 1000000000000)) := by
  have h := reflection_log_7566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7567_neg : (27960249 / 125000000) ≤ -Real.log (100000000000 / 125067323263) ∧
    -Real.log (100000000000 / 125067323263) ≤ (223681993 / 1000000000) := by
  have h := checkLog_sound (w := (25067323263 / 225067323263)) (n := 12)
    (lo := (27960249 / 125000000)) (hi := (223681993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125067323263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125067323263 / 100000000000) = 1/(100000000000 / 125067323263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7567 : Bounds (27960249 / 125000000) (223681993 / 1000000000) (Real.log (125067323263 / 100000000000)) := by
  have h := reflection_log_7567_neg
  have he : Real.log (125067323263 / 100000000000) = -Real.log (100000000000 / 125067323263) := by
    rw [show ((125067323263 / 100000000000) : ℝ) = ((100000000000 / 125067323263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7568_neg : (224648027 / 1000000000) ≤ -Real.log (125000000000 / 156485251299) ∧
    -Real.log (125000000000 / 156485251299) ≤ (56162007 / 250000000) := by
  have h := checkLog_sound (w := (31485251299 / 281485251299)) (n := 12)
    (lo := (224648027 / 1000000000)) (hi := (56162007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156485251299 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156485251299 / 125000000000) = 1/(125000000000 / 156485251299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7568 : Bounds (224648027 / 1000000000) (56162007 / 250000000) (Real.log (156485251299 / 125000000000)) := by
  have h := reflection_log_7568_neg
  have he : Real.log (156485251299 / 125000000000) = -Real.log (125000000000 / 156485251299) := by
    rw [show ((156485251299 / 125000000000) : ℝ) = ((125000000000 / 156485251299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7569_neg : (112353607 / 250000000) ≤ -Real.log (62500000000 / 97962130937) ∧
    -Real.log (62500000000 / 97962130937) ≤ (449414429 / 1000000000) := by
  have h := checkLog_sound (w := (35462130937 / 160462130937)) (n := 12)
    (lo := (112353607 / 250000000)) (hi := (449414429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97962130937 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97962130937 / 62500000000) = 1/(62500000000 / 97962130937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7569 : Bounds (112353607 / 250000000) (449414429 / 1000000000) (Real.log (97962130937 / 62500000000)) := by
  have h := reflection_log_7569_neg
  have he : Real.log (97962130937 / 62500000000) = -Real.log (62500000000 / 97962130937) := by
    rw [show ((97962130937 / 62500000000) : ℝ) = ((62500000000 / 97962130937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7570_neg : (450465899 / 1000000000) ≤ -Real.log (62500000000 / 98065189467) ∧
    -Real.log (62500000000 / 98065189467) ≤ (4504659 / 10000000) := by
  have h := checkLog_sound (w := (35565189467 / 160565189467)) (n := 12)
    (lo := (450465899 / 1000000000)) (hi := (4504659 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98065189467 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98065189467 / 62500000000) = 1/(62500000000 / 98065189467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7570 : Bounds (450465899 / 1000000000) (4504659 / 10000000) (Real.log (98065189467 / 62500000000)) := by
  have h := reflection_log_7570_neg
  have he : Real.log (98065189467 / 62500000000) = -Real.log (62500000000 / 98065189467) := by
    rw [show ((98065189467 / 62500000000) : ℝ) = ((62500000000 / 98065189467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7571_neg : (10024443 / 50000000) ≤ -Real.log (500 / 611) ∧
    -Real.log (500 / 611) ≤ (200488861 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 1111)) (n := 12)
    (lo := (10024443 / 50000000)) (hi := (200488861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611 / 500) = 1/(500 / 611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7571 : Bounds (10024443 / 50000000) (200488861 / 1000000000) (Real.log (611 / 500)) := by
  have h := reflection_log_7571_neg
  have he : Real.log (611 / 500) = -Real.log (500 / 611) := by
    rw [show ((611 / 500) : ℝ) = ((500 / 611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7572_neg : (125514377 / 500000000) ≤ -Real.log (389 / 500) ∧
    -Real.log (389 / 500) ≤ (50205751 / 200000000) := by
  have h := checkLog_sound (w := (111 / 889)) (n := 12)
    (lo := (125514377 / 500000000)) (hi := (50205751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 389) = 1/(389 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7572 : Bounds (-50205751 / 200000000) (-125514377 / 500000000) (Real.log (389 / 500)) := by
  have h := reflection_log_7572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7573_neg : (8879 / 40000000) ≤ -Real.log (500000 / 500111) ∧
    -Real.log (500000 / 500111) ≤ (27747 / 125000000) := by
  have h := checkLog_sound (w := (111 / 1000111)) (n := 12)
    (lo := (8879 / 40000000)) (hi := (27747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500111 / 500000) = 1/(500000 / 500111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7573 : Bounds (8879 / 40000000) (27747 / 125000000) (Real.log (500111 / 500000)) := by
  have h := reflection_log_7573_neg
  have he : Real.log (500111 / 500000) = -Real.log (500000 / 500111) := by
    rw [show ((500111 / 500000) : ℝ) = ((500000 / 500111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7574_neg : (27753 / 125000000) ≤ -Real.log (499889 / 500000) ∧
    -Real.log (499889 / 500000) ≤ (8881 / 40000000) := by
  have h := checkLog_sound (w := (111 / 999889)) (n := 12)
    (lo := (27753 / 125000000)) (hi := (8881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499889) = 1/(499889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7574 : Bounds (-8881 / 40000000) (-27753 / 125000000) (Real.log (499889 / 500000)) := by
  have h := reflection_log_7574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7575_neg : (26457751 / 250000000) ≤ -Real.log (500000 / 555817) ∧
    -Real.log (500000 / 555817) ≤ (21166201 / 200000000) := by
  have h := checkLog_sound (w := (55817 / 1055817)) (n := 12)
    (lo := (26457751 / 250000000)) (hi := (21166201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(555817 / 500000) = 1/(500000 / 555817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7575 : Bounds (26457751 / 250000000) (21166201 / 200000000) (Real.log (555817 / 500000)) := by
  have h := reflection_log_7575_neg
  have he : Real.log (555817 / 500000) = -Real.log (500000 / 555817) := by
    rw [show ((555817 / 500000) : ℝ) = ((500000 / 555817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7576_neg : (59185729 / 500000000) ≤ -Real.log (444183 / 500000) ∧
    -Real.log (444183 / 500000) ≤ (118371459 / 1000000000) := by
  have h := checkLog_sound (w := (55817 / 944183)) (n := 12)
    (lo := (59185729 / 500000000)) (hi := (118371459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 444183) = 1/(444183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7576 : Bounds (-118371459 / 1000000000) (-59185729 / 500000000) (Real.log (444183 / 500000)) := by
  have h := reflection_log_7576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7577_neg : (10626091 / 100000000) ≤ -Real.log (62500 / 69507) ∧
    -Real.log (62500 / 69507) ≤ (106260911 / 1000000000) := by
  have h := checkLog_sound (w := (7007 / 132007)) (n := 12)
    (lo := (10626091 / 100000000)) (hi := (106260911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69507 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69507 / 62500) = 1/(62500 / 69507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7577 : Bounds (10626091 / 100000000) (106260911 / 1000000000) (Real.log (69507 / 62500)) := by
  have h := reflection_log_7577_neg
  have he : Real.log (69507 / 62500) = -Real.log (62500 / 69507) := by
    rw [show ((69507 / 62500) : ℝ) = ((62500 / 69507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7578_neg : (11890967 / 100000000) ≤ -Real.log (55493 / 62500) ∧
    -Real.log (55493 / 62500) ≤ (118909671 / 1000000000) := by
  have h := checkLog_sound (w := (7007 / 117993)) (n := 12)
    (lo := (11890967 / 100000000)) (hi := (118909671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55493) = 1/(55493 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7578 : Bounds (-118909671 / 1000000000) (-11890967 / 100000000) (Real.log (55493 / 62500)) := by
  have h := reflection_log_7578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7579_neg : (12648759 / 1000000000) ≤ -Real.log (3857151951 / 3906250000) ∧
    -Real.log (3857151951 / 3906250000) ≤ (316219 / 25000000) := by
  have h := checkLog_sound (w := (49098049 / 7763401951)) (n := 12)
    (lo := (12648759 / 1000000000)) (hi := (316219 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3857151951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3857151951) = 1/(3857151951 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7579 : Bounds (-316219 / 25000000) (-12648759 / 1000000000) (Real.log (3857151951 / 3906250000)) := by
  have h := reflection_log_7579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7580_neg : (12540453 / 1000000000) ≤ -Real.log (246884462511 / 250000000000) ∧
    -Real.log (246884462511 / 250000000000) ≤ (6270227 / 500000000) := by
  have h := checkLog_sound (w := (3115537489 / 496884462511)) (n := 12)
    (lo := (12540453 / 1000000000)) (hi := (6270227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246884462511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246884462511) = 1/(246884462511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7580 : Bounds (-6270227 / 500000000) (-12540453 / 1000000000) (Real.log (246884462511 / 250000000000)) := by
  have h := reflection_log_7580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7581_neg : (224202463 / 1000000000) ≤ -Real.log (500000000000 / 625662170771) ∧
    -Real.log (500000000000 / 625662170771) ≤ (7006327 / 31250000) := by
  have h := checkLog_sound (w := (125662170771 / 1125662170771)) (n := 12)
    (lo := (224202463 / 1000000000)) (hi := (7006327 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625662170771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625662170771 / 500000000000) = 1/(500000000000 / 625662170771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7581 : Bounds (224202463 / 1000000000) (7006327 / 31250000) (Real.log (625662170771 / 500000000000)) := by
  have h := reflection_log_7581_neg
  have he : Real.log (625662170771 / 500000000000) = -Real.log (500000000000 / 625662170771) := by
    rw [show ((625662170771 / 500000000000) : ℝ) = ((500000000000 / 625662170771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7582_neg : (11258529 / 50000000) ≤ -Real.log (500000000000 / 626268177969) ∧
    -Real.log (500000000000 / 626268177969) ≤ (225170581 / 1000000000) := by
  have h := checkLog_sound (w := (126268177969 / 1126268177969)) (n := 12)
    (lo := (11258529 / 50000000)) (hi := (225170581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626268177969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626268177969 / 500000000000) = 1/(500000000000 / 626268177969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7582 : Bounds (11258529 / 50000000) (225170581 / 1000000000) (Real.log (626268177969 / 500000000000)) := by
  have h := reflection_log_7582_neg
  have he : Real.log (626268177969 / 500000000000) = -Real.log (500000000000 / 626268177969) := by
    rw [show ((626268177969 / 500000000000) : ℝ) = ((500000000000 / 626268177969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7583_neg : (450465899 / 1000000000) ≤ -Real.log (100000000000 / 156904303147) ∧
    -Real.log (100000000000 / 156904303147) ≤ (4504659 / 10000000) := by
  have h := checkLog_sound (w := (56904303147 / 256904303147)) (n := 12)
    (lo := (450465899 / 1000000000)) (hi := (4504659 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156904303147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156904303147 / 100000000000) = 1/(100000000000 / 156904303147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7583 : Bounds (450465899 / 1000000000) (4504659 / 10000000) (Real.log (156904303147 / 100000000000)) := by
  have h := reflection_log_7583_neg
  have he : Real.log (156904303147 / 100000000000) = -Real.log (100000000000 / 156904303147) := by
    rw [show ((156904303147 / 100000000000) : ℝ) = ((100000000000 / 156904303147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7584_neg : (90303523 / 200000000) ≤ -Real.log (250000000000 / 392673521851) ∧
    -Real.log (250000000000 / 392673521851) ≤ (28219851 / 62500000) := by
  have h := checkLog_sound (w := (142673521851 / 642673521851)) (n := 12)
    (lo := (90303523 / 200000000)) (hi := (28219851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392673521851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392673521851 / 250000000000) = 1/(250000000000 / 392673521851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7584 : Bounds (90303523 / 200000000) (28219851 / 62500000) (Real.log (392673521851 / 250000000000)) := by
  have h := reflection_log_7584_neg
  have he : Real.log (392673521851 / 250000000000) = -Real.log (250000000000 / 392673521851) := by
    rw [show ((392673521851 / 250000000000) : ℝ) = ((250000000000 / 392673521851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7585_neg : (100448971 / 500000000) ≤ -Real.log (400 / 489) ∧
    -Real.log (400 / 489) ≤ (200897943 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 889)) (n := 12)
    (lo := (100448971 / 500000000)) (hi := (200897943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489 / 400) = 1/(400 / 489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7585 : Bounds (100448971 / 500000000) (200897943 / 1000000000) (Real.log (489 / 400)) := by
  have h := reflection_log_7585_neg
  have he : Real.log (489 / 400) = -Real.log (400 / 489) := by
    rw [show ((489 / 400) : ℝ) = ((400 / 489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7586_neg : (125835817 / 500000000) ≤ -Real.log (311 / 400) ∧
    -Real.log (311 / 400) ≤ (50334327 / 200000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 311) = 1/(311 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7586 : Bounds (-50334327 / 200000000) (-125835817 / 500000000) (Real.log (311 / 400)) := by
  have h := reflection_log_7586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7587_neg : (8899 / 40000000) ≤ -Real.log (400000 / 400089) ∧
    -Real.log (400000 / 400089) ≤ (55619 / 250000000) := by
  have h := checkLog_sound (w := (89 / 800089)) (n := 12)
    (lo := (8899 / 40000000)) (hi := (55619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400089 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400089 / 400000) = 1/(400000 / 400089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7587 : Bounds (8899 / 40000000) (55619 / 250000000) (Real.log (400089 / 400000)) := by
  have h := reflection_log_7587_neg
  have he : Real.log (400089 / 400000) = -Real.log (400000 / 400089) := by
    rw [show ((400089 / 400000) : ℝ) = ((400000 / 400089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7588_neg : (55631 / 250000000) ≤ -Real.log (399911 / 400000) ∧
    -Real.log (399911 / 400000) ≤ (8901 / 40000000) := by
  have h := checkLog_sound (w := (89 / 799911)) (n := 12)
    (lo := (55631 / 250000000)) (hi := (8901 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399911) = 1/(399911 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7588 : Bounds (-8901 / 40000000) (-55631 / 250000000) (Real.log (399911 / 400000)) := by
  have h := reflection_log_7588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7589_neg : (106062169 / 1000000000) ≤ -Real.log (1000000 / 1111891) ∧
    -Real.log (1000000 / 1111891) ≤ (10606217 / 100000000) := by
  have h := checkLog_sound (w := (111891 / 2111891)) (n := 12)
    (lo := (106062169 / 1000000000)) (hi := (10606217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111891 / 1000000) = 1/(1000000 / 1111891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7589 : Bounds (106062169 / 1000000000) (10606217 / 100000000) (Real.log (1111891 / 1000000)) := by
  have h := reflection_log_7589_neg
  have he : Real.log (1111891 / 1000000) = -Real.log (1000000 / 1111891) := by
    rw [show ((1111891 / 1000000) : ℝ) = ((1000000 / 1111891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7590_neg : (23732159 / 200000000) ≤ -Real.log (888109 / 1000000) ∧
    -Real.log (888109 / 1000000) ≤ (29665199 / 250000000) := by
  have h := checkLog_sound (w := (111891 / 1888109)) (n := 12)
    (lo := (23732159 / 200000000)) (hi := (29665199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888109) = 1/(888109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7590 : Bounds (-29665199 / 250000000) (-23732159 / 200000000) (Real.log (888109 / 1000000)) := by
  have h := reflection_log_7590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7591_neg : (4259679 / 40000000) ≤ -Real.log (1000000 / 1112369) ∧
    -Real.log (1000000 / 1112369) ≤ (13311497 / 125000000) := by
  have h := checkLog_sound (w := (112369 / 2112369)) (n := 12)
    (lo := (4259679 / 40000000)) (hi := (13311497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112369 / 1000000) = 1/(1000000 / 1112369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7591 : Bounds (4259679 / 40000000) (13311497 / 125000000) (Real.log (1112369 / 1000000)) := by
  have h := reflection_log_7591_neg
  have he : Real.log (1112369 / 1000000) = -Real.log (1000000 / 1112369) := by
    rw [show ((1112369 / 1000000) : ℝ) = ((1000000 / 1112369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7592_neg : (59599581 / 500000000) ≤ -Real.log (887631 / 1000000) ∧
    -Real.log (887631 / 1000000) ≤ (119199163 / 1000000000) := by
  have h := checkLog_sound (w := (112369 / 1887631)) (n := 12)
    (lo := (59599581 / 500000000)) (hi := (119199163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887631) = 1/(887631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7592 : Bounds (-119199163 / 1000000000) (-59599581 / 500000000) (Real.log (887631 / 1000000)) := by
  have h := reflection_log_7592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7593_neg : (12707187 / 1000000000) ≤ -Real.log (987373207839 / 1000000000000) ∧
    -Real.log (987373207839 / 1000000000000) ≤ (3176797 / 250000000) := by
  have h := checkLog_sound (w := (12626792161 / 1987373207839)) (n := 12)
    (lo := (12707187 / 1000000000)) (hi := (3176797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987373207839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987373207839) = 1/(987373207839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7593 : Bounds (-3176797 / 250000000) (-12707187 / 1000000000) (Real.log (987373207839 / 1000000000000)) := by
  have h := reflection_log_7593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7594_neg : (6299313 / 500000000) ≤ -Real.log (987480404119 / 1000000000000) ∧
    -Real.log (987480404119 / 1000000000000) ≤ (12598627 / 1000000000) := by
  have h := checkLog_sound (w := (12519595881 / 1987480404119)) (n := 12)
    (lo := (6299313 / 500000000)) (hi := (12598627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987480404119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987480404119) = 1/(987480404119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7594 : Bounds (-12598627 / 1000000000) (-6299313 / 500000000) (Real.log (987480404119 / 1000000000000)) := by
  have h := reflection_log_7594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7595_neg : (44944593 / 200000000) ≤ -Real.log (100000000000 / 125197582729) ∧
    -Real.log (100000000000 / 125197582729) ≤ (112361483 / 500000000) := by
  have h := checkLog_sound (w := (25197582729 / 225197582729)) (n := 12)
    (lo := (44944593 / 200000000)) (hi := (112361483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125197582729 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125197582729 / 100000000000) = 1/(100000000000 / 125197582729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7595 : Bounds (44944593 / 200000000) (112361483 / 500000000) (Real.log (125197582729 / 100000000000)) := by
  have h := reflection_log_7595_neg
  have he : Real.log (125197582729 / 100000000000) = -Real.log (100000000000 / 125197582729) := by
    rw [show ((125197582729 / 100000000000) : ℝ) = ((100000000000 / 125197582729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7596_neg : (112845569 / 500000000) ≤ -Real.log (500000000000 / 626594271719) ∧
    -Real.log (500000000000 / 626594271719) ≤ (225691139 / 1000000000) := by
  have h := checkLog_sound (w := (126594271719 / 1126594271719)) (n := 12)
    (lo := (112845569 / 500000000)) (hi := (225691139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626594271719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626594271719 / 500000000000) = 1/(500000000000 / 626594271719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7596 : Bounds (112845569 / 500000000) (225691139 / 1000000000) (Real.log (626594271719 / 500000000000)) := by
  have h := reflection_log_7596_neg
  have he : Real.log (626594271719 / 500000000000) = -Real.log (500000000000 / 626594271719) := by
    rw [show ((626594271719 / 500000000000) : ℝ) = ((500000000000 / 626594271719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7597_neg : (90303523 / 200000000) ≤ -Real.log (500000000000 / 785347043701) ∧
    -Real.log (500000000000 / 785347043701) ≤ (28219851 / 62500000) := by
  have h := checkLog_sound (w := (285347043701 / 1285347043701)) (n := 12)
    (lo := (90303523 / 200000000)) (hi := (28219851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785347043701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785347043701 / 500000000000) = 1/(500000000000 / 785347043701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7597 : Bounds (90303523 / 200000000) (28219851 / 62500000) (Real.log (785347043701 / 500000000000)) := by
  have h := reflection_log_7597_neg
  have he : Real.log (785347043701 / 500000000000) = -Real.log (500000000000 / 785347043701) := by
    rw [show ((785347043701 / 500000000000) : ℝ) = ((500000000000 / 785347043701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7598_neg : (452569577 / 1000000000) ≤ -Real.log (500000000000 / 786173633441) ∧
    -Real.log (500000000000 / 786173633441) ≤ (226284789 / 500000000) := by
  have h := checkLog_sound (w := (286173633441 / 1286173633441)) (n := 12)
    (lo := (452569577 / 1000000000)) (hi := (226284789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786173633441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786173633441 / 500000000000) = 1/(500000000000 / 786173633441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7598 : Bounds (452569577 / 1000000000) (226284789 / 500000000) (Real.log (786173633441 / 500000000000)) := by
  have h := reflection_log_7598_neg
  have he : Real.log (786173633441 / 500000000000) = -Real.log (500000000000 / 786173633441) := by
    rw [show ((786173633441 / 500000000000) : ℝ) = ((500000000000 / 786173633441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7599_neg : (25163357 / 125000000) ≤ -Real.log (1000 / 1223) ∧
    -Real.log (1000 / 1223) ≤ (201306857 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2223)) (n := 12)
    (lo := (25163357 / 125000000)) (hi := (201306857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 1000) = 1/(1000 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7599 : Bounds (25163357 / 125000000) (201306857 / 1000000000) (Real.log (1223 / 1000)) := by
  have h := reflection_log_7599_neg
  have he : Real.log (1223 / 1000) = -Real.log (1000 / 1223) := by
    rw [show ((1223 / 1000) : ℝ) = ((1000 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7600_neg : (15769683 / 62500000) ≤ -Real.log (777 / 1000) ∧
    -Real.log (777 / 1000) ≤ (252314929 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1777)) (n := 12)
    (lo := (15769683 / 62500000)) (hi := (252314929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 777) = 1/(777 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7600 : Bounds (-252314929 / 1000000000) (-15769683 / 62500000) (Real.log (777 / 1000)) := by
  have h := reflection_log_7600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7601_neg : (8919 / 40000000) ≤ -Real.log (1000000 / 1000223) ∧
    -Real.log (1000000 / 1000223) ≤ (871 / 3906250) := by
  have h := checkLog_sound (w := (223 / 2000223)) (n := 12)
    (lo := (8919 / 40000000)) (hi := (871 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000223 / 1000000) = 1/(1000000 / 1000223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7601 : Bounds (8919 / 40000000) (871 / 3906250) (Real.log (1000223 / 1000000)) := by
  have h := reflection_log_7601_neg
  have he : Real.log (1000223 / 1000000) = -Real.log (1000000 / 1000223) := by
    rw [show ((1000223 / 1000000) : ℝ) = ((1000000 / 1000223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7602_neg : (13939 / 62500000) ≤ -Real.log (999777 / 1000000) ∧
    -Real.log (999777 / 1000000) ≤ (8921 / 40000000) := by
  have h := checkLog_sound (w := (223 / 1999777)) (n := 12)
    (lo := (13939 / 62500000)) (hi := (8921 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999777) = 1/(999777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7602 : Bounds (-8921 / 40000000) (-13939 / 62500000) (Real.log (999777 / 1000000)) := by
  have h := reflection_log_7602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7603_neg : (106292381 / 1000000000) ≤ -Real.log (1000000 / 1112147) ∧
    -Real.log (1000000 / 1112147) ≤ (53146191 / 500000000) := by
  have h := checkLog_sound (w := (112147 / 2112147)) (n := 12)
    (lo := (106292381 / 1000000000)) (hi := (53146191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112147 / 1000000) = 1/(1000000 / 1112147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7603 : Bounds (106292381 / 1000000000) (53146191 / 500000000) (Real.log (1112147 / 1000000)) := by
  have h := reflection_log_7603_neg
  have he : Real.log (1112147 / 1000000) = -Real.log (1000000 / 1112147) := by
    rw [show ((1112147 / 1000000) : ℝ) = ((1000000 / 1112147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7604_neg : (11894909 / 100000000) ≤ -Real.log (887853 / 1000000) ∧
    -Real.log (887853 / 1000000) ≤ (118949091 / 1000000000) := by
  have h := checkLog_sound (w := (112147 / 1887853)) (n := 12)
    (lo := (11894909 / 100000000)) (hi := (118949091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887853) = 1/(887853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7604 : Bounds (-118949091 / 1000000000) (-11894909 / 100000000) (Real.log (887853 / 1000000)) := by
  have h := reflection_log_7604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7605_neg : (106722987 / 1000000000) ≤ -Real.log (500000 / 556313) ∧
    -Real.log (500000 / 556313) ≤ (26680747 / 250000000) := by
  have h := checkLog_sound (w := (56313 / 1056313)) (n := 12)
    (lo := (106722987 / 1000000000)) (hi := (26680747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(556313 / 500000) = 1/(500000 / 556313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7605 : Bounds (106722987 / 1000000000) (26680747 / 250000000) (Real.log (556313 / 500000)) := by
  have h := reflection_log_7605_neg
  have he : Real.log (556313 / 500000) = -Real.log (500000 / 556313) := by
    rw [show ((556313 / 500000) : ℝ) = ((500000 / 556313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7606_neg : (119488739 / 1000000000) ≤ -Real.log (443687 / 500000) ∧
    -Real.log (443687 / 500000) ≤ (5974437 / 50000000) := by
  have h := checkLog_sound (w := (56313 / 943687)) (n := 12)
    (lo := (119488739 / 1000000000)) (hi := (5974437 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 443687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 443687) = 1/(443687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7606 : Bounds (-5974437 / 50000000) (-119488739 / 1000000000) (Real.log (443687 / 500000)) := by
  have h := reflection_log_7606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7607_neg : (1595719 / 125000000) ≤ -Real.log (246828846031 / 250000000000) ∧
    -Real.log (246828846031 / 250000000000) ≤ (12765753 / 1000000000) := by
  have h := checkLog_sound (w := (3171153969 / 496828846031)) (n := 12)
    (lo := (1595719 / 125000000)) (hi := (12765753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246828846031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246828846031) = 1/(246828846031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7607 : Bounds (-12765753 / 1000000000) (-1595719 / 125000000) (Real.log (246828846031 / 250000000000)) := by
  have h := reflection_log_7607_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7608_neg : (3164177 / 250000000) ≤ -Real.log (987423050391 / 1000000000000) ∧
    -Real.log (987423050391 / 1000000000000) ≤ (12656709 / 1000000000) := by
  have h := checkLog_sound (w := (12576949609 / 1987423050391)) (n := 12)
    (lo := (3164177 / 250000000)) (hi := (12656709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987423050391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987423050391) = 1/(987423050391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7608 : Bounds (-12656709 / 1000000000) (-3164177 / 250000000) (Real.log (987423050391 / 1000000000000)) := by
  have h := reflection_log_7608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7609_neg : (225241471 / 1000000000) ≤ -Real.log (250000000000 / 313156288259) ∧
    -Real.log (250000000000 / 313156288259) ≤ (1759699 / 7812500) := by
  have h := checkLog_sound (w := (63156288259 / 563156288259)) (n := 12)
    (lo := (225241471 / 1000000000)) (hi := (1759699 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313156288259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313156288259 / 250000000000) = 1/(250000000000 / 313156288259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7609 : Bounds (225241471 / 1000000000) (1759699 / 7812500) (Real.log (313156288259 / 250000000000)) := by
  have h := reflection_log_7609_neg
  have he : Real.log (313156288259 / 250000000000) = -Real.log (250000000000 / 313156288259) := by
    rw [show ((313156288259 / 250000000000) : ℝ) = ((250000000000 / 313156288259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7610_neg : (113105863 / 500000000) ≤ -Real.log (100000000000 / 125384110871) ∧
    -Real.log (100000000000 / 125384110871) ≤ (226211727 / 1000000000) := by
  have h := checkLog_sound (w := (25384110871 / 225384110871)) (n := 12)
    (lo := (113105863 / 500000000)) (hi := (226211727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125384110871 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125384110871 / 100000000000) = 1/(100000000000 / 125384110871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7610 : Bounds (113105863 / 500000000) (226211727 / 1000000000) (Real.log (125384110871 / 100000000000)) := by
  have h := reflection_log_7610_neg
  have he : Real.log (125384110871 / 100000000000) = -Real.log (100000000000 / 125384110871) := by
    rw [show ((125384110871 / 100000000000) : ℝ) = ((100000000000 / 125384110871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7611_neg : (452569577 / 1000000000) ≤ -Real.log (3125000000 / 4913585209) ∧
    -Real.log (3125000000 / 4913585209) ≤ (226284789 / 500000000) := by
  have h := checkLog_sound (w := (1788585209 / 8038585209)) (n := 12)
    (lo := (452569577 / 1000000000)) (hi := (226284789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913585209 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913585209 / 3125000000) = 1/(3125000000 / 4913585209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7611 : Bounds (452569577 / 1000000000) (226284789 / 500000000) (Real.log (4913585209 / 3125000000)) := by
  have h := reflection_log_7611_neg
  have he : Real.log (4913585209 / 3125000000) = -Real.log (3125000000 / 4913585209) := by
    rw [show ((4913585209 / 3125000000) : ℝ) = ((3125000000 / 4913585209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7612_neg : (90724357 / 200000000) ≤ -Real.log (250000000000 / 393500643501) ∧
    -Real.log (250000000000 / 393500643501) ≤ (226810893 / 500000000) := by
  have h := checkLog_sound (w := (143500643501 / 643500643501)) (n := 12)
    (lo := (90724357 / 200000000)) (hi := (226810893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393500643501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393500643501 / 250000000000) = 1/(250000000000 / 393500643501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7612 : Bounds (90724357 / 200000000) (226810893 / 500000000) (Real.log (393500643501 / 250000000000)) := by
  have h := reflection_log_7612_neg
  have he : Real.log (393500643501 / 250000000000) = -Real.log (250000000000 / 393500643501) := by
    rw [show ((393500643501 / 250000000000) : ℝ) = ((250000000000 / 393500643501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7613_neg : (201715603 / 1000000000) ≤ -Real.log (2000 / 2447) ∧
    -Real.log (2000 / 2447) ≤ (50428901 / 250000000) := by
  have h := checkLog_sound (w := (447 / 4447)) (n := 12)
    (lo := (201715603 / 1000000000)) (hi := (50428901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 2000) = 1/(2000 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7613 : Bounds (201715603 / 1000000000) (50428901 / 250000000) (Real.log (2447 / 2000)) := by
  have h := reflection_log_7613_neg
  have he : Real.log (2447 / 2000) = -Real.log (2000 / 2447) := by
    rw [show ((2447 / 2000) : ℝ) = ((2000 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7614_neg : (63239659 / 250000000) ≤ -Real.log (1553 / 2000) ∧
    -Real.log (1553 / 2000) ≤ (252958637 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 3553)) (n := 12)
    (lo := (63239659 / 250000000)) (hi := (252958637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1553) = 1/(1553 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7614 : Bounds (-252958637 / 1000000000) (-63239659 / 250000000) (Real.log (1553 / 2000)) := by
  have h := reflection_log_7614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7615_neg : (8939 / 40000000) ≤ -Real.log (2000000 / 2000447) ∧
    -Real.log (2000000 / 2000447) ≤ (55869 / 250000000) := by
  have h := checkLog_sound (w := (447 / 4000447)) (n := 12)
    (lo := (8939 / 40000000)) (hi := (55869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000447 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000447 / 2000000) = 1/(2000000 / 2000447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7615 : Bounds (8939 / 40000000) (55869 / 250000000) (Real.log (2000447 / 2000000)) := by
  have h := reflection_log_7615_neg
  have he : Real.log (2000447 / 2000000) = -Real.log (2000000 / 2000447) := by
    rw [show ((2000447 / 2000000) : ℝ) = ((2000000 / 2000447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
