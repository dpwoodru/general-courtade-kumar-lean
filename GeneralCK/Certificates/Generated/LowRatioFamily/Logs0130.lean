import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8320_neg : (2688533 / 20000000) ≤ -Real.log (874217 / 1000000) ∧
    -Real.log (874217 / 1000000) ≤ (134426651 / 1000000000) := by
  have h := checkLog_sound (w := (125783 / 1874217)) (n := 12)
    (lo := (2688533 / 20000000)) (hi := (134426651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 874217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 874217) = 1/(874217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8320 : Bounds (-134426651 / 1000000000) (-2688533 / 20000000) (Real.log (874217 / 1000000)) := by
  have h := reflection_log_8320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8321_neg : (996741 / 62500000) ≤ -Real.log (984178636911 / 1000000000000) ∧
    -Real.log (984178636911 / 1000000000000) ≤ (15947857 / 1000000000) := by
  have h := checkLog_sound (w := (15821363089 / 1984178636911)) (n := 12)
    (lo := (996741 / 62500000)) (hi := (15947857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984178636911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984178636911) = 1/(984178636911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8321 : Bounds (-15947857 / 1000000000) (-996741 / 62500000) (Real.log (984178636911 / 1000000000000)) := by
  have h := reflection_log_8321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8322_neg : (15819041 / 1000000000) ≤ -Real.log (246076355679 / 250000000000) ∧
    -Real.log (246076355679 / 250000000000) ≤ (7909521 / 500000000) := by
  have h := checkLog_sound (w := (3923644321 / 496076355679)) (n := 12)
    (lo := (15819041 / 1000000000)) (hi := (7909521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246076355679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246076355679) = 1/(246076355679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8322 : Bounds (-7909521 / 500000000) (-15819041 / 1000000000) (Real.log (246076355679 / 250000000000)) := by
  have h := reflection_log_8322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8323_neg : (251879273 / 1000000000) ≤ -Real.log (500000000000 / 643220360297) ∧
    -Real.log (500000000000 / 643220360297) ≤ (125939637 / 500000000) := by
  have h := checkLog_sound (w := (143220360297 / 1143220360297)) (n := 12)
    (lo := (251879273 / 1000000000)) (hi := (125939637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643220360297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643220360297 / 500000000000) = 1/(500000000000 / 643220360297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8323 : Bounds (251879273 / 1000000000) (125939637 / 500000000) (Real.log (643220360297 / 500000000000)) := by
  have h := reflection_log_8323_neg
  have he : Real.log (643220360297 / 500000000000) = -Real.log (500000000000 / 643220360297) := by
    rw [show ((643220360297 / 500000000000) : ℝ) = ((500000000000 / 643220360297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8324_neg : (252905443 / 1000000000) ≤ -Real.log (6250000000 / 8048509409) ∧
    -Real.log (6250000000 / 8048509409) ≤ (63226361 / 250000000) := by
  have h := checkLog_sound (w := (1798509409 / 14298509409)) (n := 12)
    (lo := (252905443 / 1000000000)) (hi := (63226361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8048509409 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8048509409 / 6250000000) = 1/(6250000000 / 8048509409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8324 : Bounds (252905443 / 1000000000) (63226361 / 250000000) (Real.log (8048509409 / 6250000000)) := by
  have h := reflection_log_8324_neg
  have he : Real.log (8048509409 / 6250000000) = -Real.log (6250000000 / 8048509409) := by
    rw [show ((8048509409 / 6250000000) : ℝ) = ((6250000000 / 8048509409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8325_neg : (63320153 / 125000000) ≤ -Real.log (250000000000 / 414893617021) ∧
    -Real.log (250000000000 / 414893617021) ≤ (20262449 / 40000000) := by
  have h := checkLog_sound (w := (164893617021 / 664893617021)) (n := 12)
    (lo := (63320153 / 125000000)) (hi := (20262449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414893617021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414893617021 / 250000000000) = 1/(250000000000 / 414893617021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8325 : Bounds (63320153 / 125000000) (20262449 / 40000000) (Real.log (414893617021 / 250000000000)) := by
  have h := reflection_log_8325_neg
  have he : Real.log (414893617021 / 250000000000) = -Real.log (250000000000 / 414893617021) := by
    rw [show ((414893617021 / 250000000000) : ℝ) = ((250000000000 / 414893617021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8326_neg : (5076269 / 10000000) ≤ -Real.log (100000000000 / 166134397871) ∧
    -Real.log (100000000000 / 166134397871) ≤ (507626901 / 1000000000) := by
  have h := checkLog_sound (w := (66134397871 / 266134397871)) (n := 12)
    (lo := (5076269 / 10000000)) (hi := (507626901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166134397871 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166134397871 / 100000000000) = 1/(100000000000 / 166134397871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8326 : Bounds (5076269 / 10000000) (507626901 / 1000000000) (Real.log (166134397871 / 100000000000)) := by
  have h := reflection_log_8326_neg
  have he : Real.log (166134397871 / 100000000000) = -Real.log (100000000000 / 166134397871) := by
    rw [show ((166134397871 / 100000000000) : ℝ) = ((100000000000 / 166134397871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8327_neg : (222343231 / 1000000000) ≤ -Real.log (1000 / 1249) ∧
    -Real.log (1000 / 1249) ≤ (3474113 / 15625000) := by
  have h := checkLog_sound (w := (249 / 2249)) (n := 12)
    (lo := (222343231 / 1000000000)) (hi := (3474113 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249 / 1000) = 1/(1000 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8327 : Bounds (222343231 / 1000000000) (3474113 / 15625000) (Real.log (1249 / 1000)) := by
  have h := reflection_log_8327_neg
  have he : Real.log (1249 / 1000) = -Real.log (1000 / 1249) := by
    rw [show ((1249 / 1000) : ℝ) = ((1000 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8328_neg : (286349627 / 1000000000) ≤ -Real.log (751 / 1000) ∧
    -Real.log (751 / 1000) ≤ (71587407 / 250000000) := by
  have h := checkLog_sound (w := (249 / 1751)) (n := 12)
    (lo := (286349627 / 1000000000)) (hi := (71587407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 751) = 1/(751 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8328 : Bounds (-71587407 / 250000000) (-286349627 / 1000000000) (Real.log (751 / 1000)) := by
  have h := reflection_log_8328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8329_neg : (248969 / 1000000000) ≤ -Real.log (1000000 / 1000249) ∧
    -Real.log (1000000 / 1000249) ≤ (24897 / 100000000) := by
  have h := checkLog_sound (w := (249 / 2000249)) (n := 12)
    (lo := (248969 / 1000000000)) (hi := (24897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000249 / 1000000) = 1/(1000000 / 1000249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8329 : Bounds (248969 / 1000000000) (24897 / 100000000) (Real.log (1000249 / 1000000)) := by
  have h := reflection_log_8329_neg
  have he : Real.log (1000249 / 1000000) = -Real.log (1000000 / 1000249) := by
    rw [show ((1000249 / 1000000) : ℝ) = ((1000000 / 1000249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8330_neg : (249031 / 1000000000) ≤ -Real.log (999751 / 1000000) ∧
    -Real.log (999751 / 1000000) ≤ (31129 / 125000000) := by
  have h := checkLog_sound (w := (249 / 1999751)) (n := 12)
    (lo := (249031 / 1000000000)) (hi := (31129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999751) = 1/(999751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8330 : Bounds (-31129 / 125000000) (-249031 / 1000000000) (Real.log (999751 / 1000000)) := by
  have h := reflection_log_8330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8331_neg : (59129683 / 500000000) ≤ -Real.log (31250 / 35173) ∧
    -Real.log (31250 / 35173) ≤ (118259367 / 1000000000) := by
  have h := checkLog_sound (w := (3923 / 66423)) (n := 12)
    (lo := (59129683 / 500000000)) (hi := (118259367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35173 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35173 / 31250) = 1/(31250 / 35173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8331 : Bounds (59129683 / 500000000) (118259367 / 1000000000) (Real.log (35173 / 31250)) := by
  have h := reflection_log_8331_neg
  have he : Real.log (35173 / 31250) = -Real.log (31250 / 35173) := by
    rw [show ((35173 / 31250) : ℝ) = ((31250 / 35173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8332_neg : (134144151 / 1000000000) ≤ -Real.log (27327 / 31250) ∧
    -Real.log (27327 / 31250) ≤ (16768019 / 125000000) := by
  have h := checkLog_sound (w := (3923 / 58577)) (n := 12)
    (lo := (134144151 / 1000000000)) (hi := (16768019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27327) = 1/(27327 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8332 : Bounds (-16768019 / 125000000) (-134144151 / 1000000000) (Real.log (27327 / 31250)) := by
  have h := reflection_log_8332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8333_neg : (118707941 / 1000000000) ≤ -Real.log (1000000 / 1126041) ∧
    -Real.log (1000000 / 1126041) ≤ (59353971 / 500000000) := by
  have h := checkLog_sound (w := (126041 / 2126041)) (n := 12)
    (lo := (118707941 / 1000000000)) (hi := (59353971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126041 / 1000000) = 1/(1000000 / 1126041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8333 : Bounds (118707941 / 1000000000) (59353971 / 500000000) (Real.log (1126041 / 1000000)) := by
  have h := reflection_log_8333_neg
  have he : Real.log (1126041 / 1000000) = -Real.log (1000000 / 1126041) := by
    rw [show ((1126041 / 1000000) : ℝ) = ((1000000 / 1126041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8334_neg : (26944363 / 200000000) ≤ -Real.log (873959 / 1000000) ∧
    -Real.log (873959 / 1000000) ≤ (16840227 / 125000000) := by
  have h := checkLog_sound (w := (126041 / 1873959)) (n := 12)
    (lo := (26944363 / 200000000)) (hi := (16840227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873959) = 1/(873959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8334 : Bounds (-16840227 / 125000000) (-26944363 / 200000000) (Real.log (873959 / 1000000)) := by
  have h := reflection_log_8334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8335_neg : (8006937 / 500000000) ≤ -Real.log (984113666319 / 1000000000000) ∧
    -Real.log (984113666319 / 1000000000000) ≤ (128111 / 8000000) := by
  have h := checkLog_sound (w := (15886333681 / 1984113666319)) (n := 12)
    (lo := (8006937 / 500000000)) (hi := (128111 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984113666319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984113666319) = 1/(984113666319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8335 : Bounds (-128111 / 8000000) (-8006937 / 500000000) (Real.log (984113666319 / 1000000000000)) := by
  have h := reflection_log_8335_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8336_neg : (3176957 / 200000000) ≤ -Real.log (961172571 / 976562500) ∧
    -Real.log (961172571 / 976562500) ≤ (7942393 / 500000000) := by
  have h := checkLog_sound (w := (15389929 / 1937735071)) (n := 12)
    (lo := (3176957 / 200000000)) (hi := (7942393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 961172571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 961172571) = 1/(961172571 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8336 : Bounds (-7942393 / 500000000) (-3176957 / 200000000) (Real.log (961172571 / 976562500)) := by
  have h := reflection_log_8336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8337_neg : (126201759 / 500000000) ≤ -Real.log (250000000000 / 321778826801) ∧
    -Real.log (250000000000 / 321778826801) ≤ (252403519 / 1000000000) := by
  have h := checkLog_sound (w := (71778826801 / 571778826801)) (n := 12)
    (lo := (126201759 / 500000000)) (hi := (252403519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321778826801 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321778826801 / 250000000000) = 1/(250000000000 / 321778826801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8337 : Bounds (126201759 / 500000000) (252403519 / 1000000000) (Real.log (321778826801 / 250000000000)) := by
  have h := reflection_log_8337_neg
  have he : Real.log (321778826801 / 250000000000) = -Real.log (250000000000 / 321778826801) := by
    rw [show ((321778826801 / 250000000000) : ℝ) = ((250000000000 / 321778826801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8338_neg : (63357439 / 250000000) ≤ -Real.log (500000000000 / 644218435877) ∧
    -Real.log (500000000000 / 644218435877) ≤ (253429757 / 1000000000) := by
  have h := checkLog_sound (w := (144218435877 / 1144218435877)) (n := 12)
    (lo := (63357439 / 250000000)) (hi := (253429757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644218435877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644218435877 / 500000000000) = 1/(500000000000 / 644218435877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8338 : Bounds (63357439 / 250000000) (253429757 / 1000000000) (Real.log (644218435877 / 500000000000)) := by
  have h := reflection_log_8338_neg
  have he : Real.log (644218435877 / 500000000000) = -Real.log (500000000000 / 644218435877) := by
    rw [show ((644218435877 / 500000000000) : ℝ) = ((500000000000 / 644218435877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8339_neg : (5076269 / 10000000) ≤ -Real.log (250000000000 / 415335994677) ∧
    -Real.log (250000000000 / 415335994677) ≤ (507626901 / 1000000000) := by
  have h := checkLog_sound (w := (165335994677 / 665335994677)) (n := 12)
    (lo := (5076269 / 10000000)) (hi := (507626901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415335994677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415335994677 / 250000000000) = 1/(250000000000 / 415335994677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8339 : Bounds (5076269 / 10000000) (507626901 / 1000000000) (Real.log (415335994677 / 250000000000)) := by
  have h := reflection_log_8339_neg
  have he : Real.log (415335994677 / 250000000000) = -Real.log (250000000000 / 415335994677) := by
    rw [show ((415335994677 / 250000000000) : ℝ) = ((250000000000 / 415335994677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8340_neg : (254346429 / 500000000) ≤ -Real.log (50000000000 / 83155792277) ∧
    -Real.log (50000000000 / 83155792277) ≤ (508692859 / 1000000000) := by
  have h := checkLog_sound (w := (33155792277 / 133155792277)) (n := 12)
    (lo := (254346429 / 500000000)) (hi := (508692859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83155792277 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83155792277 / 50000000000) = 1/(50000000000 / 83155792277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8340 : Bounds (254346429 / 500000000) (508692859 / 1000000000) (Real.log (83155792277 / 50000000000)) := by
  have h := reflection_log_8340_neg
  have he : Real.log (83155792277 / 50000000000) = -Real.log (50000000000 / 83155792277) := by
    rw [show ((83155792277 / 50000000000) : ℝ) = ((50000000000 / 83155792277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8341_neg : (222743471 / 1000000000) ≤ -Real.log (2000 / 2499) ∧
    -Real.log (2000 / 2499) ≤ (13921467 / 62500000) := by
  have h := checkLog_sound (w := (499 / 4499)) (n := 12)
    (lo := (222743471 / 1000000000)) (hi := (13921467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2000) = 1/(2000 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8341 : Bounds (222743471 / 1000000000) (13921467 / 62500000) (Real.log (2499 / 2000)) := by
  have h := reflection_log_8341_neg
  have he : Real.log (2499 / 2000) = -Real.log (2000 / 2499) := by
    rw [show ((2499 / 2000) : ℝ) = ((2000 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8342_neg : (287015627 / 1000000000) ≤ -Real.log (1501 / 2000) ∧
    -Real.log (1501 / 2000) ≤ (71753907 / 250000000) := by
  have h := checkLog_sound (w := (499 / 3501)) (n := 12)
    (lo := (287015627 / 1000000000)) (hi := (71753907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1501) = 1/(1501 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8342 : Bounds (-71753907 / 250000000) (-287015627 / 1000000000) (Real.log (1501 / 2000)) := by
  have h := reflection_log_8342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8343_neg : (62367 / 250000000) ≤ -Real.log (2000000 / 2000499) ∧
    -Real.log (2000000 / 2000499) ≤ (249469 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4000499)) (n := 12)
    (lo := (62367 / 250000000)) (hi := (249469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000499 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000499 / 2000000) = 1/(2000000 / 2000499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8343 : Bounds (62367 / 250000000) (249469 / 1000000000) (Real.log (2000499 / 2000000)) := by
  have h := reflection_log_8343_neg
  have he : Real.log (2000499 / 2000000) = -Real.log (2000000 / 2000499) := by
    rw [show ((2000499 / 2000000) : ℝ) = ((2000000 / 2000499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8344_neg : (249531 / 1000000000) ≤ -Real.log (1999501 / 2000000) ∧
    -Real.log (1999501 / 2000000) ≤ (62383 / 250000000) := by
  have h := checkLog_sound (w := (499 / 3999501)) (n := 12)
    (lo := (249531 / 1000000000)) (hi := (62383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999501) = 1/(1999501 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8344 : Bounds (-62383 / 250000000) (-249531 / 1000000000) (Real.log (1999501 / 2000000)) := by
  have h := reflection_log_8344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8345_neg : (29622141 / 250000000) ≤ -Real.log (500000 / 562897) ∧
    -Real.log (500000 / 562897) ≤ (23697713 / 200000000) := by
  have h := checkLog_sound (w := (62897 / 1062897)) (n := 12)
    (lo := (29622141 / 250000000)) (hi := (23697713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562897 / 500000) = 1/(500000 / 562897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8345 : Bounds (29622141 / 250000000) (23697713 / 200000000) (Real.log (562897 / 500000)) := by
  have h := reflection_log_8345_neg
  have he : Real.log (562897 / 500000) = -Real.log (500000 / 562897) := by
    rw [show ((562897 / 500000) : ℝ) = ((500000 / 562897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8346_neg : (134439233 / 1000000000) ≤ -Real.log (437103 / 500000) ∧
    -Real.log (437103 / 500000) ≤ (67219617 / 500000000) := by
  have h := checkLog_sound (w := (62897 / 937103)) (n := 12)
    (lo := (134439233 / 1000000000)) (hi := (67219617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437103) = 1/(437103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8346 : Bounds (-67219617 / 500000000) (-134439233 / 1000000000) (Real.log (437103 / 500000)) := by
  have h := reflection_log_8346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8347_neg : (29734481 / 250000000) ≤ -Real.log (10000 / 11263) ∧
    -Real.log (10000 / 11263) ≤ (4757517 / 40000000) := by
  have h := checkLog_sound (w := (1263 / 21263)) (n := 12)
    (lo := (29734481 / 250000000)) (hi := (4757517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11263 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11263 / 10000) = 1/(10000 / 11263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8347 : Bounds (29734481 / 250000000) (4757517 / 40000000) (Real.log (11263 / 10000)) := by
  have h := reflection_log_8347_neg
  have he : Real.log (11263 / 10000) = -Real.log (10000 / 11263) := by
    rw [show ((11263 / 10000) : ℝ) = ((10000 / 11263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8348_neg : (135018211 / 1000000000) ≤ -Real.log (8737 / 10000) ∧
    -Real.log (8737 / 10000) ≤ (33754553 / 250000000) := by
  have h := checkLog_sound (w := (1263 / 18737)) (n := 12)
    (lo := (135018211 / 1000000000)) (hi := (33754553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8737) = 1/(8737 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8348 : Bounds (-33754553 / 250000000) (-135018211 / 1000000000) (Real.log (8737 / 10000)) := by
  have h := reflection_log_8348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8349_neg : (16080287 / 1000000000) ≤ -Real.log (98404831 / 100000000) ∧
    -Real.log (98404831 / 100000000) ≤ (502509 / 31250000) := by
  have h := checkLog_sound (w := (1595169 / 198404831)) (n := 12)
    (lo := (16080287 / 1000000000)) (hi := (502509 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98404831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98404831) = 1/(98404831 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8349 : Bounds (-502509 / 31250000) (-16080287 / 1000000000) (Real.log (98404831 / 100000000)) := by
  have h := reflection_log_8349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8350_neg : (3987667 / 250000000) ≤ -Real.log (246043967391 / 250000000000) ∧
    -Real.log (246043967391 / 250000000000) ≤ (15950669 / 1000000000) := by
  have h := checkLog_sound (w := (3956032609 / 496043967391)) (n := 12)
    (lo := (3987667 / 250000000)) (hi := (15950669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246043967391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246043967391) = 1/(246043967391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8350 : Bounds (-15950669 / 1000000000) (-3987667 / 250000000) (Real.log (246043967391 / 250000000000)) := by
  have h := reflection_log_8350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8351_neg : (252927797 / 1000000000) ≤ -Real.log (100000000000 / 128779029199) ∧
    -Real.log (100000000000 / 128779029199) ≤ (126463899 / 500000000) := by
  have h := checkLog_sound (w := (28779029199 / 228779029199)) (n := 12)
    (lo := (252927797 / 1000000000)) (hi := (126463899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128779029199 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128779029199 / 100000000000) = 1/(100000000000 / 128779029199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8351 : Bounds (252927797 / 1000000000) (126463899 / 500000000) (Real.log (128779029199 / 100000000000)) := by
  have h := reflection_log_8351_neg
  have he : Real.log (128779029199 / 100000000000) = -Real.log (100000000000 / 128779029199) := by
    rw [show ((128779029199 / 100000000000) : ℝ) = ((100000000000 / 128779029199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8352_neg : (50791227 / 200000000) ≤ -Real.log (500000000000 / 644557628477) ∧
    -Real.log (500000000000 / 644557628477) ≤ (31744517 / 125000000) := by
  have h := checkLog_sound (w := (144557628477 / 1144557628477)) (n := 12)
    (lo := (50791227 / 200000000)) (hi := (31744517 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644557628477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644557628477 / 500000000000) = 1/(500000000000 / 644557628477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8352 : Bounds (50791227 / 200000000) (31744517 / 125000000) (Real.log (644557628477 / 500000000000)) := by
  have h := reflection_log_8352_neg
  have he : Real.log (644557628477 / 500000000000) = -Real.log (500000000000 / 644557628477) := by
    rw [show ((644557628477 / 500000000000) : ℝ) = ((500000000000 / 644557628477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8353_neg : (254346429 / 500000000) ≤ -Real.log (500000000000 / 831557922769) ∧
    -Real.log (500000000000 / 831557922769) ≤ (508692859 / 1000000000) := by
  have h := checkLog_sound (w := (331557922769 / 1331557922769)) (n := 12)
    (lo := (254346429 / 500000000)) (hi := (508692859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831557922769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831557922769 / 500000000000) = 1/(500000000000 / 831557922769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8353 : Bounds (254346429 / 500000000) (508692859 / 1000000000) (Real.log (831557922769 / 500000000000)) := by
  have h := reflection_log_8353_neg
  have he : Real.log (831557922769 / 500000000000) = -Real.log (500000000000 / 831557922769) := by
    rw [show ((831557922769 / 500000000000) : ℝ) = ((500000000000 / 831557922769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8354_neg : (509759099 / 1000000000) ≤ -Real.log (500000000000 / 832445036643) ∧
    -Real.log (500000000000 / 832445036643) ≤ (5097591 / 10000000) := by
  have h := checkLog_sound (w := (332445036643 / 1332445036643)) (n := 12)
    (lo := (509759099 / 1000000000)) (hi := (5097591 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832445036643 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832445036643 / 500000000000) = 1/(500000000000 / 832445036643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8354 : Bounds (509759099 / 1000000000) (5097591 / 10000000) (Real.log (832445036643 / 500000000000)) := by
  have h := reflection_log_8354_neg
  have he : Real.log (832445036643 / 500000000000) = -Real.log (500000000000 / 832445036643) := by
    rw [show ((832445036643 / 500000000000) : ℝ) = ((500000000000 / 832445036643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8355_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8355 : Bounds (223143551 / 1000000000) (1743309 / 7812500) (Real.log (5 / 4)) := by
  have h := reflection_log_8355_neg
  have he : Real.log (5 / 4) = -Real.log (4 / 5) := by
    rw [show ((5 / 4) : ℝ) = ((4 / 5) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8356_neg : (35960259 / 125000000) ≤ -Real.log (3 / 4) ∧
    -Real.log (3 / 4) ≤ (287682073 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4 / 3) = 1/(3 / 4) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8356 : Bounds (-287682073 / 1000000000) (-35960259 / 125000000) (Real.log (3 / 4)) := by
  have h := reflection_log_8356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8357_neg : (15623 / 62500000) ≤ -Real.log (4000 / 4001) ∧
    -Real.log (4000 / 4001) ≤ (249969 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 8001)) (n := 12)
    (lo := (15623 / 62500000)) (hi := (249969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 4000) = 1/(4000 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8357 : Bounds (15623 / 62500000) (249969 / 1000000000) (Real.log (4001 / 4000)) := by
  have h := reflection_log_8357_neg
  have he : Real.log (4001 / 4000) = -Real.log (4000 / 4001) := by
    rw [show ((4001 / 4000) : ℝ) = ((4000 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8358_neg : (250031 / 1000000000) ≤ -Real.log (3999 / 4000) ∧
    -Real.log (3999 / 4000) ≤ (15627 / 62500000) := by
  have h := checkLog_sound (w := (1 / 7999)) (n := 12)
    (lo := (250031 / 1000000000)) (hi := (15627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3999) = 1/(3999 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8358 : Bounds (-15627 / 62500000) (-250031 / 1000000000) (Real.log (3999 / 4000)) := by
  have h := reflection_log_8358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8359_neg : (118718597 / 1000000000) ≤ -Real.log (1000000 / 1126053) ∧
    -Real.log (1000000 / 1126053) ≤ (59359299 / 500000000) := by
  have h := checkLog_sound (w := (126053 / 2126053)) (n := 12)
    (lo := (118718597 / 1000000000)) (hi := (59359299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126053 / 1000000) = 1/(1000000 / 1126053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8359 : Bounds (118718597 / 1000000000) (59359299 / 500000000) (Real.log (1126053 / 1000000)) := by
  have h := reflection_log_8359_neg
  have he : Real.log (1126053 / 1000000) = -Real.log (1000000 / 1126053) := by
    rw [show ((1126053 / 1000000) : ℝ) = ((1000000 / 1126053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8360_neg : (26947109 / 200000000) ≤ -Real.log (873947 / 1000000) ∧
    -Real.log (873947 / 1000000) ≤ (67367773 / 500000000) := by
  have h := checkLog_sound (w := (126053 / 1873947)) (n := 12)
    (lo := (26947109 / 200000000)) (hi := (67367773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873947) = 1/(873947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8360 : Bounds (-67367773 / 500000000) (-26947109 / 200000000) (Real.log (873947 / 1000000)) := by
  have h := reflection_log_8360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8361_neg : (59583927 / 500000000) ≤ -Real.log (1000000 / 1126559) ∧
    -Real.log (1000000 / 1126559) ≤ (23833571 / 200000000) := by
  have h := checkLog_sound (w := (126559 / 2126559)) (n := 12)
    (lo := (59583927 / 500000000)) (hi := (23833571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126559 / 1000000) = 1/(1000000 / 1126559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8361 : Bounds (59583927 / 500000000) (23833571 / 200000000) (Real.log (1126559 / 1000000)) := by
  have h := reflection_log_8361_neg
  have he : Real.log (1126559 / 1000000) = -Real.log (1000000 / 1126559) := by
    rw [show ((1126559 / 1000000) : ℝ) = ((1000000 / 1126559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8362_neg : (16914337 / 125000000) ≤ -Real.log (873441 / 1000000) ∧
    -Real.log (873441 / 1000000) ≤ (135314697 / 1000000000) := by
  have h := checkLog_sound (w := (126559 / 1873441)) (n := 12)
    (lo := (16914337 / 125000000)) (hi := (135314697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873441) = 1/(873441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8362 : Bounds (-135314697 / 1000000000) (-16914337 / 125000000) (Real.log (873441 / 1000000)) := by
  have h := reflection_log_8362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8363_neg : (16146841 / 1000000000) ≤ -Real.log (983982819519 / 1000000000000) ∧
    -Real.log (983982819519 / 1000000000000) ≤ (8073421 / 500000000) := by
  have h := checkLog_sound (w := (16017180481 / 1983982819519)) (n := 12)
    (lo := (16146841 / 1000000000)) (hi := (8073421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983982819519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983982819519) = 1/(983982819519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8363 : Bounds (-8073421 / 500000000) (-16146841 / 1000000000) (Real.log (983982819519 / 1000000000000)) := by
  have h := reflection_log_8363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8364_neg : (4004237 / 250000000) ≤ -Real.log (984110641191 / 1000000000000) ∧
    -Real.log (984110641191 / 1000000000000) ≤ (16016949 / 1000000000) := by
  have h := checkLog_sound (w := (15889358809 / 1984110641191)) (n := 12)
    (lo := (4004237 / 250000000)) (hi := (16016949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984110641191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984110641191) = 1/(984110641191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8364 : Bounds (-16016949 / 1000000000) (-4004237 / 250000000) (Real.log (984110641191 / 1000000000000)) := by
  have h := reflection_log_8364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8365_neg : (253454143 / 1000000000) ≤ -Real.log (500000000000 / 644234146921) ∧
    -Real.log (500000000000 / 644234146921) ≤ (3960221 / 15625000) := by
  have h := checkLog_sound (w := (144234146921 / 1144234146921)) (n := 12)
    (lo := (253454143 / 1000000000)) (hi := (3960221 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644234146921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644234146921 / 500000000000) = 1/(500000000000 / 644234146921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8365 : Bounds (253454143 / 1000000000) (3960221 / 15625000) (Real.log (644234146921 / 500000000000)) := by
  have h := reflection_log_8365_neg
  have he : Real.log (644234146921 / 500000000000) = -Real.log (500000000000 / 644234146921) := by
    rw [show ((644234146921 / 500000000000) : ℝ) = ((500000000000 / 644234146921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8366_neg : (5089651 / 20000000) ≤ -Real.log (250000000000 / 322448511119) ∧
    -Real.log (250000000000 / 322448511119) ≤ (254482551 / 1000000000) := by
  have h := checkLog_sound (w := (72448511119 / 572448511119)) (n := 12)
    (lo := (5089651 / 20000000)) (hi := (254482551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322448511119 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322448511119 / 250000000000) = 1/(250000000000 / 322448511119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8366 : Bounds (5089651 / 20000000) (254482551 / 1000000000) (Real.log (322448511119 / 250000000000)) := by
  have h := reflection_log_8366_neg
  have he : Real.log (322448511119 / 250000000000) = -Real.log (250000000000 / 322448511119) := by
    rw [show ((322448511119 / 250000000000) : ℝ) = ((250000000000 / 322448511119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8367_neg : (509759099 / 1000000000) ≤ -Real.log (250000000000 / 416222518321) ∧
    -Real.log (250000000000 / 416222518321) ≤ (5097591 / 10000000) := by
  have h := checkLog_sound (w := (166222518321 / 666222518321)) (n := 12)
    (lo := (509759099 / 1000000000)) (hi := (5097591 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416222518321 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416222518321 / 250000000000) = 1/(250000000000 / 416222518321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8367 : Bounds (509759099 / 1000000000) (5097591 / 10000000) (Real.log (416222518321 / 250000000000)) := by
  have h := reflection_log_8367_neg
  have he : Real.log (416222518321 / 250000000000) = -Real.log (250000000000 / 416222518321) := by
    rw [show ((416222518321 / 250000000000) : ℝ) = ((250000000000 / 416222518321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8368_neg : (510825623 / 1000000000) ≤ -Real.log (250000000000 / 416666666667) ∧
    -Real.log (250000000000 / 416666666667) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (166666666667 / 666666666667)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416666666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416666666667 / 250000000000) = 1/(250000000000 / 416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8368 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (416666666667 / 250000000000)) := by
  have h := reflection_log_8368_neg
  have he : Real.log (416666666667 / 250000000000) = -Real.log (250000000000 / 416666666667) := by
    rw [show ((416666666667 / 250000000000) : ℝ) = ((250000000000 / 416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8369_neg : (223543471 / 1000000000) ≤ -Real.log (2000 / 2501) ∧
    -Real.log (2000 / 2501) ≤ (13971467 / 62500000) := by
  have h := checkLog_sound (w := (501 / 4501)) (n := 12)
    (lo := (223543471 / 1000000000)) (hi := (13971467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2501 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2501 / 2000) = 1/(2000 / 2501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8369 : Bounds (223543471 / 1000000000) (13971467 / 62500000) (Real.log (2501 / 2000)) := by
  have h := reflection_log_8369_neg
  have he : Real.log (2501 / 2000) = -Real.log (2000 / 2501) := by
    rw [show ((2501 / 2000) : ℝ) = ((2000 / 2501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8370_neg : (288348961 / 1000000000) ≤ -Real.log (1499 / 2000) ∧
    -Real.log (1499 / 2000) ≤ (144174481 / 500000000) := by
  have h := checkLog_sound (w := (501 / 3499)) (n := 12)
    (lo := (288348961 / 1000000000)) (hi := (144174481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1499) = 1/(1499 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8370 : Bounds (-144174481 / 500000000) (-288348961 / 1000000000) (Real.log (1499 / 2000)) := by
  have h := reflection_log_8370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8371_neg : (62617 / 250000000) ≤ -Real.log (2000000 / 2000501) ∧
    -Real.log (2000000 / 2000501) ≤ (250469 / 1000000000) := by
  have h := checkLog_sound (w := (501 / 4000501)) (n := 12)
    (lo := (62617 / 250000000)) (hi := (250469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000501 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000501 / 2000000) = 1/(2000000 / 2000501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8371 : Bounds (62617 / 250000000) (250469 / 1000000000) (Real.log (2000501 / 2000000)) := by
  have h := reflection_log_8371_neg
  have he : Real.log (2000501 / 2000000) = -Real.log (2000000 / 2000501) := by
    rw [show ((2000501 / 2000000) : ℝ) = ((2000000 / 2000501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8372_neg : (250531 / 1000000000) ≤ -Real.log (1999499 / 2000000) ∧
    -Real.log (1999499 / 2000000) ≤ (62633 / 250000000) := by
  have h := checkLog_sound (w := (501 / 3999499)) (n := 12)
    (lo := (250531 / 1000000000)) (hi := (62633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999499) = 1/(1999499 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8372 : Bounds (-62633 / 250000000) (-250531 / 1000000000) (Real.log (1999499 / 2000000)) := by
  have h := reflection_log_8372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8373_neg : (11894769 / 100000000) ≤ -Real.log (1000000 / 1126311) ∧
    -Real.log (1000000 / 1126311) ≤ (118947691 / 1000000000) := by
  have h := checkLog_sound (w := (126311 / 2126311)) (n := 12)
    (lo := (11894769 / 100000000)) (hi := (118947691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126311 / 1000000) = 1/(1000000 / 1126311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8373 : Bounds (11894769 / 100000000) (118947691 / 1000000000) (Real.log (1126311 / 1000000)) := by
  have h := reflection_log_8373_neg
  have he : Real.log (1126311 / 1000000) = -Real.log (1000000 / 1126311) := by
    rw [show ((1126311 / 1000000) : ℝ) = ((1000000 / 1126311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8374_neg : (135030801 / 1000000000) ≤ -Real.log (873689 / 1000000) ∧
    -Real.log (873689 / 1000000) ≤ (67515401 / 500000000) := by
  have h := checkLog_sound (w := (126311 / 1873689)) (n := 12)
    (lo := (135030801 / 1000000000)) (hi := (67515401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873689) = 1/(873689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8374 : Bounds (-67515401 / 500000000) (-135030801 / 1000000000) (Real.log (873689 / 1000000)) := by
  have h := reflection_log_8374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8375_neg : (119397731 / 1000000000) ≤ -Real.log (500000 / 563409) ∧
    -Real.log (500000 / 563409) ≤ (29849433 / 250000000) := by
  have h := checkLog_sound (w := (63409 / 1063409)) (n := 12)
    (lo := (119397731 / 1000000000)) (hi := (29849433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563409 / 500000) = 1/(500000 / 563409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8375 : Bounds (119397731 / 1000000000) (29849433 / 250000000) (Real.log (563409 / 500000)) := by
  have h := reflection_log_8375_neg
  have he : Real.log (563409 / 500000) = -Real.log (500000 / 563409) := by
    rw [show ((563409 / 500000) : ℝ) = ((500000 / 563409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8376_neg : (33902817 / 250000000) ≤ -Real.log (436591 / 500000) ∧
    -Real.log (436591 / 500000) ≤ (135611269 / 1000000000) := by
  have h := checkLog_sound (w := (63409 / 936591)) (n := 12)
    (lo := (33902817 / 250000000)) (hi := (135611269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436591) = 1/(436591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8376 : Bounds (-135611269 / 1000000000) (-33902817 / 250000000) (Real.log (436591 / 500000)) := by
  have h := reflection_log_8376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8377_neg : (16213537 / 1000000000) ≤ -Real.log (245979298719 / 250000000000) ∧
    -Real.log (245979298719 / 250000000000) ≤ (8106769 / 500000000) := by
  have h := checkLog_sound (w := (4020701281 / 495979298719)) (n := 12)
    (lo := (16213537 / 1000000000)) (hi := (8106769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245979298719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245979298719) = 1/(245979298719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8377 : Bounds (-8106769 / 500000000) (-16213537 / 1000000000) (Real.log (245979298719 / 250000000000)) := by
  have h := reflection_log_8377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8378_neg : (16083111 / 1000000000) ≤ -Real.log (984045531279 / 1000000000000) ∧
    -Real.log (984045531279 / 1000000000000) ≤ (2010389 / 125000000) := by
  have h := checkLog_sound (w := (15954468721 / 1984045531279)) (n := 12)
    (lo := (16083111 / 1000000000)) (hi := (2010389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984045531279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984045531279) = 1/(984045531279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8378 : Bounds (-2010389 / 125000000) (-16083111 / 1000000000) (Real.log (984045531279 / 1000000000000)) := by
  have h := reflection_log_8378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8379_neg : (63494623 / 250000000) ≤ -Real.log (500000000000 / 644572038791) ∧
    -Real.log (500000000000 / 644572038791) ≤ (253978493 / 1000000000) := by
  have h := checkLog_sound (w := (144572038791 / 1144572038791)) (n := 12)
    (lo := (63494623 / 250000000)) (hi := (253978493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644572038791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644572038791 / 500000000000) = 1/(500000000000 / 644572038791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8379 : Bounds (63494623 / 250000000) (253978493 / 1000000000) (Real.log (644572038791 / 500000000000)) := by
  have h := reflection_log_8379_neg
  have he : Real.log (644572038791 / 500000000000) = -Real.log (500000000000 / 644572038791) := by
    rw [show ((644572038791 / 500000000000) : ℝ) = ((500000000000 / 644572038791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8380_neg : (255008999 / 1000000000) ≤ -Real.log (250000000000 / 322618308669) ∧
    -Real.log (250000000000 / 322618308669) ≤ (255009 / 1000000) := by
  have h := checkLog_sound (w := (72618308669 / 572618308669)) (n := 12)
    (lo := (255008999 / 1000000000)) (hi := (255009 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322618308669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322618308669 / 250000000000) = 1/(250000000000 / 322618308669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8380 : Bounds (255008999 / 1000000000) (255009 / 1000000) (Real.log (322618308669 / 250000000000)) := by
  have h := reflection_log_8380_neg
  have he : Real.log (322618308669 / 250000000000) = -Real.log (250000000000 / 322618308669) := by
    rw [show ((322618308669 / 250000000000) : ℝ) = ((250000000000 / 322618308669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8381_neg : (510825623 / 1000000000) ≤ -Real.log (500000000000 / 833333333333) ∧
    -Real.log (500000000000 / 833333333333) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (333333333333 / 1333333333333)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833333333333 / 500000000000) = 1/(500000000000 / 833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8381 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (833333333333 / 500000000000)) := by
  have h := reflection_log_8381_neg
  have he : Real.log (833333333333 / 500000000000) = -Real.log (500000000000 / 833333333333) := by
    rw [show ((833333333333 / 500000000000) : ℝ) = ((500000000000 / 833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8382_neg : (31993277 / 62500000) ≤ -Real.log (500000000000 / 834222815211) ∧
    -Real.log (500000000000 / 834222815211) ≤ (511892433 / 1000000000) := by
  have h := checkLog_sound (w := (334222815211 / 1334222815211)) (n := 12)
    (lo := (31993277 / 62500000)) (hi := (511892433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834222815211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834222815211 / 500000000000) = 1/(500000000000 / 834222815211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8382 : Bounds (31993277 / 62500000) (511892433 / 1000000000) (Real.log (834222815211 / 500000000000)) := by
  have h := reflection_log_8382_neg
  have he : Real.log (834222815211 / 500000000000) = -Real.log (500000000000 / 834222815211) := by
    rw [show ((834222815211 / 500000000000) : ℝ) = ((500000000000 / 834222815211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8383_neg : (223943231 / 1000000000) ≤ -Real.log (1000 / 1251) ∧
    -Real.log (1000 / 1251) ≤ (3499113 / 15625000) := by
  have h := checkLog_sound (w := (251 / 2251)) (n := 12)
    (lo := (223943231 / 1000000000)) (hi := (3499113 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1000) = 1/(1000 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8383 : Bounds (223943231 / 1000000000) (3499113 / 15625000) (Real.log (1251 / 1000)) := by
  have h := reflection_log_8383_neg
  have he : Real.log (1251 / 1000) = -Real.log (1000 / 1251) := by
    rw [show ((1251 / 1000) : ℝ) = ((1000 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
