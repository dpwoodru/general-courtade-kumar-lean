import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15296_neg : (216869641 / 40000000) ≤ -Real.log (500000000000 / 113136363636363) ∧
    -Real.log (500000000000 / 113136363636363) ≤ (5421741033 / 1000000000) := by
  have h := checkLog_sound (w := (49136363636363 / 177136363636363)) (n := 12)
    (lo := (113942153 / 200000000)) (hi := (284855383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113136363636363 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(113136363636363 / 64000000000000) = 1/(500000000000 / 113136363636363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15296 : Bounds (216869641 / 40000000) (5421741033 / 1000000000) (Real.log (113136363636363 / 500000000000)) := by
  have h := reflection_log_15296_neg
  have he : Real.log (113136363636363 / 500000000000) = -Real.log (500000000000 / 113136363636363) := by
    rw [show ((113136363636363 / 500000000000) : ℝ) = ((500000000000 / 113136363636363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15297_neg : (272241549 / 50000000) ≤ -Real.log (250000000000 / 57889534883721) ∧
    -Real.log (250000000000 / 57889534883721) ≤ (1361207747 / 250000000) := by
  have h := checkLog_sound (w := (25889534883721 / 89889534883721)) (n := 12)
    (lo := (7410009 / 12500000)) (hi := (592800721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57889534883721 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(57889534883721 / 32000000000000) = 1/(250000000000 / 57889534883721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15297 : Bounds (272241549 / 50000000) (1361207747 / 250000000) (Real.log (57889534883721 / 250000000000)) := by
  have h := reflection_log_15297_neg
  have he : Real.log (57889534883721 / 250000000000) = -Real.log (250000000000 / 57889534883721) := by
    rw [show ((57889534883721 / 250000000000) : ℝ) = ((250000000000 / 57889534883721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15298_neg : (137787667 / 200000000) ≤ -Real.log (2500 / 4979) ∧
    -Real.log (2500 / 4979) ≤ (21529323 / 31250000) := by
  have h := checkLog_sound (w := (2479 / 7479)) (n := 12)
    (lo := (137787667 / 200000000)) (hi := (21529323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4979 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4979 / 2500) = 1/(2500 / 4979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15298 : Bounds (137787667 / 200000000) (21529323 / 31250000) (Real.log (4979 / 2500)) := by
  have h := reflection_log_15298_neg
  have he : Real.log (4979 / 2500) = -Real.log (2500 / 4979) := by
    rw [show ((4979 / 2500) : ℝ) = ((2500 / 4979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15299_neg : (4779523569 / 1000000000) ≤ -Real.log (21 / 2500) ∧
    -Real.log (21 / 2500) ≤ (597440447 / 125000000) := by
  have h := checkLog_sound (w := (289 / 961)) (n := 12)
    (lo := (620640489 / 1000000000)) (hi := (62064049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 336) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 336) = 1/(21 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15299 : Bounds (-597440447 / 125000000) (-4779523569 / 1000000000) (Real.log (21 / 2500)) := by
  have h := reflection_log_15299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15300_neg : (247777 / 250000000) ≤ -Real.log (2500000 / 2502479) ∧
    -Real.log (2500000 / 2502479) ≤ (991109 / 1000000000) := by
  have h := checkLog_sound (w := (2479 / 5002479)) (n := 12)
    (lo := (247777 / 250000000)) (hi := (991109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502479 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502479 / 2500000) = 1/(2500000 / 2502479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15300 : Bounds (247777 / 250000000) (991109 / 1000000000) (Real.log (2502479 / 2500000)) := by
  have h := reflection_log_15300_neg
  have he : Real.log (2502479 / 2500000) = -Real.log (2500000 / 2502479) := by
    rw [show ((2502479 / 2500000) : ℝ) = ((2500000 / 2502479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15301_neg : (992091 / 1000000000) ≤ -Real.log (2497521 / 2500000) ∧
    -Real.log (2497521 / 2500000) ≤ (248023 / 250000000) := by
  have h := checkLog_sound (w := (2479 / 4997521)) (n := 12)
    (lo := (992091 / 1000000000)) (hi := (248023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497521) = 1/(2497521 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15301 : Bounds (-248023 / 250000000) (-992091 / 1000000000) (Real.log (2497521 / 2500000)) := by
  have h := reflection_log_15301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15302_neg : (124243381 / 250000000) ≤ -Real.log (1000000 / 1643739) ∧
    -Real.log (1000000 / 1643739) ≤ (19878941 / 40000000) := by
  have h := checkLog_sound (w := (643739 / 2643739)) (n := 12)
    (lo := (124243381 / 250000000)) (hi := (19878941 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1643739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1643739 / 1000000) = 1/(1000000 / 1643739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15302 : Bounds (124243381 / 250000000) (19878941 / 40000000) (Real.log (1643739 / 1000000)) := by
  have h := reflection_log_15302_neg
  have he : Real.log (1643739 / 1000000) = -Real.log (1000000 / 1643739) := by
    rw [show ((1643739 / 1000000) : ℝ) = ((1000000 / 1643739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15303_neg : (103209167 / 100000000) ≤ -Real.log (356261 / 1000000) ∧
    -Real.log (356261 / 1000000) ≤ (129011459 / 125000000) := by
  have h := checkLog_sound (w := (143739 / 856261)) (n := 12)
    (lo := (33894449 / 100000000)) (hi := (338944491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 356261) = 1/(356261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15303 : Bounds (-129011459 / 125000000) (-103209167 / 100000000) (Real.log (356261 / 1000000)) := by
  have h := reflection_log_15303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15304_neg : (124384787 / 250000000) ≤ -Real.log (1000000 / 1644669) ∧
    -Real.log (1000000 / 1644669) ≤ (497539149 / 1000000000) := by
  have h := checkLog_sound (w := (644669 / 2644669)) (n := 12)
    (lo := (124384787 / 250000000)) (hi := (497539149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644669 / 1000000) = 1/(1000000 / 1644669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15304 : Bounds (124384787 / 250000000) (497539149 / 1000000000) (Real.log (1644669 / 1000000)) := by
  have h := reflection_log_15304_neg
  have he : Real.log (1644669 / 1000000) = -Real.log (1000000 / 1644669) := by
    rw [show ((1644669 / 1000000) : ℝ) = ((1000000 / 1644669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15305_neg : (129338191 / 125000000) ≤ -Real.log (355331 / 1000000) ∧
    -Real.log (355331 / 1000000) ≤ (103470553 / 100000000) := by
  have h := checkLog_sound (w := (144669 / 855331)) (n := 12)
    (lo := (85389587 / 250000000)) (hi := (341558349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355331) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355331) = 1/(355331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15305 : Bounds (-103470553 / 100000000) (-129338191 / 125000000) (Real.log (355331 / 1000000)) := by
  have h := reflection_log_15305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15306_neg : (537166381 / 1000000000) ≤ -Real.log (584401880439 / 1000000000000) ∧
    -Real.log (584401880439 / 1000000000000) ≤ (268583191 / 500000000) := by
  have h := checkLog_sound (w := (415598119561 / 1584401880439)) (n := 12)
    (lo := (537166381 / 1000000000)) (hi := (268583191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 584401880439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 584401880439) = 1/(584401880439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15306 : Bounds (-268583191 / 500000000) (-537166381 / 1000000000) (Real.log (584401880439 / 1000000000000)) := by
  have h := reflection_log_15306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15307_neg : (107023629 / 200000000) ≤ -Real.log (585600099879 / 1000000000000) ∧
    -Real.log (585600099879 / 1000000000000) ≤ (267559073 / 500000000) := by
  have h := checkLog_sound (w := (414399900121 / 1585600099879)) (n := 12)
    (lo := (107023629 / 200000000)) (hi := (267559073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 585600099879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 585600099879) = 1/(585600099879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15307 : Bounds (-267559073 / 500000000) (-107023629 / 200000000) (Real.log (585600099879 / 1000000000000)) := by
  have h := reflection_log_15307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15308_neg : (764532597 / 500000000) ≤ -Real.log (500000000000 / 2306930873713) ∧
    -Real.log (500000000000 / 2306930873713) ≤ (1529065197 / 1000000000) := by
  have h := checkLog_sound (w := (306930873713 / 4306930873713)) (n := 12)
    (lo := (71385417 / 500000000)) (hi := (28554167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2306930873713 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2306930873713 / 2000000000000) = 1/(500000000000 / 2306930873713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15308 : Bounds (764532597 / 500000000) (1529065197 / 1000000000) (Real.log (2306930873713 / 500000000000)) := by
  have h := reflection_log_15308_neg
  have he : Real.log (2306930873713 / 500000000000) = -Real.log (500000000000 / 2306930873713) := by
    rw [show ((2306930873713 / 500000000000) : ℝ) = ((500000000000 / 2306930873713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15309_neg : (383061169 / 250000000) ≤ -Real.log (250000000000 / 1157138696033) ∧
    -Real.log (250000000000 / 1157138696033) ≤ (1532244679 / 1000000000) := by
  have h := checkLog_sound (w := (157138696033 / 2157138696033)) (n := 12)
    (lo := (36487579 / 250000000)) (hi := (145950317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157138696033 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1157138696033 / 1000000000000) = 1/(250000000000 / 1157138696033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15309 : Bounds (383061169 / 250000000) (1532244679 / 1000000000) (Real.log (1157138696033 / 250000000000)) := by
  have h := reflection_log_15309_neg
  have he : Real.log (1157138696033 / 250000000000) = -Real.log (250000000000 / 1157138696033) := by
    rw [show ((1157138696033 / 250000000000) : ℝ) = ((250000000000 / 1157138696033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15310_neg : (272241549 / 50000000) ≤ -Real.log (500000000000 / 115779069767441) ∧
    -Real.log (500000000000 / 115779069767441) ≤ (1361207747 / 250000000) := by
  have h := checkLog_sound (w := (51779069767441 / 179779069767441)) (n := 12)
    (lo := (7410009 / 12500000)) (hi := (592800721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115779069767441 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(115779069767441 / 64000000000000) = 1/(500000000000 / 115779069767441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15310 : Bounds (272241549 / 50000000) (1361207747 / 250000000) (Real.log (115779069767441 / 500000000000)) := by
  have h := reflection_log_15310_neg
  have he : Real.log (115779069767441 / 500000000000) = -Real.log (500000000000 / 115779069767441) := by
    rw [show ((115779069767441 / 500000000000) : ℝ) = ((500000000000 / 115779069767441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15311_neg : (341778869 / 62500000) ≤ -Real.log (25000000000 / 5927380952381) ∧
    -Real.log (25000000000 / 5927380952381) ≤ (683557739 / 125000000) := by
  have h := checkLog_sound (w := (2727380952381 / 9127380952381)) (n := 12)
    (lo := (154107911 / 250000000)) (hi := (123286329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5927380952381 / 3200000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5927380952381 / 3200000000000) = 1/(25000000000 / 5927380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15311 : Bounds (341778869 / 62500000) (683557739 / 125000000) (Real.log (5927380952381 / 25000000000)) := by
  have h := reflection_log_15311_neg
  have he : Real.log (5927380952381 / 25000000000) = -Real.log (25000000000 / 5927380952381) := by
    rw [show ((5927380952381 / 25000000000) : ℝ) = ((25000000000 / 5927380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15312_neg : (21532461 / 31250000) ≤ -Real.log (5000 / 9959) ∧
    -Real.log (5000 / 9959) ≤ (689038753 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 14959)) (n := 12)
    (lo := (21532461 / 31250000)) (hi := (689038753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5000) = 1/(5000 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15312 : Bounds (21532461 / 31250000) (689038753 / 1000000000) (Real.log (9959 / 5000)) := by
  have h := reflection_log_15312_neg
  have he : Real.log (9959 / 5000) = -Real.log (5000 / 9959) := by
    rw [show ((9959 / 5000) : ℝ) = ((5000 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15313_neg : (4803621121 / 1000000000) ≤ -Real.log (41 / 5000) ∧
    -Real.log (41 / 5000) ≤ (600452641 / 125000000) := by
  have h := checkLog_sound (w := (297 / 953)) (n := 12)
    (lo := (644738041 / 1000000000)) (hi := (322369021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 328) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 328) = 1/(41 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15313 : Bounds (-600452641 / 125000000) (-4803621121 / 1000000000) (Real.log (41 / 5000)) := by
  have h := reflection_log_15313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15314_neg : (247827 / 250000000) ≤ -Real.log (5000000 / 5004959) ∧
    -Real.log (5000000 / 5004959) ≤ (991309 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 10004959)) (n := 12)
    (lo := (247827 / 250000000)) (hi := (991309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004959 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004959 / 5000000) = 1/(5000000 / 5004959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15314 : Bounds (247827 / 250000000) (991309 / 1000000000) (Real.log (5004959 / 5000000)) := by
  have h := reflection_log_15314_neg
  have he : Real.log (5004959 / 5000000) = -Real.log (5000000 / 5004959) := by
    rw [show ((5004959 / 5000000) : ℝ) = ((5000000 / 5004959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15315_neg : (248073 / 250000000) ≤ -Real.log (4995041 / 5000000) ∧
    -Real.log (4995041 / 5000000) ≤ (992293 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 9995041)) (n := 12)
    (lo := (248073 / 250000000)) (hi := (992293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995041) = 1/(4995041 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15315 : Bounds (-992293 / 1000000000) (-248073 / 250000000) (Real.log (4995041 / 5000000)) := by
  have h := reflection_log_15315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15316_neg : (497156627 / 1000000000) ≤ -Real.log (25000 / 41101) ∧
    -Real.log (25000 / 41101) ≤ (124289157 / 250000000) := by
  have h := checkLog_sound (w := (16101 / 66101)) (n := 12)
    (lo := (497156627 / 1000000000)) (hi := (124289157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41101 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41101 / 25000) = 1/(25000 / 41101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15316 : Bounds (497156627 / 1000000000) (124289157 / 250000000) (Real.log (41101 / 25000)) := by
  have h := reflection_log_15316_neg
  have he : Real.log (41101 / 25000) = -Real.log (25000 / 41101) := by
    rw [show ((41101 / 25000) : ℝ) = ((25000 / 41101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15317_neg : (1032936913 / 1000000000) ≤ -Real.log (8899 / 25000) ∧
    -Real.log (8899 / 25000) ≤ (206587383 / 200000000) := by
  have h := checkLog_sound (w := (3601 / 21399)) (n := 12)
    (lo := (339789733 / 1000000000)) (hi := (169894867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8899) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 8899) = 1/(8899 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15317 : Bounds (-206587383 / 200000000) (-1032936913 / 1000000000) (Real.log (8899 / 25000)) := by
  have h := reflection_log_15317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15318_neg : (248861377 / 500000000) ≤ -Real.log (1000000 / 1644971) ∧
    -Real.log (1000000 / 1644971) ≤ (99544551 / 200000000) := by
  have h := checkLog_sound (w := (644971 / 2644971)) (n := 12)
    (lo := (248861377 / 500000000)) (hi := (99544551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644971 / 1000000) = 1/(1000000 / 1644971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15318 : Bounds (248861377 / 500000000) (99544551 / 200000000) (Real.log (1644971 / 1000000)) := by
  have h := reflection_log_15318_neg
  have he : Real.log (1644971 / 1000000) = -Real.log (1000000 / 1644971) := by
    rw [show ((1644971 / 1000000) : ℝ) = ((1000000 / 1644971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15319_neg : (517777901 / 500000000) ≤ -Real.log (355029 / 1000000) ∧
    -Real.log (355029 / 1000000) ≤ (258888951 / 250000000) := by
  have h := checkLog_sound (w := (144971 / 855029)) (n := 12)
    (lo := (171204311 / 500000000)) (hi := (342408623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355029) = 1/(355029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15319 : Bounds (-258888951 / 250000000) (-517777901 / 500000000) (Real.log (355029 / 1000000)) := by
  have h := reflection_log_15319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15320_neg : (537833047 / 1000000000) ≤ -Real.log (584012409159 / 1000000000000) ∧
    -Real.log (584012409159 / 1000000000000) ≤ (67229131 / 125000000) := by
  have h := checkLog_sound (w := (415987590841 / 1584012409159)) (n := 12)
    (lo := (537833047 / 1000000000)) (hi := (67229131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 584012409159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 584012409159) = 1/(584012409159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15320 : Bounds (-67229131 / 125000000) (-537833047 / 1000000000) (Real.log (584012409159 / 1000000000000)) := by
  have h := reflection_log_15320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15321_neg : (267890143 / 500000000) ≤ -Real.log (365757799 / 625000000) ∧
    -Real.log (365757799 / 625000000) ≤ (535780287 / 1000000000) := by
  have h := checkLog_sound (w := (259242201 / 990757799)) (n := 12)
    (lo := (267890143 / 500000000)) (hi := (535780287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 365757799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 365757799) = 1/(365757799 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15321 : Bounds (-535780287 / 1000000000) (-267890143 / 500000000) (Real.log (365757799 / 625000000)) := by
  have h := reflection_log_15321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15322_neg : (76504677 / 50000000) ≤ -Real.log (250000000000 / 1154652208113) ∧
    -Real.log (250000000000 / 1154652208113) ≤ (1530093543 / 1000000000) := by
  have h := checkLog_sound (w := (154652208113 / 2154652208113)) (n := 12)
    (lo := (7189959 / 50000000)) (hi := (143799181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154652208113 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1154652208113 / 1000000000000) = 1/(250000000000 / 1154652208113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15322 : Bounds (76504677 / 50000000) (1530093543 / 1000000000) (Real.log (1154652208113 / 250000000000)) := by
  have h := reflection_log_15322_neg
  have he : Real.log (1154652208113 / 250000000000) = -Real.log (250000000000 / 1154652208113) := by
    rw [show ((1154652208113 / 250000000000) : ℝ) = ((250000000000 / 1154652208113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15323_neg : (383319639 / 250000000) ≤ -Real.log (20000000000 / 92666852567) ∧
    -Real.log (20000000000 / 92666852567) ≤ (1533278559 / 1000000000) := by
  have h := checkLog_sound (w := (12666852567 / 172666852567)) (n := 12)
    (lo := (36746049 / 250000000)) (hi := (146984197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92666852567 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(92666852567 / 80000000000) = 1/(20000000000 / 92666852567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15323 : Bounds (383319639 / 250000000) (1533278559 / 1000000000) (Real.log (92666852567 / 20000000000)) := by
  have h := reflection_log_15323_neg
  have he : Real.log (92666852567 / 20000000000) = -Real.log (20000000000 / 92666852567) := by
    rw [show ((92666852567 / 20000000000) : ℝ) = ((20000000000 / 92666852567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15324_neg : (341778869 / 62500000) ≤ -Real.log (500000000000 / 118547619047619) ∧
    -Real.log (500000000000 / 118547619047619) ≤ (683557739 / 125000000) := by
  have h := checkLog_sound (w := (54547619047619 / 182547619047619)) (n := 12)
    (lo := (154107911 / 250000000)) (hi := (123286329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118547619047619 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(118547619047619 / 64000000000000) = 1/(500000000000 / 118547619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15324 : Bounds (341778869 / 62500000) (683557739 / 125000000) (Real.log (118547619047619 / 500000000000)) := by
  have h := reflection_log_15324_neg
  have he : Real.log (118547619047619 / 500000000000) = -Real.log (500000000000 / 118547619047619) := by
    rw [show ((118547619047619 / 500000000000) : ℝ) = ((500000000000 / 118547619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15325_neg : (5492659873 / 1000000000) ≤ -Real.log (125000000000 / 30362804878049) ∧
    -Real.log (125000000000 / 30362804878049) ≤ (5492659881 / 1000000000) := by
  have h := checkLog_sound (w := (14362804878049 / 46362804878049)) (n := 12)
    (lo := (640629613 / 1000000000)) (hi := (320314807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30362804878049 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(30362804878049 / 16000000000000) = 1/(125000000000 / 30362804878049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15325 : Bounds (5492659873 / 1000000000) (5492659881 / 1000000000) (Real.log (30362804878049 / 125000000000)) := by
  have h := reflection_log_15325_neg
  have he : Real.log (30362804878049 / 125000000000) = -Real.log (125000000000 / 30362804878049) := by
    rw [show ((30362804878049 / 125000000000) : ℝ) = ((125000000000 / 30362804878049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15326_neg : (689139159 / 1000000000) ≤ -Real.log (125 / 249) ∧
    -Real.log (125 / 249) ≤ (17228479 / 25000000) := by
  have h := checkLog_sound (w := (62 / 187)) (n := 12)
    (lo := (689139159 / 1000000000)) (hi := (17228479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 125) = 1/(125 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15326 : Bounds (689139159 / 1000000000) (17228479 / 25000000) (Real.log (249 / 125)) := by
  have h := reflection_log_15326_neg
  have he : Real.log (249 / 125) = -Real.log (125 / 249) := by
    rw [show ((249 / 125) : ℝ) = ((125 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15327_neg : (4828313733 / 1000000000) ≤ -Real.log (1 / 125) ∧
    -Real.log (1 / 125) ≤ (241415687 / 50000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 64) = 1/(1 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15327 : Bounds (-241415687 / 50000000) (-4828313733 / 1000000000) (Real.log (1 / 125)) := by
  have h := reflection_log_15327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15328_neg : (247877 / 250000000) ≤ -Real.log (31250 / 31281) ∧
    -Real.log (31250 / 31281) ≤ (991509 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 62531)) (n := 12)
    (lo := (247877 / 250000000)) (hi := (991509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31281 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31281 / 31250) = 1/(31250 / 31281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15328 : Bounds (247877 / 250000000) (991509 / 1000000000) (Real.log (31281 / 31250)) := by
  have h := reflection_log_15328_neg
  have he : Real.log (31281 / 31250) = -Real.log (31250 / 31281) := by
    rw [show ((31281 / 31250) : ℝ) = ((31250 / 31281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15329_neg : (248123 / 250000000) ≤ -Real.log (31219 / 31250) ∧
    -Real.log (31219 / 31250) ≤ (992493 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 62469)) (n := 12)
    (lo := (248123 / 250000000)) (hi := (992493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31219) = 1/(31219 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15329 : Bounds (-992493 / 1000000000) (-248123 / 250000000) (Real.log (31219 / 31250)) := by
  have h := reflection_log_15329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15330_neg : (31083769 / 62500000) ≤ -Real.log (500000 / 822171) ∧
    -Real.log (500000 / 822171) ≤ (99468061 / 200000000) := by
  have h := checkLog_sound (w := (322171 / 1322171)) (n := 12)
    (lo := (31083769 / 62500000)) (hi := (99468061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822171 / 500000) = 1/(500000 / 822171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15330 : Bounds (31083769 / 62500000) (99468061 / 200000000) (Real.log (822171 / 500000)) := by
  have h := reflection_log_15330_neg
  have he : Real.log (822171 / 500000) = -Real.log (500000 / 822171) := by
    rw [show ((822171 / 500000) : ℝ) = ((500000 / 822171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15331_neg : (1033785683 / 1000000000) ≤ -Real.log (177829 / 500000) ∧
    -Real.log (177829 / 500000) ≤ (206757137 / 200000000) := by
  have h := checkLog_sound (w := (72171 / 427829)) (n := 12)
    (lo := (340638503 / 1000000000)) (hi := (42579813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177829) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177829) = 1/(177829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15331 : Bounds (-206757137 / 200000000) (-1033785683 / 1000000000) (Real.log (177829 / 500000)) := by
  have h := reflection_log_15331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15332_neg : (99581387 / 200000000) ≤ -Real.log (500000 / 822637) ∧
    -Real.log (500000 / 822637) ≤ (62238367 / 125000000) := by
  have h := checkLog_sound (w := (322637 / 1322637)) (n := 12)
    (lo := (99581387 / 200000000)) (hi := (62238367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822637 / 500000) = 1/(500000 / 822637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15332 : Bounds (99581387 / 200000000) (62238367 / 125000000) (Real.log (822637 / 500000)) := by
  have h := reflection_log_15332_neg
  have he : Real.log (822637 / 500000) = -Real.log (500000 / 822637) := by
    rw [show ((822637 / 500000) : ℝ) = ((500000 / 822637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15333_neg : (1036409617 / 1000000000) ≤ -Real.log (177363 / 500000) ∧
    -Real.log (177363 / 500000) ≤ (1036409619 / 1000000000) := by
  have h := checkLog_sound (w := (72637 / 427363)) (n := 12)
    (lo := (343262437 / 1000000000)) (hi := (171631219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177363) = 1/(177363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15333 : Bounds (-1036409619 / 1000000000) (-1036409617 / 1000000000) (Real.log (177363 / 500000)) := by
  have h := reflection_log_15333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15334_neg : (269251341 / 500000000) ≤ -Real.log (145905366231 / 250000000000) ∧
    -Real.log (145905366231 / 250000000000) ≤ (538502683 / 1000000000) := by
  have h := checkLog_sound (w := (104094633769 / 395905366231)) (n := 12)
    (lo := (269251341 / 500000000)) (hi := (538502683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145905366231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145905366231) = 1/(145905366231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15334 : Bounds (-538502683 / 1000000000) (-269251341 / 500000000) (Real.log (145905366231 / 250000000000)) := by
  have h := reflection_log_15334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15335_neg : (536445379 / 1000000000) ≤ -Real.log (146205846759 / 250000000000) ∧
    -Real.log (146205846759 / 250000000000) ≤ (26822269 / 50000000) := by
  have h := checkLog_sound (w := (103794153241 / 396205846759)) (n := 12)
    (lo := (536445379 / 1000000000)) (hi := (26822269 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146205846759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146205846759) = 1/(146205846759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15335 : Bounds (-26822269 / 50000000) (-536445379 / 1000000000) (Real.log (146205846759 / 250000000000)) := by
  have h := reflection_log_15335_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15336_neg : (1531125987 / 1000000000) ≤ -Real.log (125000000000 / 577922470463) ∧
    -Real.log (125000000000 / 577922470463) ≤ (153112599 / 100000000) := by
  have h := checkLog_sound (w := (77922470463 / 1077922470463)) (n := 12)
    (lo := (144831627 / 1000000000)) (hi := (36207907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577922470463 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(577922470463 / 500000000000) = 1/(125000000000 / 577922470463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15336 : Bounds (1531125987 / 1000000000) (153112599 / 100000000) (Real.log (577922470463 / 125000000000)) := by
  have h := reflection_log_15336_neg
  have he : Real.log (577922470463 / 125000000000) = -Real.log (125000000000 / 577922470463) := by
    rw [show ((577922470463 / 125000000000) : ℝ) = ((125000000000 / 577922470463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15337_neg : (1534316553 / 1000000000) ≤ -Real.log (31250000000 / 144942328727) ∧
    -Real.log (31250000000 / 144942328727) ≤ (383579139 / 250000000) := by
  have h := checkLog_sound (w := (19942328727 / 269942328727)) (n := 12)
    (lo := (148022193 / 1000000000)) (hi := (74011097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144942328727 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(144942328727 / 125000000000) = 1/(31250000000 / 144942328727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15337 : Bounds (1534316553 / 1000000000) (383579139 / 250000000) (Real.log (144942328727 / 31250000000)) := by
  have h := reflection_log_15337_neg
  have he : Real.log (144942328727 / 31250000000) = -Real.log (31250000000 / 144942328727) := by
    rw [show ((144942328727 / 31250000000) : ℝ) = ((31250000000 / 144942328727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15338_neg : (5492659873 / 1000000000) ≤ -Real.log (100000000000 / 24290243902439) ∧
    -Real.log (100000000000 / 24290243902439) ≤ (5492659881 / 1000000000) := by
  have h := checkLog_sound (w := (11490243902439 / 37090243902439)) (n := 12)
    (lo := (640629613 / 1000000000)) (hi := (320314807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24290243902439 / 12800000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(24290243902439 / 12800000000000) = 1/(100000000000 / 24290243902439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15338 : Bounds (5492659873 / 1000000000) (5492659881 / 1000000000) (Real.log (24290243902439 / 100000000000)) := by
  have h := reflection_log_15338_neg
  have he : Real.log (24290243902439 / 100000000000) = -Real.log (100000000000 / 24290243902439) := by
    rw [show ((24290243902439 / 100000000000) : ℝ) = ((100000000000 / 24290243902439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15339_neg : (1379363223 / 250000000) ≤ -Real.log (1 / 249) ∧
    -Real.log (1 / 249) ≤ (55174529 / 10000000) := by
  have h := checkLog_sound (w := (121 / 377)) (n := 12)
    (lo := (83177829 / 125000000)) (hi := (665422633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 128) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(249 / 128) = 1/(1 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15339 : Bounds (1379363223 / 250000000) (55174529 / 10000000) (Real.log (249 / 1)) := by
  have h := reflection_log_15339_neg
  have he : Real.log (249 / 1) = -Real.log (1 / 249) := by
    rw [show ((249 / 1) : ℝ) = ((1 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15340_neg : (137847911 / 200000000) ≤ -Real.log (5000 / 9961) ∧
    -Real.log (5000 / 9961) ≤ (172309889 / 250000000) := by
  have h := checkLog_sound (w := (4961 / 14961)) (n := 12)
    (lo := (137847911 / 200000000)) (hi := (172309889 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9961 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9961 / 5000) = 1/(5000 / 9961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15340 : Bounds (137847911 / 200000000) (172309889 / 250000000) (Real.log (9961 / 5000)) := by
  have h := reflection_log_15340_neg
  have he : Real.log (9961 / 5000) = -Real.log (5000 / 9961) := by
    rw [show ((9961 / 5000) : ℝ) = ((5000 / 9961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15341_neg : (4853631541 / 1000000000) ≤ -Real.log (39 / 5000) ∧
    -Real.log (39 / 5000) ≤ (4853631549 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1249)) (n := 12)
    (lo := (1601281 / 1000000000)) (hi := (800641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 624) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 624) = 1/(39 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15341 : Bounds (-4853631549 / 1000000000) (-4853631541 / 1000000000) (Real.log (39 / 5000)) := by
  have h := reflection_log_15341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15342_neg : (247927 / 250000000) ≤ -Real.log (5000000 / 5004961) ∧
    -Real.log (5000000 / 5004961) ≤ (991709 / 1000000000) := by
  have h := checkLog_sound (w := (4961 / 10004961)) (n := 12)
    (lo := (247927 / 250000000)) (hi := (991709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004961 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004961 / 5000000) = 1/(5000000 / 5004961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15342 : Bounds (247927 / 250000000) (991709 / 1000000000) (Real.log (5004961 / 5000000)) := by
  have h := reflection_log_15342_neg
  have he : Real.log (5004961 / 5000000) = -Real.log (5000000 / 5004961) := by
    rw [show ((5004961 / 5000000) : ℝ) = ((5000000 / 5004961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15343_neg : (248173 / 250000000) ≤ -Real.log (4995039 / 5000000) ∧
    -Real.log (4995039 / 5000000) ≤ (992693 / 1000000000) := by
  have h := checkLog_sound (w := (4961 / 9995039)) (n := 12)
    (lo := (248173 / 250000000)) (hi := (992693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995039) = 1/(4995039 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15343 : Bounds (-992693 / 1000000000) (-248173 / 250000000) (Real.log (4995039 / 5000000)) := by
  have h := reflection_log_15343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15344_neg : (497525163 / 1000000000) ≤ -Real.log (500000 / 822323) ∧
    -Real.log (500000 / 822323) ≤ (124381291 / 250000000) := by
  have h := checkLog_sound (w := (322323 / 1322323)) (n := 12)
    (lo := (497525163 / 1000000000)) (hi := (124381291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822323 / 500000) = 1/(500000 / 822323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15344 : Bounds (497525163 / 1000000000) (124381291 / 250000000) (Real.log (822323 / 500000)) := by
  have h := reflection_log_15344_neg
  have he : Real.log (822323 / 500000) = -Real.log (500000 / 822323) := by
    rw [show ((822323 / 500000) : ℝ) = ((500000 / 822323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15345_neg : (517320401 / 500000000) ≤ -Real.log (177677 / 500000) ∧
    -Real.log (177677 / 500000) ≤ (258660201 / 250000000) := by
  have h := checkLog_sound (w := (72323 / 427677)) (n := 12)
    (lo := (170746811 / 500000000)) (hi := (341493623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177677) = 1/(177677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15345 : Bounds (-258660201 / 250000000) (-517320401 / 500000000) (Real.log (177677 / 500000)) := by
  have h := reflection_log_15345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15346_neg : (49809169 / 100000000) ≤ -Real.log (500000 / 822789) ∧
    -Real.log (500000 / 822789) ≤ (498091691 / 1000000000) := by
  have h := checkLog_sound (w := (322789 / 1322789)) (n := 12)
    (lo := (49809169 / 100000000)) (hi := (498091691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822789 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822789 / 500000) = 1/(500000 / 822789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15346 : Bounds (49809169 / 100000000) (498091691 / 1000000000) (Real.log (822789 / 500000)) := by
  have h := reflection_log_15346_neg
  have he : Real.log (822789 / 500000) = -Real.log (500000 / 822789) := by
    rw [show ((822789 / 500000) : ℝ) = ((500000 / 822789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15347_neg : (129658373 / 125000000) ≤ -Real.log (177211 / 500000) ∧
    -Real.log (177211 / 500000) ≤ (518633493 / 500000000) := by
  have h := checkLog_sound (w := (72789 / 427211)) (n := 12)
    (lo := (86029951 / 250000000)) (hi := (68823961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177211) = 1/(177211 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15347 : Bounds (-518633493 / 500000000) (-129658373 / 125000000) (Real.log (177211 / 500000)) := by
  have h := reflection_log_15347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15348_neg : (107835059 / 200000000) ≤ -Real.log (145807261479 / 250000000000) ∧
    -Real.log (145807261479 / 250000000000) ≤ (4212307 / 7812500) := by
  have h := checkLog_sound (w := (104192738521 / 395807261479)) (n := 12)
    (lo := (107835059 / 200000000)) (hi := (4212307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145807261479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145807261479) = 1/(145807261479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15348 : Bounds (-4212307 / 7812500) (-107835059 / 200000000) (Real.log (145807261479 / 250000000000)) := by
  have h := reflection_log_15348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15349_neg : (537115639 / 1000000000) ≤ -Real.log (146107883671 / 250000000000) ∧
    -Real.log (146107883671 / 250000000000) ≤ (13427891 / 25000000) := by
  have h := checkLog_sound (w := (103892116329 / 396107883671)) (n := 12)
    (lo := (537115639 / 1000000000)) (hi := (13427891 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146107883671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146107883671) = 1/(146107883671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15349 : Bounds (-13427891 / 25000000) (-537115639 / 1000000000) (Real.log (146107883671 / 250000000000)) := by
  have h := reflection_log_15349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15350_neg : (306433193 / 200000000) ≤ -Real.log (500000000000 / 2314095240239) ∧
    -Real.log (500000000000 / 2314095240239) ≤ (95760373 / 62500000) := by
  have h := checkLog_sound (w := (314095240239 / 4314095240239)) (n := 12)
    (lo := (29174321 / 200000000)) (hi := (72935803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2314095240239 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2314095240239 / 2000000000000) = 1/(500000000000 / 2314095240239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15350 : Bounds (306433193 / 200000000) (95760373 / 62500000) (Real.log (2314095240239 / 500000000000)) := by
  have h := reflection_log_15350_neg
  have he : Real.log (2314095240239 / 500000000000) = -Real.log (500000000000 / 2314095240239) := by
    rw [show ((2314095240239 / 500000000000) : ℝ) = ((500000000000 / 2314095240239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15351_neg : (767679337 / 500000000) ≤ -Real.log (500000000000 / 2321495279639) ∧
    -Real.log (500000000000 / 2321495279639) ≤ (1535358677 / 1000000000) := by
  have h := checkLog_sound (w := (321495279639 / 4321495279639)) (n := 12)
    (lo := (74532157 / 500000000)) (hi := (29812863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2321495279639 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2321495279639 / 2000000000000) = 1/(500000000000 / 2321495279639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15351 : Bounds (767679337 / 500000000) (1535358677 / 1000000000) (Real.log (2321495279639 / 500000000000)) := by
  have h := reflection_log_15351_neg
  have he : Real.log (2321495279639 / 500000000000) = -Real.log (500000000000 / 2321495279639) := by
    rw [show ((2321495279639 / 500000000000) : ℝ) = ((500000000000 / 2321495279639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15352_neg : (5542871097 / 1000000000) ≤ -Real.log (500000000000 / 127705128205129) ∧
    -Real.log (500000000000 / 127705128205129) ≤ (1108574221 / 200000000) := by
  have h := checkLog_sound (w := (63705128205129 / 191705128205129)) (n := 12)
    (lo := (690840837 / 1000000000)) (hi := (345420419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127705128205129 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(127705128205129 / 64000000000000) = 1/(500000000000 / 127705128205129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15352 : Bounds (5542871097 / 1000000000) (1108574221 / 200000000) (Real.log (127705128205129 / 500000000000)) := by
  have h := reflection_log_15352_neg
  have he : Real.log (127705128205129 / 500000000000) = -Real.log (500000000000 / 127705128205129) := by
    rw [show ((127705128205129 / 500000000000) : ℝ) = ((500000000000 / 127705128205129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15353_neg : (344669971 / 500000000) ≤ -Real.log (2500 / 4981) ∧
    -Real.log (2500 / 4981) ≤ (689339943 / 1000000000) := by
  have h := checkLog_sound (w := (2481 / 7481)) (n := 12)
    (lo := (344669971 / 500000000)) (hi := (689339943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4981 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4981 / 2500) = 1/(2500 / 4981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15353 : Bounds (344669971 / 500000000) (689339943 / 1000000000) (Real.log (4981 / 2500)) := by
  have h := reflection_log_15353_neg
  have he : Real.log (4981 / 2500) = -Real.log (2500 / 4981) := by
    rw [show ((4981 / 2500) : ℝ) = ((2500 / 4981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15354_neg : (4879607027 / 1000000000) ≤ -Real.log (19 / 2500) ∧
    -Real.log (19 / 2500) ≤ (975921407 / 200000000) := by
  have h := checkLog_sound (w := (17 / 1233)) (n := 12)
    (lo := (27576767 / 1000000000)) (hi := (430887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 608) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 608) = 1/(19 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15354 : Bounds (-975921407 / 200000000) (-4879607027 / 1000000000) (Real.log (19 / 2500)) := by
  have h := reflection_log_15354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15355_neg : (991907 / 1000000000) ≤ -Real.log (2500000 / 2502481) ∧
    -Real.log (2500000 / 2502481) ≤ (247977 / 250000000) := by
  have h := checkLog_sound (w := (2481 / 5002481)) (n := 12)
    (lo := (991907 / 1000000000)) (hi := (247977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502481 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502481 / 2500000) = 1/(2500000 / 2502481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15355 : Bounds (991907 / 1000000000) (247977 / 250000000) (Real.log (2502481 / 2500000)) := by
  have h := reflection_log_15355_neg
  have he : Real.log (2502481 / 2500000) = -Real.log (2500000 / 2502481) := by
    rw [show ((2502481 / 2500000) : ℝ) = ((2500000 / 2502481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15356_neg : (248223 / 250000000) ≤ -Real.log (2497519 / 2500000) ∧
    -Real.log (2497519 / 2500000) ≤ (992893 / 1000000000) := by
  have h := checkLog_sound (w := (2481 / 4997519)) (n := 12)
    (lo := (248223 / 250000000)) (hi := (992893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497519) = 1/(2497519 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15356 : Bounds (-992893 / 1000000000) (-248223 / 250000000) (Real.log (2497519 / 2500000)) := by
  have h := reflection_log_15356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15357_neg : (124427497 / 250000000) ≤ -Real.log (20000 / 32899) ∧
    -Real.log (20000 / 32899) ≤ (497709989 / 1000000000) := by
  have h := checkLog_sound (w := (12899 / 52899)) (n := 12)
    (lo := (124427497 / 250000000)) (hi := (497709989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32899 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32899 / 20000) = 1/(20000 / 32899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15357 : Bounds (124427497 / 250000000) (497709989 / 1000000000) (Real.log (32899 / 20000)) := by
  have h := reflection_log_15357_neg
  have he : Real.log (32899 / 20000) = -Real.log (20000 / 32899) := by
    rw [show ((32899 / 20000) : ℝ) = ((20000 / 32899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15358_neg : (1035496653 / 1000000000) ≤ -Real.log (7101 / 20000) ∧
    -Real.log (7101 / 20000) ≤ (207099331 / 200000000) := by
  have h := checkLog_sound (w := (2899 / 17101)) (n := 12)
    (lo := (342349473 / 1000000000)) (hi := (171174737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10000 / 7101) = 1/(7101 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15358 : Bounds (-207099331 / 200000000) (-1035496653 / 1000000000) (Real.log (7101 / 20000)) := by
  have h := reflection_log_15358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15359_neg : (249138509 / 500000000) ≤ -Real.log (1000000 / 1645883) ∧
    -Real.log (1000000 / 1645883) ≤ (498277019 / 1000000000) := by
  have h := checkLog_sound (w := (645883 / 2645883)) (n := 12)
    (lo := (249138509 / 500000000)) (hi := (498277019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1645883 / 1000000) = 1/(1000000 / 1645883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15359 : Bounds (249138509 / 500000000) (498277019 / 1000000000) (Real.log (1645883 / 1000000)) := by
  have h := reflection_log_15359_neg
  have he : Real.log (1645883 / 1000000) = -Real.log (1000000 / 1645883) := by
    rw [show ((1645883 / 1000000) : ℝ) = ((1000000 / 1645883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
