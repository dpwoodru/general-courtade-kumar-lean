import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0074
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

theorem reflection_log_1_neg : (88748461 / 250000000) ≤ -Real.log (2560 / 3651) ∧
    -Real.log (2560 / 3651) ≤ (70998769 / 200000000) := by
  have h := checkLog_sound (w := (1091 / 6211)) (n := 12)
    (lo := (88748461 / 250000000)) (hi := (70998769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3651 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3651 / 2560) = 1/(2560 / 3651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (88748461 / 250000000) (70998769 / 200000000) (Real.log (3651 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3651 / 2560) = -Real.log (2560 / 3651) := by
    rw [show ((3651 / 2560) : ℝ) = ((2560 / 3651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (555425361 / 1000000000) ≤ -Real.log (1469 / 2560) ∧
    -Real.log (1469 / 2560) ≤ (277712681 / 500000000) := by
  have h := checkLog_sound (w := (1091 / 4029)) (n := 12)
    (lo := (555425361 / 1000000000)) (hi := (277712681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1469) = 1/(1469 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-277712681 / 500000000) (-555425361 / 1000000000) (Real.log (1469 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
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


theorem reflection_log_3 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
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


theorem reflection_log_4 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (615185639 / 1000000000) ≤ -Real.log (20 / 37) ∧
    -Real.log (20 / 37) ≤ (15379641 / 25000000) := by
  have h := checkLog_sound (w := (17 / 57)) (n := 12)
    (lo := (615185639 / 1000000000)) (hi := (15379641 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 20) = 1/(20 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (615185639 / 1000000000) (15379641 / 25000000) (Real.log (37 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (37 / 20) = -Real.log (20 / 37) := by
    rw [show ((37 / 20) : ℝ) = ((20 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1897119983 / 1000000000) ≤ -Real.log (3 / 20) ∧
    -Real.log (3 / 20) ≤ (948559993 / 500000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5 / 3) = 1/(3 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-948559993 / 500000000) (-1897119983 / 1000000000) (Real.log (3 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (243927299 / 500000000) ≤ -Real.log (500000 / 814409) ∧
    -Real.log (500000 / 814409) ≤ (487854599 / 1000000000) := by
  have h := checkLog_sound (w := (314409 / 1314409)) (n := 12)
    (lo := (243927299 / 500000000)) (hi := (487854599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814409 / 500000) = 1/(500000 / 814409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (243927299 / 500000000) (487854599 / 1000000000) (Real.log (814409 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (814409 / 500000) = -Real.log (500000 / 814409) := by
    rw [show ((814409 / 500000) : ℝ) = ((500000 / 814409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99106277 / 100000000) ≤ -Real.log (185591 / 500000) ∧
    -Real.log (185591 / 500000) ≤ (247765693 / 250000000) := by
  have h := checkLog_sound (w := (64409 / 435591)) (n := 12)
    (lo := (29791559 / 100000000)) (hi := (297915591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185591) = 1/(185591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-247765693 / 250000000) (-99106277 / 100000000) (Real.log (185591 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9781561 / 20000000) ≤ -Real.log (250000 / 407703) ∧
    -Real.log (250000 / 407703) ≤ (489078051 / 1000000000) := by
  have h := checkLog_sound (w := (157703 / 657703)) (n := 12)
    (lo := (9781561 / 20000000)) (hi := (489078051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407703 / 250000) = 1/(250000 / 407703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9781561 / 20000000) (489078051 / 1000000000) (Real.log (407703 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (407703 / 250000) = -Real.log (250000 / 407703) := by
    rw [show ((407703 / 250000) : ℝ) = ((250000 / 407703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (996449279 / 1000000000) ≤ -Real.log (92297 / 250000) ∧
    -Real.log (92297 / 250000) ≤ (996449281 / 1000000000) := by
  have h := checkLog_sound (w := (32703 / 217297)) (n := 12)
    (lo := (303302099 / 1000000000)) (hi := (3033021 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 92297) = 1/(92297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-996449281 / 1000000000) (-996449279 / 1000000000) (Real.log (92297 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (404631427 / 1000000000) ≤ -Real.log (800 / 1199) ∧
    -Real.log (800 / 1199) ≤ (101157857 / 250000000) := by
  have h := checkLog_sound (w := (399 / 1999)) (n := 12)
    (lo := (404631427 / 1000000000)) (hi := (101157857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 800) = 1/(800 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (404631427 / 1000000000) (101157857 / 250000000) (Real.log (1199 / 800)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1199 / 800) = -Real.log (800 / 1199) := by
    rw [show ((1199 / 800) : ℝ) = ((800 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6906503 / 10000000) ≤ -Real.log (401 / 800) ∧
    -Real.log (401 / 800) ≤ (690650301 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 1201)) (n := 12)
    (lo := (6906503 / 10000000)) (hi := (690650301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 401) = 1/(401 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-690650301 / 1000000000) (-6906503 / 10000000) (Real.log (401 / 800)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202969831 / 500000000) ≤ -Real.log (125000 / 187589) ∧
    -Real.log (125000 / 187589) ≤ (405939663 / 1000000000) := by
  have h := checkLog_sound (w := (62589 / 312589)) (n := 12)
    (lo := (202969831 / 500000000)) (hi := (405939663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187589 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187589 / 125000) = 1/(125000 / 187589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202969831 / 500000000) (405939663 / 1000000000) (Real.log (187589 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (187589 / 125000) = -Real.log (125000 / 187589) := by
    rw [show ((187589 / 125000) : ℝ) = ((125000 / 187589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (347286097 / 500000000) ≤ -Real.log (62411 / 125000) ∧
    -Real.log (62411 / 125000) ≤ (173643049 / 250000000) := by
  have h := checkLog_sound (w := (89 / 124911)) (n := 12)
    (lo := (712507 / 500000000)) (hi := (285003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 62411) = 1/(62411 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-173643049 / 250000000) (-347286097 / 500000000) (Real.log (62411 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1478917367 / 1000000000) ≤ -Real.log (6250000000 / 27426201971) ∧
    -Real.log (6250000000 / 27426201971) ≤ (147891737 / 100000000) := by
  have h := checkLog_sound (w := (2426201971 / 52426201971)) (n := 12)
    (lo := (92623007 / 1000000000)) (hi := (2894469 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27426201971 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(27426201971 / 25000000000) = 1/(6250000000 / 27426201971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1478917367 / 1000000000) (147891737 / 100000000) (Real.log (27426201971 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27426201971 / 6250000000) = -Real.log (6250000000 / 27426201971) := by
    rw [show ((27426201971 / 6250000000) : ℝ) = ((6250000000 / 27426201971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (46422729 / 31250000) ≤ -Real.log (100000000000 / 441729416991) ∧
    -Real.log (100000000000 / 441729416991) ≤ (1485527331 / 1000000000) := by
  have h := checkLog_sound (w := (41729416991 / 841729416991)) (n := 12)
    (lo := (12404121 / 125000000)) (hi := (99232969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441729416991 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(441729416991 / 400000000000) = 1/(100000000000 / 441729416991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (46422729 / 31250000) (1485527331 / 1000000000) (Real.log (441729416991 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (441729416991 / 100000000000) = -Real.log (100000000000 / 441729416991) := by
    rw [show ((441729416991 / 100000000000) : ℝ) = ((100000000000 / 441729416991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1095281727 / 1000000000) ≤ -Real.log (500000000000 / 1495012468827) ∧
    -Real.log (500000000000 / 1495012468827) ≤ (1095281729 / 1000000000) := by
  have h := checkLog_sound (w := (495012468827 / 2495012468827)) (n := 12)
    (lo := (402134547 / 1000000000)) (hi := (100533637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495012468827 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495012468827 / 1000000000000) = 1/(500000000000 / 1495012468827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1095281727 / 1000000000) (1095281729 / 1000000000) (Real.log (1495012468827 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1495012468827 / 500000000000) = -Real.log (500000000000 / 1495012468827) := by
    rw [show ((1495012468827 / 500000000000) : ℝ) = ((500000000000 / 1495012468827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1100511857 / 1000000000) ≤ -Real.log (62500000000 / 187856507667) ∧
    -Real.log (62500000000 / 187856507667) ≤ (1100511859 / 1000000000) := by
  have h := checkLog_sound (w := (62856507667 / 312856507667)) (n := 12)
    (lo := (407364677 / 1000000000)) (hi := (203682339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187856507667 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(187856507667 / 125000000000) = 1/(62500000000 / 187856507667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1100511857 / 1000000000) (1100511859 / 1000000000) (Real.log (187856507667 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (187856507667 / 62500000000) = -Real.log (62500000000 / 187856507667) := by
    rw [show ((187856507667 / 62500000000) : ℝ) = ((62500000000 / 187856507667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0074
