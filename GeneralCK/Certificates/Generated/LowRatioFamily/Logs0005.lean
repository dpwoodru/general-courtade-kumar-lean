import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_320_neg : (15318887 / 100000000) ≤ -Real.log (62500000000 / 72846568423) ∧
    -Real.log (62500000000 / 72846568423) ≤ (153188871 / 1000000000) := by
  have h := checkLog_sound (w := (10346568423 / 135346568423)) (n := 12)
    (lo := (15318887 / 100000000)) (hi := (153188871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72846568423 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72846568423 / 62500000000) = 1/(62500000000 / 72846568423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_320 : Bounds (15318887 / 100000000) (153188871 / 1000000000) (Real.log (72846568423 / 62500000000)) := by
  have h := reflection_log_320_neg
  have he : Real.log (72846568423 / 62500000000) = -Real.log (62500000000 / 72846568423) := by
    rw [show ((72846568423 / 62500000000) : ℝ) = ((62500000000 / 72846568423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_321_neg : (153597263 / 1000000000) ≤ -Real.log (31250000000 / 36438162261) ∧
    -Real.log (31250000000 / 36438162261) ≤ (9599829 / 62500000) := by
  have h := checkLog_sound (w := (5188162261 / 67688162261)) (n := 12)
    (lo := (153597263 / 1000000000)) (hi := (9599829 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36438162261 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36438162261 / 31250000000) = 1/(31250000000 / 36438162261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_321 : Bounds (153597263 / 1000000000) (9599829 / 62500000) (Real.log (36438162261 / 31250000000)) := by
  have h := reflection_log_321_neg
  have he : Real.log (36438162261 / 31250000000) = -Real.log (31250000000 / 36438162261) := by
    rw [show ((36438162261 / 31250000000) : ℝ) = ((31250000000 / 36438162261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_322_neg : (38399147 / 125000000) ≤ -Real.log (250000000000 / 339900896649) ∧
    -Real.log (250000000000 / 339900896649) ≤ (307193177 / 1000000000) := by
  have h := checkLog_sound (w := (89900896649 / 589900896649)) (n := 12)
    (lo := (38399147 / 125000000)) (hi := (307193177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339900896649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339900896649 / 250000000000) = 1/(250000000000 / 339900896649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_322 : Bounds (38399147 / 125000000) (307193177 / 1000000000) (Real.log (339900896649 / 250000000000)) := by
  have h := reflection_log_322_neg
  have he : Real.log (339900896649 / 250000000000) = -Real.log (250000000000 / 339900896649) := by
    rw [show ((339900896649 / 250000000000) : ℝ) = ((250000000000 / 339900896649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_323_neg : (61479587 / 200000000) ≤ -Real.log (10000000000 / 13598820059) ∧
    -Real.log (10000000000 / 13598820059) ≤ (19212371 / 62500000) := by
  have h := checkLog_sound (w := (3598820059 / 23598820059)) (n := 12)
    (lo := (61479587 / 200000000)) (hi := (19212371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13598820059 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13598820059 / 10000000000) = 1/(10000000000 / 13598820059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_323 : Bounds (61479587 / 200000000) (19212371 / 62500000) (Real.log (13598820059 / 10000000000)) := by
  have h := reflection_log_323_neg
  have he : Real.log (13598820059 / 10000000000) = -Real.log (10000000000 / 13598820059) := by
    rw [show ((13598820059 / 10000000000) : ℝ) = ((10000000000 / 13598820059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_324_neg : (7101013 / 50000000) ≤ -Real.log (5000 / 5763) ∧
    -Real.log (5000 / 5763) ≤ (142020261 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 10763)) (n := 12)
    (lo := (7101013 / 50000000)) (hi := (142020261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5763 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5763 / 5000) = 1/(5000 / 5763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_324 : Bounds (7101013 / 50000000) (142020261 / 1000000000) (Real.log (5763 / 5000)) := by
  have h := reflection_log_324_neg
  have he : Real.log (5763 / 5000) = -Real.log (5000 / 5763) := by
    rw [show ((5763 / 5000) : ℝ) = ((5000 / 5763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_325_neg : (4139561 / 25000000) ≤ -Real.log (4237 / 5000) ∧
    -Real.log (4237 / 5000) ≤ (165582441 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 9237)) (n := 12)
    (lo := (4139561 / 25000000)) (hi := (165582441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4237) = 1/(4237 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_325 : Bounds (-165582441 / 1000000000) (-4139561 / 25000000) (Real.log (4237 / 5000)) := by
  have h := reflection_log_325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_326_neg : (38147 / 250000000) ≤ -Real.log (5000000 / 5000763) ∧
    -Real.log (5000000 / 5000763) ≤ (152589 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 10000763)) (n := 12)
    (lo := (38147 / 250000000)) (hi := (152589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000763 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000763 / 5000000) = 1/(5000000 / 5000763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_326 : Bounds (38147 / 250000000) (152589 / 1000000000) (Real.log (5000763 / 5000000)) := by
  have h := reflection_log_326_neg
  have he : Real.log (5000763 / 5000000) = -Real.log (5000000 / 5000763) := by
    rw [show ((5000763 / 5000000) : ℝ) = ((5000000 / 5000763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_327_neg : (152611 / 1000000000) ≤ -Real.log (4999237 / 5000000) ∧
    -Real.log (4999237 / 5000000) ≤ (38153 / 250000000) := by
  have h := checkLog_sound (w := (763 / 9999237)) (n := 12)
    (lo := (152611 / 1000000000)) (hi := (38153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999237) = 1/(4999237 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_327 : Bounds (-38153 / 250000000) (-152611 / 1000000000) (Real.log (4999237 / 5000000)) := by
  have h := reflection_log_327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_328_neg : (73899879 / 1000000000) ≤ -Real.log (1000000 / 1076699) ∧
    -Real.log (1000000 / 1076699) ≤ (1847497 / 25000000) := by
  have h := checkLog_sound (w := (76699 / 2076699)) (n := 12)
    (lo := (73899879 / 1000000000)) (hi := (1847497 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076699 / 1000000) = 1/(1000000 / 1076699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_328 : Bounds (73899879 / 1000000000) (1847497 / 25000000) (Real.log (1076699 / 1000000)) := by
  have h := reflection_log_328_neg
  have he : Real.log (1076699 / 1000000) = -Real.log (1000000 / 1076699) := by
    rw [show ((1076699 / 1000000) : ℝ) = ((1000000 / 1076699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_329_neg : (79799987 / 1000000000) ≤ -Real.log (923301 / 1000000) ∧
    -Real.log (923301 / 1000000) ≤ (19949997 / 250000000) := by
  have h := checkLog_sound (w := (76699 / 1923301)) (n := 12)
    (lo := (79799987 / 1000000000)) (hi := (19949997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923301) = 1/(923301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_329 : Bounds (-19949997 / 250000000) (-79799987 / 1000000000) (Real.log (923301 / 1000000)) := by
  have h := reflection_log_329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_330_neg : (1475027 / 250000000) ≤ -Real.log (994117263399 / 1000000000000) ∧
    -Real.log (994117263399 / 1000000000000) ≤ (5900109 / 1000000000) := by
  have h := checkLog_sound (w := (5882736601 / 1994117263399)) (n := 12)
    (lo := (1475027 / 250000000)) (hi := (5900109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994117263399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994117263399) = 1/(994117263399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_330 : Bounds (-5900109 / 1000000000) (-1475027 / 250000000) (Real.log (994117263399 / 1000000000000)) := by
  have h := reflection_log_330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_331_neg : (15329147 / 100000000) ≤ -Real.log (250000000000 / 291416171451) ∧
    -Real.log (250000000000 / 291416171451) ≤ (153291471 / 1000000000) := by
  have h := checkLog_sound (w := (41416171451 / 541416171451)) (n := 12)
    (lo := (15329147 / 100000000)) (hi := (153291471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291416171451 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291416171451 / 250000000000) = 1/(250000000000 / 291416171451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_331 : Bounds (15329147 / 100000000) (153291471 / 1000000000) (Real.log (291416171451 / 250000000000)) := by
  have h := reflection_log_331_neg
  have he : Real.log (291416171451 / 250000000000) = -Real.log (250000000000 / 291416171451) := by
    rw [show ((291416171451 / 250000000000) : ℝ) = ((250000000000 / 291416171451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_332_neg : (76849933 / 500000000) ≤ -Real.log (50000000000 / 58307041799) ∧
    -Real.log (50000000000 / 58307041799) ≤ (153699867 / 1000000000) := by
  have h := checkLog_sound (w := (8307041799 / 108307041799)) (n := 12)
    (lo := (76849933 / 500000000)) (hi := (153699867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58307041799 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58307041799 / 50000000000) = 1/(50000000000 / 58307041799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_332 : Bounds (76849933 / 500000000) (153699867 / 1000000000) (Real.log (58307041799 / 50000000000)) := by
  have h := reflection_log_332_neg
  have he : Real.log (58307041799 / 50000000000) = -Real.log (50000000000 / 58307041799) := by
    rw [show ((58307041799 / 50000000000) : ℝ) = ((50000000000 / 58307041799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_333_neg : (61479587 / 200000000) ≤ -Real.log (500000000000 / 679941002949) ∧
    -Real.log (500000000000 / 679941002949) ≤ (19212371 / 62500000) := by
  have h := checkLog_sound (w := (179941002949 / 1179941002949)) (n := 12)
    (lo := (61479587 / 200000000)) (hi := (19212371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679941002949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679941002949 / 500000000000) = 1/(500000000000 / 679941002949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_333 : Bounds (61479587 / 200000000) (19212371 / 62500000) (Real.log (679941002949 / 500000000000)) := by
  have h := reflection_log_333_neg
  have he : Real.log (679941002949 / 500000000000) = -Real.log (500000000000 / 679941002949) := by
    rw [show ((679941002949 / 500000000000) : ℝ) = ((500000000000 / 679941002949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_334_neg : (3076027 / 10000000) ≤ -Real.log (500000000000 / 680080245457) ∧
    -Real.log (500000000000 / 680080245457) ≤ (307602701 / 1000000000) := by
  have h := checkLog_sound (w := (180080245457 / 1180080245457)) (n := 12)
    (lo := (3076027 / 10000000)) (hi := (307602701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680080245457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680080245457 / 500000000000) = 1/(500000000000 / 680080245457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_334 : Bounds (3076027 / 10000000) (307602701 / 1000000000) (Real.log (680080245457 / 500000000000)) := by
  have h := reflection_log_334_neg
  have he : Real.log (680080245457 / 500000000000) = -Real.log (500000000000 / 680080245457) := by
    rw [show ((680080245457 / 500000000000) : ℝ) = ((500000000000 / 680080245457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_335_neg : (17763377 / 125000000) ≤ -Real.log (10000 / 11527) ∧
    -Real.log (10000 / 11527) ≤ (142107017 / 1000000000) := by
  have h := checkLog_sound (w := (1527 / 21527)) (n := 12)
    (lo := (17763377 / 125000000)) (hi := (142107017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11527 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11527 / 10000) = 1/(10000 / 11527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_335 : Bounds (17763377 / 125000000) (142107017 / 1000000000) (Real.log (11527 / 10000)) := by
  have h := reflection_log_335_neg
  have he : Real.log (11527 / 10000) = -Real.log (10000 / 11527) := by
    rw [show ((11527 / 10000) : ℝ) = ((10000 / 11527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_336_neg : (33140091 / 200000000) ≤ -Real.log (8473 / 10000) ∧
    -Real.log (8473 / 10000) ≤ (20712557 / 125000000) := by
  have h := checkLog_sound (w := (1527 / 18473)) (n := 12)
    (lo := (33140091 / 200000000)) (hi := (20712557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8473) = 1/(8473 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_336 : Bounds (-20712557 / 125000000) (-33140091 / 200000000) (Real.log (8473 / 10000)) := by
  have h := reflection_log_336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_337_neg : (9543 / 62500000) ≤ -Real.log (10000000 / 10001527) ∧
    -Real.log (10000000 / 10001527) ≤ (152689 / 1000000000) := by
  have h := checkLog_sound (w := (1527 / 20001527)) (n := 12)
    (lo := (9543 / 62500000)) (hi := (152689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001527 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001527 / 10000000) = 1/(10000000 / 10001527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_337 : Bounds (9543 / 62500000) (152689 / 1000000000) (Real.log (10001527 / 10000000)) := by
  have h := reflection_log_337_neg
  have he : Real.log (10001527 / 10000000) = -Real.log (10000000 / 10001527) := by
    rw [show ((10001527 / 10000000) : ℝ) = ((10000000 / 10001527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_338_neg : (152711 / 1000000000) ≤ -Real.log (9998473 / 10000000) ∧
    -Real.log (9998473 / 10000000) ≤ (19089 / 125000000) := by
  have h := checkLog_sound (w := (1527 / 19998473)) (n := 12)
    (lo := (152711 / 1000000000)) (hi := (19089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998473) = 1/(9998473 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_338 : Bounds (-19089 / 125000000) (-152711 / 1000000000) (Real.log (9998473 / 10000000)) := by
  have h := reflection_log_338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_339_neg : (73757767 / 1000000000) ≤ -Real.log (500000 / 538273) ∧
    -Real.log (500000 / 538273) ≤ (9219721 / 125000000) := by
  have h := checkLog_sound (w := (38273 / 1038273)) (n := 12)
    (lo := (73757767 / 1000000000)) (hi := (9219721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538273 / 500000) = 1/(500000 / 538273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_339 : Bounds (73757767 / 1000000000) (9219721 / 125000000) (Real.log (538273 / 500000)) := by
  have h := reflection_log_339_neg
  have he : Real.log (538273 / 500000) = -Real.log (500000 / 538273) := by
    rw [show ((538273 / 500000) : ℝ) = ((500000 / 538273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_340_neg : (79634291 / 1000000000) ≤ -Real.log (461727 / 500000) ∧
    -Real.log (461727 / 500000) ≤ (19908573 / 250000000) := by
  have h := checkLog_sound (w := (38273 / 961727)) (n := 12)
    (lo := (79634291 / 1000000000)) (hi := (19908573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461727) = 1/(461727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_340 : Bounds (-19908573 / 250000000) (-79634291 / 1000000000) (Real.log (461727 / 500000)) := by
  have h := reflection_log_340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_341_neg : (18486811 / 250000000) ≤ -Real.log (4000 / 4307) ∧
    -Real.log (4000 / 4307) ≤ (14789449 / 200000000) := by
  have h := checkLog_sound (w := (307 / 8307)) (n := 12)
    (lo := (18486811 / 250000000)) (hi := (14789449 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4307 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4307 / 4000) = 1/(4000 / 4307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_341 : Bounds (18486811 / 250000000) (14789449 / 200000000) (Real.log (4307 / 4000)) := by
  have h := reflection_log_341_neg
  have he : Real.log (4307 / 4000) = -Real.log (4000 / 4307) := by
    rw [show ((4307 / 4000) : ℝ) = ((4000 / 4307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_342_neg : (3194209 / 40000000) ≤ -Real.log (3693 / 4000) ∧
    -Real.log (3693 / 4000) ≤ (39927613 / 500000000) := by
  have h := checkLog_sound (w := (307 / 7693)) (n := 12)
    (lo := (3194209 / 40000000)) (hi := (39927613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3693) = 1/(3693 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_342 : Bounds (-39927613 / 500000000) (-3194209 / 40000000) (Real.log (3693 / 4000)) := by
  have h := reflection_log_342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_343_neg : (295399 / 50000000) ≤ -Real.log (15905751 / 16000000) ∧
    -Real.log (15905751 / 16000000) ≤ (5907981 / 1000000000) := by
  have h := checkLog_sound (w := (94249 / 31905751)) (n := 12)
    (lo := (295399 / 50000000)) (hi := (5907981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15905751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15905751) = 1/(15905751 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_343 : Bounds (-5907981 / 1000000000) (-295399 / 50000000) (Real.log (15905751 / 16000000)) := by
  have h := reflection_log_343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_344_neg : (5876523 / 1000000000) ≤ -Real.log (248535177471 / 250000000000) ∧
    -Real.log (248535177471 / 250000000000) ≤ (1469131 / 250000000) := by
  have h := checkLog_sound (w := (1464822529 / 498535177471)) (n := 12)
    (lo := (5876523 / 1000000000)) (hi := (1469131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248535177471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248535177471) = 1/(248535177471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_344 : Bounds (-1469131 / 250000000) (-5876523 / 1000000000) (Real.log (248535177471 / 250000000000)) := by
  have h := reflection_log_344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_345_neg : (153392059 / 1000000000) ≤ -Real.log (500000000000 / 582890972371) ∧
    -Real.log (500000000000 / 582890972371) ≤ (7669603 / 50000000) := by
  have h := checkLog_sound (w := (82890972371 / 1082890972371)) (n := 12)
    (lo := (153392059 / 1000000000)) (hi := (7669603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582890972371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582890972371 / 500000000000) = 1/(500000000000 / 582890972371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_345 : Bounds (153392059 / 1000000000) (7669603 / 50000000) (Real.log (582890972371 / 500000000000)) := by
  have h := reflection_log_345_neg
  have he : Real.log (582890972371 / 500000000000) = -Real.log (500000000000 / 582890972371) := by
    rw [show ((582890972371 / 500000000000) : ℝ) = ((500000000000 / 582890972371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_346_neg : (15380247 / 100000000) ≤ -Real.log (500000000000 / 583130246413) ∧
    -Real.log (500000000000 / 583130246413) ≤ (153802471 / 1000000000) := by
  have h := checkLog_sound (w := (83130246413 / 1083130246413)) (n := 12)
    (lo := (15380247 / 100000000)) (hi := (153802471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583130246413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583130246413 / 500000000000) = 1/(500000000000 / 583130246413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_346 : Bounds (15380247 / 100000000) (153802471 / 1000000000) (Real.log (583130246413 / 500000000000)) := by
  have h := reflection_log_346_neg
  have he : Real.log (583130246413 / 500000000000) = -Real.log (500000000000 / 583130246413) := by
    rw [show ((583130246413 / 500000000000) : ℝ) = ((500000000000 / 583130246413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_347_neg : (3076027 / 10000000) ≤ -Real.log (31250000000 / 42505015341) ∧
    -Real.log (31250000000 / 42505015341) ≤ (307602701 / 1000000000) := by
  have h := checkLog_sound (w := (11255015341 / 73755015341)) (n := 12)
    (lo := (3076027 / 10000000)) (hi := (307602701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42505015341 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42505015341 / 31250000000) = 1/(31250000000 / 42505015341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_347 : Bounds (3076027 / 10000000) (307602701 / 1000000000) (Real.log (42505015341 / 31250000000)) := by
  have h := reflection_log_347_neg
  have he : Real.log (42505015341 / 31250000000) = -Real.log (31250000000 / 42505015341) := by
    rw [show ((42505015341 / 31250000000) : ℝ) = ((31250000000 / 42505015341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_348_neg : (19237967 / 62500000) ≤ -Real.log (500000000000 / 680219520831) ∧
    -Real.log (500000000000 / 680219520831) ≤ (307807473 / 1000000000) := by
  have h := checkLog_sound (w := (180219520831 / 1180219520831)) (n := 12)
    (lo := (19237967 / 62500000)) (hi := (307807473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680219520831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680219520831 / 500000000000) = 1/(500000000000 / 680219520831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_348 : Bounds (19237967 / 62500000) (307807473 / 1000000000) (Real.log (680219520831 / 500000000000)) := by
  have h := reflection_log_348_neg
  have he : Real.log (680219520831 / 500000000000) = -Real.log (500000000000 / 680219520831) := by
    rw [show ((680219520831 / 500000000000) : ℝ) = ((500000000000 / 680219520831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_349_neg : (28438753 / 200000000) ≤ -Real.log (1250 / 1441) ∧
    -Real.log (1250 / 1441) ≤ (71096883 / 500000000) := by
  have h := checkLog_sound (w := (191 / 2691)) (n := 12)
    (lo := (28438753 / 200000000)) (hi := (71096883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441 / 1250) = 1/(1250 / 1441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_349 : Bounds (28438753 / 200000000) (71096883 / 500000000) (Real.log (1441 / 1250)) := by
  have h := reflection_log_349_neg
  have he : Real.log (1441 / 1250) = -Real.log (1250 / 1441) := by
    rw [show ((1441 / 1250) : ℝ) = ((1250 / 1441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_350_neg : (41454621 / 250000000) ≤ -Real.log (1059 / 1250) ∧
    -Real.log (1059 / 1250) ≤ (33163697 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2309)) (n := 12)
    (lo := (41454621 / 250000000)) (hi := (33163697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1059) = 1/(1059 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_350 : Bounds (-33163697 / 200000000) (-41454621 / 250000000) (Real.log (1059 / 1250)) := by
  have h := reflection_log_350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_351_neg : (38197 / 250000000) ≤ -Real.log (1250000 / 1250191) ∧
    -Real.log (1250000 / 1250191) ≤ (152789 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 2500191)) (n := 12)
    (lo := (38197 / 250000000)) (hi := (152789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250191 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250191 / 1250000) = 1/(1250000 / 1250191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_351 : Bounds (38197 / 250000000) (152789 / 1000000000) (Real.log (1250191 / 1250000)) := by
  have h := reflection_log_351_neg
  have he : Real.log (1250191 / 1250000) = -Real.log (1250000 / 1250191) := by
    rw [show ((1250191 / 1250000) : ℝ) = ((1250000 / 1250191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_352_neg : (152811 / 1000000000) ≤ -Real.log (1249809 / 1250000) ∧
    -Real.log (1249809 / 1250000) ≤ (38203 / 250000000) := by
  have h := checkLog_sound (w := (191 / 2499809)) (n := 12)
    (lo := (152811 / 1000000000)) (hi := (38203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249809) = 1/(1249809 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_352 : Bounds (-38203 / 250000000) (-152811 / 1000000000) (Real.log (1249809 / 1250000)) := by
  have h := reflection_log_352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_353_neg : (3690257 / 50000000) ≤ -Real.log (1000000 / 1076597) ∧
    -Real.log (1000000 / 1076597) ≤ (73805141 / 1000000000) := by
  have h := checkLog_sound (w := (76597 / 2076597)) (n := 12)
    (lo := (3690257 / 50000000)) (hi := (73805141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076597 / 1000000) = 1/(1000000 / 1076597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_353 : Bounds (3690257 / 50000000) (73805141 / 1000000000) (Real.log (1076597 / 1000000)) := by
  have h := reflection_log_353_neg
  have he : Real.log (1076597 / 1000000) = -Real.log (1000000 / 1076597) := by
    rw [show ((1076597 / 1000000) : ℝ) = ((1000000 / 1076597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_354_neg : (996119 / 12500000) ≤ -Real.log (923403 / 1000000) ∧
    -Real.log (923403 / 1000000) ≤ (79689521 / 1000000000) := by
  have h := checkLog_sound (w := (76597 / 1923403)) (n := 12)
    (lo := (996119 / 12500000)) (hi := (79689521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923403) = 1/(923403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_354 : Bounds (-79689521 / 1000000000) (-996119 / 12500000) (Real.log (923403 / 1000000)) := by
  have h := reflection_log_354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_355_neg : (73993679 / 1000000000) ≤ -Real.log (625 / 673) ∧
    -Real.log (625 / 673) ≤ (924921 / 12500000) := by
  have h := checkLog_sound (w := (24 / 649)) (n := 12)
    (lo := (73993679 / 1000000000)) (hi := (924921 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 625) = 1/(625 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_355 : Bounds (73993679 / 1000000000) (924921 / 12500000) (Real.log (673 / 625)) := by
  have h := reflection_log_355_neg
  have he : Real.log (673 / 625) = -Real.log (625 / 673) := by
    rw [show ((673 / 625) : ℝ) = ((625 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_356_neg : (79909383 / 1000000000) ≤ -Real.log (577 / 625) ∧
    -Real.log (577 / 625) ≤ (9988673 / 125000000) := by
  have h := checkLog_sound (w := (24 / 601)) (n := 12)
    (lo := (79909383 / 1000000000)) (hi := (9988673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 577) = 1/(577 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_356 : Bounds (-9988673 / 125000000) (-79909383 / 1000000000) (Real.log (577 / 625)) := by
  have h := reflection_log_356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_357_neg : (5915703 / 1000000000) ≤ -Real.log (388321 / 390625) ∧
    -Real.log (388321 / 390625) ≤ (739463 / 125000000) := by
  have h := checkLog_sound (w := (1152 / 389473)) (n := 12)
    (lo := (5915703 / 1000000000)) (hi := (739463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390625 / 388321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390625 / 388321) = 1/(388321 / 390625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_357 : Bounds (-739463 / 125000000) (-5915703 / 1000000000) (Real.log (388321 / 390625)) := by
  have h := reflection_log_357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_358_neg : (5884379 / 1000000000) ≤ -Real.log (994132899591 / 1000000000000) ∧
    -Real.log (994132899591 / 1000000000000) ≤ (294219 / 50000000) := by
  have h := checkLog_sound (w := (5867100409 / 1994132899591)) (n := 12)
    (lo := (5884379 / 1000000000)) (hi := (294219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994132899591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994132899591) = 1/(994132899591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_358 : Bounds (-294219 / 50000000) (-5884379 / 1000000000) (Real.log (994132899591 / 1000000000000)) := by
  have h := reflection_log_358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_359_neg : (7674733 / 50000000) ≤ -Real.log (500000000000 / 582950780969) ∧
    -Real.log (500000000000 / 582950780969) ≤ (153494661 / 1000000000) := by
  have h := checkLog_sound (w := (82950780969 / 1082950780969)) (n := 12)
    (lo := (7674733 / 50000000)) (hi := (153494661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582950780969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582950780969 / 500000000000) = 1/(500000000000 / 582950780969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_359 : Bounds (7674733 / 50000000) (153494661 / 1000000000) (Real.log (582950780969 / 500000000000)) := by
  have h := reflection_log_359_neg
  have he : Real.log (582950780969 / 500000000000) = -Real.log (500000000000 / 582950780969) := by
    rw [show ((582950780969 / 500000000000) : ℝ) = ((500000000000 / 582950780969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_360_neg : (153903063 / 1000000000) ≤ -Real.log (250000000000 / 291594454073) ∧
    -Real.log (250000000000 / 291594454073) ≤ (19237883 / 125000000) := by
  have h := checkLog_sound (w := (41594454073 / 541594454073)) (n := 12)
    (lo := (153903063 / 1000000000)) (hi := (19237883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291594454073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291594454073 / 250000000000) = 1/(250000000000 / 291594454073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_360 : Bounds (153903063 / 1000000000) (19237883 / 125000000) (Real.log (291594454073 / 250000000000)) := by
  have h := reflection_log_360_neg
  have he : Real.log (291594454073 / 250000000000) = -Real.log (250000000000 / 291594454073) := by
    rw [show ((291594454073 / 250000000000) : ℝ) = ((250000000000 / 291594454073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_361_neg : (19237967 / 62500000) ≤ -Real.log (50000000000 / 68021952083) ∧
    -Real.log (50000000000 / 68021952083) ≤ (307807473 / 1000000000) := by
  have h := checkLog_sound (w := (18021952083 / 118021952083)) (n := 12)
    (lo := (19237967 / 62500000)) (hi := (307807473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68021952083 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68021952083 / 50000000000) = 1/(50000000000 / 68021952083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_361 : Bounds (19237967 / 62500000) (307807473 / 1000000000) (Real.log (68021952083 / 50000000000)) := by
  have h := reflection_log_361_neg
  have he : Real.log (68021952083 / 50000000000) = -Real.log (50000000000 / 68021952083) := by
    rw [show ((68021952083 / 50000000000) : ℝ) = ((50000000000 / 68021952083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_362_neg : (1232049 / 4000000) ≤ -Real.log (100000000000 / 136071765817) ∧
    -Real.log (100000000000 / 136071765817) ≤ (308012251 / 1000000000) := by
  have h := checkLog_sound (w := (36071765817 / 236071765817)) (n := 12)
    (lo := (1232049 / 4000000)) (hi := (308012251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136071765817 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136071765817 / 100000000000) = 1/(100000000000 / 136071765817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_362 : Bounds (1232049 / 4000000) (308012251 / 1000000000) (Real.log (136071765817 / 100000000000)) := by
  have h := reflection_log_362_neg
  have he : Real.log (136071765817 / 100000000000) = -Real.log (100000000000 / 136071765817) := by
    rw [show ((136071765817 / 100000000000) : ℝ) = ((100000000000 / 136071765817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_363_neg : (142280507 / 1000000000) ≤ -Real.log (10000 / 11529) ∧
    -Real.log (10000 / 11529) ≤ (35570127 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 21529)) (n := 12)
    (lo := (142280507 / 1000000000)) (hi := (35570127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11529 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11529 / 10000) = 1/(10000 / 11529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_363 : Bounds (142280507 / 1000000000) (35570127 / 250000000) (Real.log (11529 / 10000)) := by
  have h := reflection_log_363_neg
  have he : Real.log (11529 / 10000) = -Real.log (10000 / 11529) := by
    rw [show ((11529 / 10000) : ℝ) = ((10000 / 11529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_364_neg : (165936527 / 1000000000) ≤ -Real.log (8471 / 10000) ∧
    -Real.log (8471 / 10000) ≤ (10371033 / 62500000) := by
  have h := checkLog_sound (w := (1529 / 18471)) (n := 12)
    (lo := (165936527 / 1000000000)) (hi := (10371033 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8471) = 1/(8471 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_364 : Bounds (-10371033 / 62500000) (-165936527 / 1000000000) (Real.log (8471 / 10000)) := by
  have h := reflection_log_364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_365_neg : (19111 / 125000000) ≤ -Real.log (10000000 / 10001529) ∧
    -Real.log (10000000 / 10001529) ≤ (152889 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 20001529)) (n := 12)
    (lo := (19111 / 125000000)) (hi := (152889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001529 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001529 / 10000000) = 1/(10000000 / 10001529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_365 : Bounds (19111 / 125000000) (152889 / 1000000000) (Real.log (10001529 / 10000000)) := by
  have h := reflection_log_365_neg
  have he : Real.log (10001529 / 10000000) = -Real.log (10000000 / 10001529) := by
    rw [show ((10001529 / 10000000) : ℝ) = ((10000000 / 10001529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_366_neg : (152911 / 1000000000) ≤ -Real.log (9998471 / 10000000) ∧
    -Real.log (9998471 / 10000000) ≤ (9557 / 62500000) := by
  have h := checkLog_sound (w := (1529 / 19998471)) (n := 12)
    (lo := (152911 / 1000000000)) (hi := (9557 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998471) = 1/(9998471 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_366 : Bounds (-9557 / 62500000) (-152911 / 1000000000) (Real.log (9998471 / 10000000)) := by
  have h := reflection_log_366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_367_neg : (36925791 / 500000000) ≤ -Real.log (1000000 / 1076647) ∧
    -Real.log (1000000 / 1076647) ≤ (73851583 / 1000000000) := by
  have h := checkLog_sound (w := (76647 / 2076647)) (n := 12)
    (lo := (36925791 / 500000000)) (hi := (73851583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076647 / 1000000) = 1/(1000000 / 1076647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_367 : Bounds (36925791 / 500000000) (73851583 / 1000000000) (Real.log (1076647 / 1000000)) := by
  have h := reflection_log_367_neg
  have he : Real.log (1076647 / 1000000) = -Real.log (1000000 / 1076647) := by
    rw [show ((1076647 / 1000000) : ℝ) = ((1000000 / 1076647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_368_neg : (79743669 / 1000000000) ≤ -Real.log (923353 / 1000000) ∧
    -Real.log (923353 / 1000000) ≤ (7974367 / 100000000) := by
  have h := checkLog_sound (w := (76647 / 1923353)) (n := 12)
    (lo := (79743669 / 1000000000)) (hi := (7974367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923353) = 1/(923353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_368 : Bounds (-7974367 / 100000000) (-79743669 / 1000000000) (Real.log (923353 / 1000000)) := by
  have h := reflection_log_368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_369_neg : (74041041 / 1000000000) ≤ -Real.log (1000000 / 1076851) ∧
    -Real.log (1000000 / 1076851) ≤ (37020521 / 500000000) := by
  have h := checkLog_sound (w := (76851 / 2076851)) (n := 12)
    (lo := (74041041 / 1000000000)) (hi := (37020521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076851 / 1000000) = 1/(1000000 / 1076851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_369 : Bounds (74041041 / 1000000000) (37020521 / 500000000) (Real.log (1076851 / 1000000)) := by
  have h := reflection_log_369_neg
  have he : Real.log (1076851 / 1000000) = -Real.log (1000000 / 1076851) := by
    rw [show ((1076851 / 1000000) : ℝ) = ((1000000 / 1076851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_370_neg : (79964627 / 1000000000) ≤ -Real.log (923149 / 1000000) ∧
    -Real.log (923149 / 1000000) ≤ (19991157 / 250000000) := by
  have h := checkLog_sound (w := (76851 / 1923149)) (n := 12)
    (lo := (79964627 / 1000000000)) (hi := (19991157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923149) = 1/(923149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_370 : Bounds (-19991157 / 250000000) (-79964627 / 1000000000) (Real.log (923149 / 1000000)) := by
  have h := reflection_log_370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_371_neg : (2961793 / 500000000) ≤ -Real.log (994093923799 / 1000000000000) ∧
    -Real.log (994093923799 / 1000000000000) ≤ (5923587 / 1000000000) := by
  have h := checkLog_sound (w := (5906076201 / 1994093923799)) (n := 12)
    (lo := (2961793 / 500000000)) (hi := (5923587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994093923799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994093923799) = 1/(994093923799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_371 : Bounds (-5923587 / 1000000000) (-2961793 / 500000000) (Real.log (994093923799 / 1000000000000)) := by
  have h := reflection_log_371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_372_neg : (2946043 / 500000000) ≤ -Real.log (994125237391 / 1000000000000) ∧
    -Real.log (994125237391 / 1000000000000) ≤ (5892087 / 1000000000) := by
  have h := checkLog_sound (w := (5874762609 / 1994125237391)) (n := 12)
    (lo := (2946043 / 500000000)) (hi := (5892087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994125237391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994125237391) = 1/(994125237391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_372 : Bounds (-5892087 / 1000000000) (-2946043 / 500000000) (Real.log (994125237391 / 1000000000000)) := by
  have h := reflection_log_372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_373_neg : (153595251 / 1000000000) ≤ -Real.log (15625000000 / 18219044477) ∧
    -Real.log (15625000000 / 18219044477) ≤ (38398813 / 250000000) := by
  have h := checkLog_sound (w := (2594044477 / 33844044477)) (n := 12)
    (lo := (153595251 / 1000000000)) (hi := (38398813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18219044477 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18219044477 / 15625000000) = 1/(15625000000 / 18219044477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_373 : Bounds (153595251 / 1000000000) (38398813 / 250000000) (Real.log (18219044477 / 15625000000)) := by
  have h := reflection_log_373_neg
  have he : Real.log (18219044477 / 15625000000) = -Real.log (15625000000 / 18219044477) := by
    rw [show ((18219044477 / 15625000000) : ℝ) = ((15625000000 / 18219044477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_374_neg : (38501417 / 250000000) ≤ -Real.log (500000000000 / 583248749661) ∧
    -Real.log (500000000000 / 583248749661) ≤ (154005669 / 1000000000) := by
  have h := checkLog_sound (w := (83248749661 / 1083248749661)) (n := 12)
    (lo := (38501417 / 250000000)) (hi := (154005669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583248749661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583248749661 / 500000000000) = 1/(500000000000 / 583248749661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_374 : Bounds (38501417 / 250000000) (154005669 / 1000000000) (Real.log (583248749661 / 500000000000)) := by
  have h := reflection_log_374_neg
  have he : Real.log (583248749661 / 500000000000) = -Real.log (500000000000 / 583248749661) := by
    rw [show ((583248749661 / 500000000000) : ℝ) = ((500000000000 / 583248749661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_375_neg : (1232049 / 4000000) ≤ -Real.log (125000000000 / 170089707271) ∧
    -Real.log (125000000000 / 170089707271) ≤ (308012251 / 1000000000) := by
  have h := checkLog_sound (w := (45089707271 / 295089707271)) (n := 12)
    (lo := (1232049 / 4000000)) (hi := (308012251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170089707271 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170089707271 / 125000000000) = 1/(125000000000 / 170089707271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_375 : Bounds (1232049 / 4000000) (308012251 / 1000000000) (Real.log (170089707271 / 125000000000)) := by
  have h := reflection_log_375_neg
  have he : Real.log (170089707271 / 125000000000) = -Real.log (125000000000 / 170089707271) := by
    rw [show ((170089707271 / 125000000000) : ℝ) = ((125000000000 / 170089707271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_376_neg : (154108517 / 500000000) ≤ -Real.log (125000000000 / 170124542557) ∧
    -Real.log (125000000000 / 170124542557) ≤ (61643407 / 200000000) := by
  have h := checkLog_sound (w := (45124542557 / 295124542557)) (n := 12)
    (lo := (154108517 / 500000000)) (hi := (61643407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170124542557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170124542557 / 125000000000) = 1/(125000000000 / 170124542557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_376 : Bounds (154108517 / 500000000) (61643407 / 200000000) (Real.log (170124542557 / 125000000000)) := by
  have h := reflection_log_376_neg
  have he : Real.log (170124542557 / 125000000000) = -Real.log (125000000000 / 170124542557) := by
    rw [show ((170124542557 / 125000000000) : ℝ) = ((125000000000 / 170124542557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_377_neg : (142367241 / 1000000000) ≤ -Real.log (1000 / 1153) ∧
    -Real.log (1000 / 1153) ≤ (71183621 / 500000000) := by
  have h := checkLog_sound (w := (153 / 2153)) (n := 12)
    (lo := (142367241 / 1000000000)) (hi := (71183621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153 / 1000) = 1/(1000 / 1153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_377 : Bounds (142367241 / 1000000000) (71183621 / 500000000) (Real.log (1153 / 1000)) := by
  have h := reflection_log_377_neg
  have he : Real.log (1153 / 1000) = -Real.log (1000 / 1153) := by
    rw [show ((1153 / 1000) : ℝ) = ((1000 / 1153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_378_neg : (20756823 / 125000000) ≤ -Real.log (847 / 1000) ∧
    -Real.log (847 / 1000) ≤ (33210917 / 200000000) := by
  have h := checkLog_sound (w := (153 / 1847)) (n := 12)
    (lo := (20756823 / 125000000)) (hi := (33210917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 847) = 1/(847 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_378 : Bounds (-33210917 / 200000000) (-20756823 / 125000000) (Real.log (847 / 1000)) := by
  have h := reflection_log_378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_379_neg : (38247 / 250000000) ≤ -Real.log (1000000 / 1000153) ∧
    -Real.log (1000000 / 1000153) ≤ (152989 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 2000153)) (n := 12)
    (lo := (38247 / 250000000)) (hi := (152989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000153 / 1000000) = 1/(1000000 / 1000153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_379 : Bounds (38247 / 250000000) (152989 / 1000000000) (Real.log (1000153 / 1000000)) := by
  have h := reflection_log_379_neg
  have he : Real.log (1000153 / 1000000) = -Real.log (1000000 / 1000153) := by
    rw [show ((1000153 / 1000000) : ℝ) = ((1000000 / 1000153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_380_neg : (153011 / 1000000000) ≤ -Real.log (999847 / 1000000) ∧
    -Real.log (999847 / 1000000) ≤ (38253 / 250000000) := by
  have h := checkLog_sound (w := (153 / 1999847)) (n := 12)
    (lo := (153011 / 1000000000)) (hi := (38253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999847) = 1/(999847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_380 : Bounds (-38253 / 250000000) (-153011 / 1000000000) (Real.log (999847 / 1000000)) := by
  have h := reflection_log_380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_381_neg : (1477979 / 20000000) ≤ -Real.log (500000 / 538349) ∧
    -Real.log (500000 / 538349) ≤ (73898951 / 1000000000) := by
  have h := checkLog_sound (w := (38349 / 1038349)) (n := 12)
    (lo := (1477979 / 20000000)) (hi := (73898951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538349 / 500000) = 1/(500000 / 538349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_381 : Bounds (1477979 / 20000000) (73898951 / 1000000000) (Real.log (538349 / 500000)) := by
  have h := reflection_log_381_neg
  have he : Real.log (538349 / 500000) = -Real.log (500000 / 538349) := by
    rw [show ((538349 / 500000) : ℝ) = ((500000 / 538349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_382_neg : (9974863 / 125000000) ≤ -Real.log (461651 / 500000) ∧
    -Real.log (461651 / 500000) ≤ (15959781 / 200000000) := by
  have h := checkLog_sound (w := (38349 / 961651)) (n := 12)
    (lo := (9974863 / 125000000)) (hi := (15959781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461651) = 1/(461651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_382 : Bounds (-15959781 / 200000000) (-9974863 / 125000000) (Real.log (461651 / 500000)) := by
  have h := reflection_log_382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_383_neg : (185221 / 2500000) ≤ -Real.log (500000 / 538451) ∧
    -Real.log (500000 / 538451) ≤ (74088401 / 1000000000) := by
  have h := checkLog_sound (w := (38451 / 1038451)) (n := 12)
    (lo := (185221 / 2500000)) (hi := (74088401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538451 / 500000) = 1/(500000 / 538451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_383 : Bounds (185221 / 2500000) (74088401 / 1000000000) (Real.log (538451 / 500000)) := by
  have h := reflection_log_383_neg
  have he : Real.log (538451 / 500000) = -Real.log (500000 / 538451) := by
    rw [show ((538451 / 500000) : ℝ) = ((500000 / 538451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
