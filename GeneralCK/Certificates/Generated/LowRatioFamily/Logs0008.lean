import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_512_neg : (1492593 / 250000000) ≤ -Real.log (994047414591 / 1000000000000) ∧
    -Real.log (994047414591 / 1000000000000) ≤ (5970373 / 1000000000) := by
  have h := checkLog_sound (w := (5952585409 / 1994047414591)) (n := 12)
    (lo := (1492593 / 250000000)) (hi := (5970373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994047414591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994047414591) = 1/(994047414591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_512 : Bounds (-5970373 / 1000000000) (-1492593 / 250000000) (Real.log (994047414591 / 1000000000000)) := by
  have h := reflection_log_512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_513_neg : (154613271 / 1000000000) ≤ -Real.log (12500000000 / 14590081021) ∧
    -Real.log (12500000000 / 14590081021) ≤ (19326659 / 125000000) := by
  have h := checkLog_sound (w := (2090081021 / 27090081021)) (n := 12)
    (lo := (154613271 / 1000000000)) (hi := (19326659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14590081021 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14590081021 / 12500000000) = 1/(12500000000 / 14590081021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_513 : Bounds (154613271 / 1000000000) (19326659 / 125000000) (Real.log (14590081021 / 12500000000)) := by
  have h := reflection_log_513_neg
  have he : Real.log (14590081021 / 12500000000) = -Real.log (12500000000 / 14590081021) := by
    rw [show ((14590081021 / 12500000000) : ℝ) = ((12500000000 / 14590081021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_514_neg : (155025733 / 1000000000) ≤ -Real.log (500000000000 / 583844004501) ∧
    -Real.log (500000000000 / 583844004501) ≤ (77512867 / 500000000) := by
  have h := checkLog_sound (w := (83844004501 / 1083844004501)) (n := 12)
    (lo := (155025733 / 1000000000)) (hi := (77512867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583844004501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583844004501 / 500000000000) = 1/(500000000000 / 583844004501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_514 : Bounds (155025733 / 1000000000) (77512867 / 500000000) (Real.log (583844004501 / 500000000000)) := by
  have h := reflection_log_514_neg
  have he : Real.log (583844004501 / 500000000000) = -Real.log (500000000000 / 583844004501) := by
    rw [show ((583844004501 / 500000000000) : ℝ) = ((500000000000 / 583844004501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_515_neg : (310060383 / 1000000000) ≤ -Real.log (125000000000 / 170438430631) ∧
    -Real.log (125000000000 / 170438430631) ≤ (9689387 / 31250000) := by
  have h := checkLog_sound (w := (45438430631 / 295438430631)) (n := 12)
    (lo := (310060383 / 1000000000)) (hi := (9689387 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170438430631 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170438430631 / 125000000000) = 1/(125000000000 / 170438430631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_515 : Bounds (310060383 / 1000000000) (9689387 / 31250000) (Real.log (170438430631 / 125000000000)) := by
  have h := reflection_log_515_neg
  have he : Real.log (170438430631 / 125000000000) = -Real.log (125000000000 / 170438430631) := by
    rw [show ((170438430631 / 125000000000) : ℝ) = ((125000000000 / 170438430631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_516_neg : (19391577 / 62500000) ≤ -Real.log (7812500000 / 10654584269) ∧
    -Real.log (7812500000 / 10654584269) ≤ (310265233 / 1000000000) := by
  have h := checkLog_sound (w := (2842084269 / 18467084269)) (n := 12)
    (lo := (19391577 / 62500000)) (hi := (310265233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10654584269 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10654584269 / 7812500000) = 1/(7812500000 / 10654584269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_516 : Bounds (19391577 / 62500000) (310265233 / 1000000000) (Real.log (10654584269 / 7812500000)) := by
  have h := reflection_log_516_neg
  have he : Real.log (10654584269 / 7812500000) = -Real.log (7812500000 / 10654584269) := by
    rw [show ((10654584269 / 7812500000) : ℝ) = ((7812500000 / 10654584269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_517_neg : (17904271 / 125000000) ≤ -Real.log (500 / 577) ∧
    -Real.log (500 / 577) ≤ (143234169 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 1077)) (n := 12)
    (lo := (17904271 / 125000000)) (hi := (143234169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 500) = 1/(500 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_517 : Bounds (17904271 / 125000000) (143234169 / 1000000000) (Real.log (577 / 500)) := by
  have h := reflection_log_517_neg
  have he : Real.log (577 / 500) = -Real.log (500 / 577) := by
    rw [show ((577 / 500) : ℝ) = ((500 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_518_neg : (167235919 / 1000000000) ≤ -Real.log (423 / 500) ∧
    -Real.log (423 / 500) ≤ (2090449 / 12500000) := by
  have h := checkLog_sound (w := (77 / 923)) (n := 12)
    (lo := (167235919 / 1000000000)) (hi := (2090449 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 423) = 1/(423 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_518 : Bounds (-2090449 / 12500000) (-167235919 / 1000000000) (Real.log (423 / 500)) := by
  have h := reflection_log_518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_519_neg : (38497 / 250000000) ≤ -Real.log (500000 / 500077) ∧
    -Real.log (500000 / 500077) ≤ (153989 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 1000077)) (n := 12)
    (lo := (38497 / 250000000)) (hi := (153989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500077 / 500000) = 1/(500000 / 500077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_519 : Bounds (38497 / 250000000) (153989 / 1000000000) (Real.log (500077 / 500000)) := by
  have h := reflection_log_519_neg
  have he : Real.log (500077 / 500000) = -Real.log (500000 / 500077) := by
    rw [show ((500077 / 500000) : ℝ) = ((500000 / 500077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_520_neg : (154011 / 1000000000) ≤ -Real.log (499923 / 500000) ∧
    -Real.log (499923 / 500000) ≤ (38503 / 250000000) := by
  have h := checkLog_sound (w := (77 / 999923)) (n := 12)
    (lo := (154011 / 1000000000)) (hi := (38503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499923) = 1/(499923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_520 : Bounds (-38503 / 250000000) (-154011 / 1000000000) (Real.log (499923 / 500000)) := by
  have h := reflection_log_520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_521_neg : (14873759 / 200000000) ≤ -Real.log (250000 / 269301) ∧
    -Real.log (250000 / 269301) ≤ (18592199 / 250000000) := by
  have h := checkLog_sound (w := (19301 / 519301)) (n := 12)
    (lo := (14873759 / 200000000)) (hi := (18592199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269301 / 250000) = 1/(250000 / 269301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_521 : Bounds (14873759 / 200000000) (18592199 / 250000000) (Real.log (269301 / 250000)) := by
  have h := reflection_log_521_neg
  have he : Real.log (269301 / 250000) = -Real.log (250000 / 269301) := by
    rw [show ((269301 / 250000) : ℝ) = ((250000 / 269301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_522_neg : (80347087 / 1000000000) ≤ -Real.log (230699 / 250000) ∧
    -Real.log (230699 / 250000) ≤ (5021693 / 62500000) := by
  have h := checkLog_sound (w := (19301 / 480699)) (n := 12)
    (lo := (80347087 / 1000000000)) (hi := (5021693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230699) = 1/(230699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_522 : Bounds (-5021693 / 62500000) (-80347087 / 1000000000) (Real.log (230699 / 250000)) := by
  have h := reflection_log_522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_523_neg : (18639771 / 250000000) ≤ -Real.log (1000000 / 1077409) ∧
    -Real.log (1000000 / 1077409) ≤ (14911817 / 200000000) := by
  have h := checkLog_sound (w := (77409 / 2077409)) (n := 12)
    (lo := (18639771 / 250000000)) (hi := (14911817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077409 / 1000000) = 1/(1000000 / 1077409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_523 : Bounds (18639771 / 250000000) (14911817 / 200000000) (Real.log (1077409 / 1000000)) := by
  have h := reflection_log_523_neg
  have he : Real.log (1077409 / 1000000) = -Real.log (1000000 / 1077409) := by
    rw [show ((1077409 / 1000000) : ℝ) = ((1000000 / 1077409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_524_neg : (40284631 / 500000000) ≤ -Real.log (922591 / 1000000) ∧
    -Real.log (922591 / 1000000) ≤ (80569263 / 1000000000) := by
  have h := checkLog_sound (w := (77409 / 1922591)) (n := 12)
    (lo := (40284631 / 500000000)) (hi := (80569263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922591) = 1/(922591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_524 : Bounds (-80569263 / 1000000000) (-40284631 / 500000000) (Real.log (922591 / 1000000)) := by
  have h := reflection_log_524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_525_neg : (3005089 / 500000000) ≤ -Real.log (994007846719 / 1000000000000) ∧
    -Real.log (994007846719 / 1000000000000) ≤ (6010179 / 1000000000) := by
  have h := checkLog_sound (w := (5992153281 / 1994007846719)) (n := 12)
    (lo := (3005089 / 500000000)) (hi := (6010179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994007846719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994007846719) = 1/(994007846719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_525 : Bounds (-6010179 / 1000000000) (-3005089 / 500000000) (Real.log (994007846719 / 1000000000000)) := by
  have h := reflection_log_525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_526_neg : (1494573 / 250000000) ≤ -Real.log (62127471399 / 62500000000) ∧
    -Real.log (62127471399 / 62500000000) ≤ (5978293 / 1000000000) := by
  have h := checkLog_sound (w := (372528601 / 124627471399)) (n := 12)
    (lo := (1494573 / 250000000)) (hi := (5978293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62127471399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62127471399) = 1/(62127471399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_526 : Bounds (-5978293 / 1000000000) (-1494573 / 250000000) (Real.log (62127471399 / 62500000000)) := by
  have h := reflection_log_526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_527_neg : (77357941 / 500000000) ≤ -Real.log (100000000000 / 116732625629) ∧
    -Real.log (100000000000 / 116732625629) ≤ (154715883 / 1000000000) := by
  have h := checkLog_sound (w := (16732625629 / 216732625629)) (n := 12)
    (lo := (77357941 / 500000000)) (hi := (154715883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116732625629 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116732625629 / 100000000000) = 1/(100000000000 / 116732625629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_527 : Bounds (77357941 / 500000000) (154715883 / 1000000000) (Real.log (116732625629 / 100000000000)) := by
  have h := reflection_log_527_neg
  have he : Real.log (116732625629 / 100000000000) = -Real.log (100000000000 / 116732625629) := by
    rw [show ((116732625629 / 100000000000) : ℝ) = ((100000000000 / 116732625629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_528_neg : (155128347 / 1000000000) ≤ -Real.log (250000000000 / 291951959211) ∧
    -Real.log (250000000000 / 291951959211) ≤ (38782087 / 250000000) := by
  have h := checkLog_sound (w := (41951959211 / 541951959211)) (n := 12)
    (lo := (155128347 / 1000000000)) (hi := (38782087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291951959211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291951959211 / 250000000000) = 1/(250000000000 / 291951959211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_528 : Bounds (155128347 / 1000000000) (38782087 / 250000000) (Real.log (291951959211 / 250000000000)) := by
  have h := reflection_log_528_neg
  have he : Real.log (291951959211 / 250000000000) = -Real.log (250000000000 / 291951959211) := by
    rw [show ((291951959211 / 250000000000) : ℝ) = ((250000000000 / 291951959211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_529_neg : (19391577 / 62500000) ≤ -Real.log (100000000000 / 136378678643) ∧
    -Real.log (100000000000 / 136378678643) ≤ (310265233 / 1000000000) := by
  have h := checkLog_sound (w := (36378678643 / 236378678643)) (n := 12)
    (lo := (19391577 / 62500000)) (hi := (310265233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136378678643 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136378678643 / 100000000000) = 1/(100000000000 / 136378678643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_529 : Bounds (19391577 / 62500000) (310265233 / 1000000000) (Real.log (136378678643 / 100000000000)) := by
  have h := reflection_log_529_neg
  have he : Real.log (136378678643 / 100000000000) = -Real.log (100000000000 / 136378678643) := by
    rw [show ((136378678643 / 100000000000) : ℝ) = ((100000000000 / 136378678643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_530_neg : (310470087 / 1000000000) ≤ -Real.log (500000000000 / 682033096927) ∧
    -Real.log (500000000000 / 682033096927) ≤ (38808761 / 125000000) := by
  have h := checkLog_sound (w := (182033096927 / 1182033096927)) (n := 12)
    (lo := (310470087 / 1000000000)) (hi := (38808761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682033096927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682033096927 / 500000000000) = 1/(500000000000 / 682033096927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_530 : Bounds (310470087 / 1000000000) (38808761 / 125000000) (Real.log (682033096927 / 500000000000)) := by
  have h := reflection_log_530_neg
  have he : Real.log (682033096927 / 500000000000) = -Real.log (500000000000 / 682033096927) := by
    rw [show ((682033096927 / 500000000000) : ℝ) = ((500000000000 / 682033096927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_531_neg : (143320819 / 1000000000) ≤ -Real.log (10000 / 11541) ∧
    -Real.log (10000 / 11541) ≤ (7166041 / 50000000) := by
  have h := checkLog_sound (w := (1541 / 21541)) (n := 12)
    (lo := (143320819 / 1000000000)) (hi := (7166041 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11541 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11541 / 10000) = 1/(10000 / 11541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_531 : Bounds (143320819 / 1000000000) (7166041 / 50000000) (Real.log (11541 / 10000)) := by
  have h := reflection_log_531_neg
  have he : Real.log (11541 / 10000) = -Real.log (10000 / 11541) := by
    rw [show ((11541 / 10000) : ℝ) = ((10000 / 11541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_532_neg : (167354129 / 1000000000) ≤ -Real.log (8459 / 10000) ∧
    -Real.log (8459 / 10000) ≤ (16735413 / 100000000) := by
  have h := checkLog_sound (w := (1541 / 18459)) (n := 12)
    (lo := (167354129 / 1000000000)) (hi := (16735413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8459) = 1/(8459 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_532 : Bounds (-16735413 / 100000000) (-167354129 / 1000000000) (Real.log (8459 / 10000)) := by
  have h := reflection_log_532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_533_neg : (19261 / 125000000) ≤ -Real.log (10000000 / 10001541) ∧
    -Real.log (10000000 / 10001541) ≤ (154089 / 1000000000) := by
  have h := checkLog_sound (w := (1541 / 20001541)) (n := 12)
    (lo := (19261 / 125000000)) (hi := (154089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001541 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001541 / 10000000) = 1/(10000000 / 10001541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_533 : Bounds (19261 / 125000000) (154089 / 1000000000) (Real.log (10001541 / 10000000)) := by
  have h := reflection_log_533_neg
  have he : Real.log (10001541 / 10000000) = -Real.log (10000000 / 10001541) := by
    rw [show ((10001541 / 10000000) : ℝ) = ((10000000 / 10001541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_534_neg : (154111 / 1000000000) ≤ -Real.log (9998459 / 10000000) ∧
    -Real.log (9998459 / 10000000) ≤ (301 / 1953125) := by
  have h := checkLog_sound (w := (1541 / 19998459)) (n := 12)
    (lo := (154111 / 1000000000)) (hi := (301 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998459) = 1/(9998459 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_534 : Bounds (-301 / 1953125) (-154111 / 1000000000) (Real.log (9998459 / 10000000)) := by
  have h := reflection_log_534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_535_neg : (7441521 / 100000000) ≤ -Real.log (500000 / 538627) ∧
    -Real.log (500000 / 538627) ≤ (74415211 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 1038627)) (n := 12)
    (lo := (7441521 / 100000000)) (hi := (74415211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538627 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538627 / 500000) = 1/(500000 / 538627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_535 : Bounds (7441521 / 100000000) (74415211 / 1000000000) (Real.log (538627 / 500000)) := by
  have h := reflection_log_535_neg
  have he : Real.log (538627 / 500000) = -Real.log (500000 / 538627) := by
    rw [show ((538627 / 500000) : ℝ) = ((500000 / 538627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_536_neg : (80401271 / 1000000000) ≤ -Real.log (461373 / 500000) ∧
    -Real.log (461373 / 500000) ≤ (10050159 / 125000000) := by
  have h := checkLog_sound (w := (38627 / 961373)) (n := 12)
    (lo := (80401271 / 1000000000)) (hi := (10050159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461373) = 1/(461373 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_536 : Bounds (-10050159 / 125000000) (-80401271 / 1000000000) (Real.log (461373 / 500000)) := by
  have h := reflection_log_536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_537_neg : (74605491 / 1000000000) ≤ -Real.log (1000000 / 1077459) ∧
    -Real.log (1000000 / 1077459) ≤ (18651373 / 250000000) := by
  have h := checkLog_sound (w := (77459 / 2077459)) (n := 12)
    (lo := (74605491 / 1000000000)) (hi := (18651373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077459 / 1000000) = 1/(1000000 / 1077459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_537 : Bounds (74605491 / 1000000000) (18651373 / 250000000) (Real.log (1077459 / 1000000)) := by
  have h := reflection_log_537_neg
  have he : Real.log (1077459 / 1000000) = -Real.log (1000000 / 1077459) := by
    rw [show ((1077459 / 1000000) : ℝ) = ((1000000 / 1077459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_538_neg : (80623459 / 1000000000) ≤ -Real.log (922541 / 1000000) ∧
    -Real.log (922541 / 1000000) ≤ (4031173 / 50000000) := by
  have h := checkLog_sound (w := (77459 / 1922541)) (n := 12)
    (lo := (80623459 / 1000000000)) (hi := (4031173 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922541) = 1/(922541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_538 : Bounds (-4031173 / 50000000) (-80623459 / 1000000000) (Real.log (922541 / 1000000)) := by
  have h := reflection_log_538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_539_neg : (376123 / 62500000) ≤ -Real.log (994000103319 / 1000000000000) ∧
    -Real.log (994000103319 / 1000000000000) ≤ (6017969 / 1000000000) := by
  have h := checkLog_sound (w := (5999896681 / 1994000103319)) (n := 12)
    (lo := (376123 / 62500000)) (hi := (6017969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994000103319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994000103319) = 1/(994000103319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_539 : Bounds (-6017969 / 1000000000) (-376123 / 62500000) (Real.log (994000103319 / 1000000000000)) := by
  have h := reflection_log_539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_540_neg : (5986061 / 1000000000) ≤ -Real.log (248507954871 / 250000000000) ∧
    -Real.log (248507954871 / 250000000000) ≤ (2993031 / 500000000) := by
  have h := checkLog_sound (w := (1492045129 / 498507954871)) (n := 12)
    (lo := (5986061 / 1000000000)) (hi := (2993031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248507954871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248507954871) = 1/(248507954871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_540 : Bounds (-2993031 / 500000000) (-5986061 / 1000000000) (Real.log (248507954871 / 250000000000)) := by
  have h := reflection_log_540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_541_neg : (77408241 / 500000000) ≤ -Real.log (100000000000 / 116744369523) ∧
    -Real.log (100000000000 / 116744369523) ≤ (154816483 / 1000000000) := by
  have h := checkLog_sound (w := (16744369523 / 216744369523)) (n := 12)
    (lo := (77408241 / 500000000)) (hi := (154816483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116744369523 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116744369523 / 100000000000) = 1/(100000000000 / 116744369523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_541 : Bounds (77408241 / 500000000) (154816483 / 1000000000) (Real.log (116744369523 / 100000000000)) := by
  have h := reflection_log_541_neg
  have he : Real.log (116744369523 / 100000000000) = -Real.log (100000000000 / 116744369523) := by
    rw [show ((116744369523 / 100000000000) : ℝ) = ((100000000000 / 116744369523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_542_neg : (3104579 / 20000000) ≤ -Real.log (500000000000 / 583962663991) ∧
    -Real.log (500000000000 / 583962663991) ≤ (155228951 / 1000000000) := by
  have h := checkLog_sound (w := (83962663991 / 1083962663991)) (n := 12)
    (lo := (3104579 / 20000000)) (hi := (155228951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583962663991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583962663991 / 500000000000) = 1/(500000000000 / 583962663991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_542 : Bounds (3104579 / 20000000) (155228951 / 1000000000) (Real.log (583962663991 / 500000000000)) := by
  have h := reflection_log_542_neg
  have he : Real.log (583962663991 / 500000000000) = -Real.log (500000000000 / 583962663991) := by
    rw [show ((583962663991 / 500000000000) : ℝ) = ((500000000000 / 583962663991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_543_neg : (310470087 / 1000000000) ≤ -Real.log (250000000000 / 341016548463) ∧
    -Real.log (250000000000 / 341016548463) ≤ (38808761 / 125000000) := by
  have h := checkLog_sound (w := (91016548463 / 591016548463)) (n := 12)
    (lo := (310470087 / 1000000000)) (hi := (38808761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341016548463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341016548463 / 250000000000) = 1/(250000000000 / 341016548463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_543 : Bounds (310470087 / 1000000000) (38808761 / 125000000) (Real.log (341016548463 / 250000000000)) := by
  have h := reflection_log_543_neg
  have he : Real.log (341016548463 / 250000000000) = -Real.log (250000000000 / 341016548463) := by
    rw [show ((341016548463 / 250000000000) : ℝ) = ((250000000000 / 341016548463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_544_neg : (310674949 / 1000000000) ≤ -Real.log (500000000000 / 682172833669) ∧
    -Real.log (500000000000 / 682172833669) ≤ (6213499 / 20000000) := by
  have h := checkLog_sound (w := (182172833669 / 1182172833669)) (n := 12)
    (lo := (310674949 / 1000000000)) (hi := (6213499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682172833669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682172833669 / 500000000000) = 1/(500000000000 / 682172833669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_544 : Bounds (310674949 / 1000000000) (6213499 / 20000000) (Real.log (682172833669 / 500000000000)) := by
  have h := reflection_log_544_neg
  have he : Real.log (682172833669 / 500000000000) = -Real.log (500000000000 / 682172833669) := by
    rw [show ((682172833669 / 500000000000) : ℝ) = ((500000000000 / 682172833669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_545_neg : (143407463 / 1000000000) ≤ -Real.log (5000 / 5771) ∧
    -Real.log (5000 / 5771) ≤ (17925933 / 125000000) := by
  have h := checkLog_sound (w := (771 / 10771)) (n := 12)
    (lo := (143407463 / 1000000000)) (hi := (17925933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5771 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5771 / 5000) = 1/(5000 / 5771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_545 : Bounds (143407463 / 1000000000) (17925933 / 125000000) (Real.log (5771 / 5000)) := by
  have h := reflection_log_545_neg
  have he : Real.log (5771 / 5000) = -Real.log (5000 / 5771) := by
    rw [show ((5771 / 5000) : ℝ) = ((5000 / 5771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_546_neg : (167472353 / 1000000000) ≤ -Real.log (4229 / 5000) ∧
    -Real.log (4229 / 5000) ≤ (83736177 / 500000000) := by
  have h := checkLog_sound (w := (771 / 9229)) (n := 12)
    (lo := (167472353 / 1000000000)) (hi := (83736177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4229) = 1/(4229 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_546 : Bounds (-83736177 / 500000000) (-167472353 / 1000000000) (Real.log (4229 / 5000)) := by
  have h := reflection_log_546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_547_neg : (38547 / 250000000) ≤ -Real.log (5000000 / 5000771) ∧
    -Real.log (5000000 / 5000771) ≤ (154189 / 1000000000) := by
  have h := checkLog_sound (w := (771 / 10000771)) (n := 12)
    (lo := (38547 / 250000000)) (hi := (154189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000771 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000771 / 5000000) = 1/(5000000 / 5000771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_547 : Bounds (38547 / 250000000) (154189 / 1000000000) (Real.log (5000771 / 5000000)) := by
  have h := reflection_log_547_neg
  have he : Real.log (5000771 / 5000000) = -Real.log (5000000 / 5000771) := by
    rw [show ((5000771 / 5000000) : ℝ) = ((5000000 / 5000771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_548_neg : (154211 / 1000000000) ≤ -Real.log (4999229 / 5000000) ∧
    -Real.log (4999229 / 5000000) ≤ (38553 / 250000000) := by
  have h := checkLog_sound (w := (771 / 9999229)) (n := 12)
    (lo := (154211 / 1000000000)) (hi := (38553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999229) = 1/(4999229 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_548 : Bounds (-38553 / 250000000) (-154211 / 1000000000) (Real.log (4999229 / 5000000)) := by
  have h := reflection_log_548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_549_neg : (9307819 / 125000000) ≤ -Real.log (200000 / 215461) ∧
    -Real.log (200000 / 215461) ≤ (74462553 / 1000000000) := by
  have h := checkLog_sound (w := (15461 / 415461)) (n := 12)
    (lo := (9307819 / 125000000)) (hi := (74462553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215461 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215461 / 200000) = 1/(200000 / 215461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_549 : Bounds (9307819 / 125000000) (74462553 / 1000000000) (Real.log (215461 / 200000)) := by
  have h := reflection_log_549_neg
  have he : Real.log (215461 / 200000) = -Real.log (200000 / 215461) := by
    rw [show ((215461 / 200000) : ℝ) = ((200000 / 215461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_550_neg : (80456543 / 1000000000) ≤ -Real.log (184539 / 200000) ∧
    -Real.log (184539 / 200000) ≤ (2514267 / 31250000) := by
  have h := checkLog_sound (w := (15461 / 384539)) (n := 12)
    (lo := (80456543 / 1000000000)) (hi := (2514267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184539) = 1/(184539 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_550 : Bounds (-2514267 / 31250000) (-80456543 / 1000000000) (Real.log (184539 / 200000)) := by
  have h := reflection_log_550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_551_neg : (74652823 / 1000000000) ≤ -Real.log (100000 / 107751) ∧
    -Real.log (100000 / 107751) ≤ (9331603 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 207751)) (n := 12)
    (lo := (74652823 / 1000000000)) (hi := (9331603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107751 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107751 / 100000) = 1/(100000 / 107751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_551 : Bounds (74652823 / 1000000000) (9331603 / 125000000) (Real.log (107751 / 100000)) := by
  have h := reflection_log_551_neg
  have he : Real.log (107751 / 100000) = -Real.log (100000 / 107751) := by
    rw [show ((107751 / 100000) : ℝ) = ((100000 / 107751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_552_neg : (80678743 / 1000000000) ≤ -Real.log (92249 / 100000) ∧
    -Real.log (92249 / 100000) ≤ (10084843 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 192249)) (n := 12)
    (lo := (80678743 / 1000000000)) (hi := (10084843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92249) = 1/(92249 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_552 : Bounds (-10084843 / 125000000) (-80678743 / 1000000000) (Real.log (92249 / 100000)) := by
  have h := reflection_log_552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_553_neg : (6025919 / 1000000000) ≤ -Real.log (9939921999 / 10000000000) ∧
    -Real.log (9939921999 / 10000000000) ≤ (18831 / 3125000) := by
  have h := checkLog_sound (w := (60078001 / 19939921999)) (n := 12)
    (lo := (6025919 / 1000000000)) (hi := (18831 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9939921999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9939921999) = 1/(9939921999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_553 : Bounds (-18831 / 3125000) (-6025919 / 1000000000) (Real.log (9939921999 / 10000000000)) := by
  have h := reflection_log_553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_554_neg : (5993991 / 1000000000) ≤ -Real.log (39760957479 / 40000000000) ∧
    -Real.log (39760957479 / 40000000000) ≤ (749249 / 125000000) := by
  have h := checkLog_sound (w := (239042521 / 79760957479)) (n := 12)
    (lo := (5993991 / 1000000000)) (hi := (749249 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39760957479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39760957479) = 1/(39760957479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_554 : Bounds (-749249 / 125000000) (-5993991 / 1000000000) (Real.log (39760957479 / 40000000000)) := by
  have h := reflection_log_554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_555_neg : (30983819 / 200000000) ≤ -Real.log (500000000000 / 583781748031) ∧
    -Real.log (500000000000 / 583781748031) ≤ (19364887 / 125000000) := by
  have h := checkLog_sound (w := (83781748031 / 1083781748031)) (n := 12)
    (lo := (30983819 / 200000000)) (hi := (19364887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583781748031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583781748031 / 500000000000) = 1/(500000000000 / 583781748031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_555 : Bounds (30983819 / 200000000) (19364887 / 125000000) (Real.log (583781748031 / 500000000000)) := by
  have h := reflection_log_555_neg
  have he : Real.log (583781748031 / 500000000000) = -Real.log (500000000000 / 583781748031) := by
    rw [show ((583781748031 / 500000000000) : ℝ) = ((500000000000 / 583781748031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_556_neg : (77665783 / 500000000) ≤ -Real.log (500000000000 / 584022591031) ∧
    -Real.log (500000000000 / 584022591031) ≤ (155331567 / 1000000000) := by
  have h := checkLog_sound (w := (84022591031 / 1084022591031)) (n := 12)
    (lo := (77665783 / 500000000)) (hi := (155331567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584022591031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584022591031 / 500000000000) = 1/(500000000000 / 584022591031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_556 : Bounds (77665783 / 500000000) (155331567 / 1000000000) (Real.log (584022591031 / 500000000000)) := by
  have h := reflection_log_556_neg
  have he : Real.log (584022591031 / 500000000000) = -Real.log (500000000000 / 584022591031) := by
    rw [show ((584022591031 / 500000000000) : ℝ) = ((500000000000 / 584022591031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_557_neg : (310674949 / 1000000000) ≤ -Real.log (125000000000 / 170543208417) ∧
    -Real.log (125000000000 / 170543208417) ≤ (6213499 / 20000000) := by
  have h := checkLog_sound (w := (45543208417 / 295543208417)) (n := 12)
    (lo := (310674949 / 1000000000)) (hi := (6213499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170543208417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170543208417 / 125000000000) = 1/(125000000000 / 170543208417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_557 : Bounds (310674949 / 1000000000) (6213499 / 20000000) (Real.log (170543208417 / 125000000000)) := by
  have h := reflection_log_557_neg
  have he : Real.log (170543208417 / 125000000000) = -Real.log (125000000000 / 170543208417) := by
    rw [show ((170543208417 / 125000000000) : ℝ) = ((125000000000 / 170543208417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_558_neg : (310879817 / 1000000000) ≤ -Real.log (500000000000 / 682312603453) ∧
    -Real.log (500000000000 / 682312603453) ≤ (155439909 / 500000000) := by
  have h := checkLog_sound (w := (182312603453 / 1182312603453)) (n := 12)
    (lo := (310879817 / 1000000000)) (hi := (155439909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682312603453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682312603453 / 500000000000) = 1/(500000000000 / 682312603453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_558 : Bounds (310879817 / 1000000000) (155439909 / 500000000) (Real.log (682312603453 / 500000000000)) := by
  have h := reflection_log_558_neg
  have he : Real.log (682312603453 / 500000000000) = -Real.log (500000000000 / 682312603453) := by
    rw [show ((682312603453 / 500000000000) : ℝ) = ((500000000000 / 682312603453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_559_neg : (143494099 / 1000000000) ≤ -Real.log (10000 / 11543) ∧
    -Real.log (10000 / 11543) ≤ (1434941 / 10000000) := by
  have h := checkLog_sound (w := (1543 / 21543)) (n := 12)
    (lo := (143494099 / 1000000000)) (hi := (1434941 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11543 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11543 / 10000) = 1/(10000 / 11543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_559 : Bounds (143494099 / 1000000000) (1434941 / 10000000) (Real.log (11543 / 10000)) := by
  have h := reflection_log_559_neg
  have he : Real.log (11543 / 10000) = -Real.log (10000 / 11543) := by
    rw [show ((11543 / 10000) : ℝ) = ((10000 / 11543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_560_neg : (2618603 / 15625000) ≤ -Real.log (8457 / 10000) ∧
    -Real.log (8457 / 10000) ≤ (167590593 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 18457)) (n := 12)
    (lo := (2618603 / 15625000)) (hi := (167590593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8457) = 1/(8457 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_560 : Bounds (-167590593 / 1000000000) (-2618603 / 15625000) (Real.log (8457 / 10000)) := by
  have h := reflection_log_560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_561_neg : (9643 / 62500000) ≤ -Real.log (10000000 / 10001543) ∧
    -Real.log (10000000 / 10001543) ≤ (154289 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 20001543)) (n := 12)
    (lo := (9643 / 62500000)) (hi := (154289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001543 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001543 / 10000000) = 1/(10000000 / 10001543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_561 : Bounds (9643 / 62500000) (154289 / 1000000000) (Real.log (10001543 / 10000000)) := by
  have h := reflection_log_561_neg
  have he : Real.log (10001543 / 10000000) = -Real.log (10000000 / 10001543) := by
    rw [show ((10001543 / 10000000) : ℝ) = ((10000000 / 10001543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_562_neg : (154311 / 1000000000) ≤ -Real.log (9998457 / 10000000) ∧
    -Real.log (9998457 / 10000000) ≤ (19289 / 125000000) := by
  have h := checkLog_sound (w := (1543 / 19998457)) (n := 12)
    (lo := (154311 / 1000000000)) (hi := (19289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998457) = 1/(9998457 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_562 : Bounds (-19289 / 125000000) (-154311 / 1000000000) (Real.log (9998457 / 10000000)) := by
  have h := reflection_log_562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_563_neg : (74509891 / 1000000000) ≤ -Real.log (250000 / 269339) ∧
    -Real.log (250000 / 269339) ≤ (18627473 / 250000000) := by
  have h := checkLog_sound (w := (19339 / 519339)) (n := 12)
    (lo := (74509891 / 1000000000)) (hi := (18627473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269339 / 250000) = 1/(250000 / 269339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_563 : Bounds (74509891 / 1000000000) (18627473 / 250000000) (Real.log (269339 / 250000)) := by
  have h := reflection_log_563_neg
  have he : Real.log (269339 / 250000) = -Real.log (250000 / 269339) := by
    rw [show ((269339 / 250000) : ℝ) = ((250000 / 269339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_564_neg : (80511817 / 1000000000) ≤ -Real.log (230661 / 250000) ∧
    -Real.log (230661 / 250000) ≤ (40255909 / 500000000) := by
  have h := checkLog_sound (w := (19339 / 480661)) (n := 12)
    (lo := (80511817 / 1000000000)) (hi := (40255909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230661) = 1/(230661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_564 : Bounds (-40255909 / 500000000) (-80511817 / 1000000000) (Real.log (230661 / 250000)) := by
  have h := reflection_log_564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_565_neg : (74700153 / 1000000000) ≤ -Real.log (1000000 / 1077561) ∧
    -Real.log (1000000 / 1077561) ≤ (37350077 / 500000000) := by
  have h := checkLog_sound (w := (77561 / 2077561)) (n := 12)
    (lo := (74700153 / 1000000000)) (hi := (37350077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077561 / 1000000) = 1/(1000000 / 1077561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_565 : Bounds (74700153 / 1000000000) (37350077 / 500000000) (Real.log (1077561 / 1000000)) := by
  have h := reflection_log_565_neg
  have he : Real.log (1077561 / 1000000) = -Real.log (1000000 / 1077561) := by
    rw [show ((1077561 / 1000000) : ℝ) = ((1000000 / 1077561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_566_neg : (80734029 / 1000000000) ≤ -Real.log (922439 / 1000000) ∧
    -Real.log (922439 / 1000000) ≤ (8073403 / 100000000) := by
  have h := checkLog_sound (w := (77561 / 1922439)) (n := 12)
    (lo := (80734029 / 1000000000)) (hi := (8073403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922439) = 1/(922439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_566 : Bounds (-8073403 / 100000000) (-80734029 / 1000000000) (Real.log (922439 / 1000000)) := by
  have h := reflection_log_566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_567_neg : (48271 / 8000000) ≤ -Real.log (993984291279 / 1000000000000) ∧
    -Real.log (993984291279 / 1000000000000) ≤ (1508469 / 250000000) := by
  have h := checkLog_sound (w := (6015708721 / 1993984291279)) (n := 12)
    (lo := (48271 / 8000000)) (hi := (1508469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993984291279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993984291279) = 1/(993984291279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_567 : Bounds (-1508469 / 250000000) (-48271 / 8000000) (Real.log (993984291279 / 1000000000000)) := by
  have h := reflection_log_567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_568_neg : (3000963 / 500000000) ≤ -Real.log (62126003079 / 62500000000) ∧
    -Real.log (62126003079 / 62500000000) ≤ (6001927 / 1000000000) := by
  have h := checkLog_sound (w := (373996921 / 124626003079)) (n := 12)
    (lo := (3000963 / 500000000)) (hi := (6001927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62126003079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62126003079) = 1/(62126003079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_568 : Bounds (-6001927 / 1000000000) (-3000963 / 500000000) (Real.log (62126003079 / 62500000000)) := by
  have h := reflection_log_568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_569_neg : (155021709 / 1000000000) ≤ -Real.log (500000000000 / 583841655069) ∧
    -Real.log (500000000000 / 583841655069) ≤ (15502171 / 100000000) := by
  have h := checkLog_sound (w := (83841655069 / 1083841655069)) (n := 12)
    (lo := (155021709 / 1000000000)) (hi := (15502171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583841655069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583841655069 / 500000000000) = 1/(500000000000 / 583841655069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_569 : Bounds (155021709 / 1000000000) (15502171 / 100000000) (Real.log (583841655069 / 500000000000)) := by
  have h := reflection_log_569_neg
  have he : Real.log (583841655069 / 500000000000) = -Real.log (500000000000 / 583841655069) := by
    rw [show ((583841655069 / 500000000000) : ℝ) = ((500000000000 / 583841655069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_570_neg : (155434183 / 1000000000) ≤ -Real.log (500000000000 / 584082524699) ∧
    -Real.log (500000000000 / 584082524699) ≤ (19429273 / 125000000) := by
  have h := checkLog_sound (w := (84082524699 / 1084082524699)) (n := 12)
    (lo := (155434183 / 1000000000)) (hi := (19429273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584082524699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584082524699 / 500000000000) = 1/(500000000000 / 584082524699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_570 : Bounds (155434183 / 1000000000) (19429273 / 125000000) (Real.log (584082524699 / 500000000000)) := by
  have h := reflection_log_570_neg
  have he : Real.log (584082524699 / 500000000000) = -Real.log (500000000000 / 584082524699) := by
    rw [show ((584082524699 / 500000000000) : ℝ) = ((500000000000 / 584082524699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_571_neg : (310879817 / 1000000000) ≤ -Real.log (125000000000 / 170578150863) ∧
    -Real.log (125000000000 / 170578150863) ≤ (155439909 / 500000000) := by
  have h := checkLog_sound (w := (45578150863 / 295578150863)) (n := 12)
    (lo := (310879817 / 1000000000)) (hi := (155439909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170578150863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170578150863 / 125000000000) = 1/(125000000000 / 170578150863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_571 : Bounds (310879817 / 1000000000) (155439909 / 500000000) (Real.log (170578150863 / 125000000000)) := by
  have h := reflection_log_571_neg
  have he : Real.log (170578150863 / 125000000000) = -Real.log (125000000000 / 170578150863) := by
    rw [show ((170578150863 / 125000000000) : ℝ) = ((125000000000 / 170578150863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_572_neg : (311084691 / 1000000000) ≤ -Real.log (500000000000 / 682452406291) ∧
    -Real.log (500000000000 / 682452406291) ≤ (77771173 / 250000000) := by
  have h := checkLog_sound (w := (182452406291 / 1182452406291)) (n := 12)
    (lo := (311084691 / 1000000000)) (hi := (77771173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682452406291 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682452406291 / 500000000000) = 1/(500000000000 / 682452406291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_572 : Bounds (311084691 / 1000000000) (77771173 / 250000000) (Real.log (682452406291 / 500000000000)) := by
  have h := reflection_log_572_neg
  have he : Real.log (682452406291 / 500000000000) = -Real.log (500000000000 / 682452406291) := by
    rw [show ((682452406291 / 500000000000) : ℝ) = ((500000000000 / 682452406291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_573_neg : (17947591 / 125000000) ≤ -Real.log (1250 / 1443) ∧
    -Real.log (1250 / 1443) ≤ (143580729 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 2693)) (n := 12)
    (lo := (17947591 / 125000000)) (hi := (143580729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443 / 1250) = 1/(1250 / 1443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_573 : Bounds (17947591 / 125000000) (143580729 / 1000000000) (Real.log (1443 / 1250)) := by
  have h := reflection_log_573_neg
  have he : Real.log (1443 / 1250) = -Real.log (1250 / 1443) := by
    rw [show ((1443 / 1250) : ℝ) = ((1250 / 1443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_574_neg : (41927211 / 250000000) ≤ -Real.log (1057 / 1250) ∧
    -Real.log (1057 / 1250) ≤ (33541769 / 200000000) := by
  have h := checkLog_sound (w := (193 / 2307)) (n := 12)
    (lo := (41927211 / 250000000)) (hi := (33541769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1057) = 1/(1057 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_574 : Bounds (-33541769 / 200000000) (-41927211 / 250000000) (Real.log (1057 / 1250)) := by
  have h := reflection_log_574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_575_neg : (38597 / 250000000) ≤ -Real.log (1250000 / 1250193) ∧
    -Real.log (1250000 / 1250193) ≤ (154389 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 2500193)) (n := 12)
    (lo := (38597 / 250000000)) (hi := (154389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250193 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250193 / 1250000) = 1/(1250000 / 1250193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_575 : Bounds (38597 / 250000000) (154389 / 1000000000) (Real.log (1250193 / 1250000)) := by
  have h := reflection_log_575_neg
  have he : Real.log (1250193 / 1250000) = -Real.log (1250000 / 1250193) := by
    rw [show ((1250193 / 1250000) : ℝ) = ((1250000 / 1250193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
