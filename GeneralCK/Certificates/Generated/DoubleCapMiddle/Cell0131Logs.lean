import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0131
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

theorem reflection_log_1_neg : (61405007 / 200000000) ≤ -Real.log (64 / 87) ∧
    -Real.log (64 / 87) ≤ (76756259 / 250000000) := by
  have h := checkLog_sound (w := (23 / 151)) (n := 12)
    (lo := (61405007 / 200000000)) (hi := (76756259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 64) = 1/(64 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61405007 / 200000000) (76756259 / 250000000) (Real.log (87 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (87 / 64) = -Real.log (64 / 87) := by
    rw [show ((87 / 64) : ℝ) = ((64 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55663877 / 125000000) ≤ -Real.log (41 / 64) ∧
    -Real.log (41 / 64) ≤ (445311017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 41) = 1/(41 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-445311017 / 1000000000) (-55663877 / 125000000) (Real.log (41 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153081297 / 500000000) ≤ -Real.log (2560 / 3477) ∧
    -Real.log (2560 / 3477) ≤ (61232519 / 200000000) := by
  have h := checkLog_sound (w := (917 / 6037)) (n := 12)
    (lo := (153081297 / 500000000)) (hi := (61232519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3477 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3477 / 2560) = 1/(2560 / 3477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153081297 / 500000000) (61232519 / 200000000) (Real.log (3477 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3477 / 2560) = -Real.log (2560 / 3477) := by
    rw [show ((3477 / 2560) : ℝ) = ((2560 / 3477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (443483419 / 1000000000) ≤ -Real.log (1643 / 2560) ∧
    -Real.log (1643 / 2560) ≤ (22174171 / 50000000) := by
  have h := checkLog_sound (w := (917 / 4203)) (n := 12)
    (lo := (443483419 / 1000000000)) (hi := (22174171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1643) = 1/(1643 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22174171 / 50000000) (-443483419 / 1000000000) (Real.log (1643 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (108046543 / 200000000) ≤ -Real.log (1280 / 2197) ∧
    -Real.log (1280 / 2197) ≤ (135058179 / 250000000) := by
  have h := checkLog_sound (w := (917 / 3477)) (n := 12)
    (lo := (108046543 / 200000000)) (hi := (135058179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2197 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2197 / 1280) = 1/(1280 / 2197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (108046543 / 200000000) (135058179 / 250000000) (Real.log (2197 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2197 / 1280) = -Real.log (1280 / 2197) := by
    rw [show ((2197 / 1280) : ℝ) = ((1280 / 2197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (630106261 / 500000000) ≤ -Real.log (363 / 1280) ∧
    -Real.log (363 / 1280) ≤ (315053131 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 363) = 1/(363 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-315053131 / 250000000) (-630106261 / 500000000) (Real.log (363 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (419166809 / 1000000000) ≤ -Real.log (500000 / 760347) ∧
    -Real.log (500000 / 760347) ≤ (41916681 / 100000000) := by
  have h := checkLog_sound (w := (260347 / 1260347)) (n := 12)
    (lo := (419166809 / 1000000000)) (hi := (41916681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760347 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760347 / 500000) = 1/(500000 / 760347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (419166809 / 1000000000) (41916681 / 100000000) (Real.log (760347 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (760347 / 500000) = -Real.log (500000 / 760347) := by
    rw [show ((760347 / 500000) : ℝ) = ((500000 / 760347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367708027 / 500000000) ≤ -Real.log (239653 / 500000) ∧
    -Real.log (239653 / 500000) ≤ (91927007 / 125000000) := by
  have h := checkLog_sound (w := (10347 / 489653)) (n := 12)
    (lo := (21134437 / 500000000)) (hi := (338151 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 239653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 239653) = 1/(239653 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91927007 / 125000000) (-367708027 / 500000000) (Real.log (239653 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (420368827 / 1000000000) ≤ -Real.log (1000000 / 1522523) ∧
    -Real.log (1000000 / 1522523) ≤ (105092207 / 250000000) := by
  have h := checkLog_sound (w := (522523 / 2522523)) (n := 12)
    (lo := (420368827 / 1000000000)) (hi := (105092207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1522523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1522523 / 1000000) = 1/(1000000 / 1522523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (420368827 / 1000000000) (105092207 / 250000000) (Real.log (1522523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1522523 / 1000000) = -Real.log (1000000 / 1522523) := by
    rw [show ((1522523 / 1000000) : ℝ) = ((1000000 / 1522523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (739239287 / 1000000000) ≤ -Real.log (477477 / 1000000) ∧
    -Real.log (477477 / 1000000) ≤ (739239289 / 1000000000) := by
  have h := checkLog_sound (w := (22523 / 977477)) (n := 12)
    (lo := (46092107 / 1000000000)) (hi := (11523027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 477477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 477477) = 1/(477477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-739239289 / 1000000000) (-739239287 / 1000000000) (Real.log (477477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10468339 / 31250000) ≤ -Real.log (500000 / 698961) ∧
    -Real.log (500000 / 698961) ≤ (334986849 / 1000000000) := by
  have h := checkLog_sound (w := (198961 / 1198961)) (n := 12)
    (lo := (10468339 / 31250000)) (hi := (334986849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698961 / 500000) = 1/(500000 / 698961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10468339 / 31250000) (334986849 / 1000000000) (Real.log (698961 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (698961 / 500000) = -Real.log (500000 / 698961) := by
    rw [show ((698961 / 500000) : ℝ) = ((500000 / 698961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (507368273 / 1000000000) ≤ -Real.log (301039 / 500000) ∧
    -Real.log (301039 / 500000) ≤ (253684137 / 500000000) := by
  have h := checkLog_sound (w := (198961 / 801039)) (n := 12)
    (lo := (507368273 / 1000000000)) (hi := (253684137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 301039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 301039) = 1/(301039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-253684137 / 500000000) (-507368273 / 1000000000) (Real.log (301039 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336147183 / 1000000000) ≤ -Real.log (200000 / 279909) ∧
    -Real.log (200000 / 279909) ≤ (21009199 / 62500000) := by
  have h := checkLog_sound (w := (79909 / 479909)) (n := 12)
    (lo := (336147183 / 1000000000)) (hi := (21009199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279909 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279909 / 200000) = 1/(200000 / 279909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336147183 / 1000000000) (21009199 / 62500000) (Real.log (279909 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (279909 / 200000) = -Real.log (200000 / 279909) := by
    rw [show ((279909 / 200000) : ℝ) = ((200000 / 279909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (510067577 / 1000000000) ≤ -Real.log (120091 / 200000) ∧
    -Real.log (120091 / 200000) ≤ (255033789 / 500000000) := by
  have h := checkLog_sound (w := (79909 / 320091)) (n := 12)
    (lo := (510067577 / 1000000000)) (hi := (255033789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120091) = 1/(120091 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255033789 / 500000000) (-510067577 / 1000000000) (Real.log (120091 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1154582863 / 1000000000) ≤ -Real.log (500000000000 / 1586349847487) ∧
    -Real.log (500000000000 / 1586349847487) ≤ (230916573 / 200000000) := by
  have h := checkLog_sound (w := (586349847487 / 2586349847487)) (n := 12)
    (lo := (461435683 / 1000000000)) (hi := (115358921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1586349847487 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1586349847487 / 1000000000000) = 1/(500000000000 / 1586349847487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1154582863 / 1000000000) (230916573 / 200000000) (Real.log (1586349847487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1586349847487 / 500000000000) = -Real.log (500000000000 / 1586349847487) := by
    rw [show ((1586349847487 / 500000000000) : ℝ) = ((500000000000 / 1586349847487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (579804057 / 500000000) ≤ -Real.log (62500000000 / 199292714623) ∧
    -Real.log (62500000000 / 199292714623) ≤ (289902029 / 250000000) := by
  have h := checkLog_sound (w := (74292714623 / 324292714623)) (n := 12)
    (lo := (233230467 / 500000000)) (hi := (93292187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199292714623 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(199292714623 / 125000000000) = 1/(62500000000 / 199292714623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (579804057 / 500000000) (289902029 / 250000000) (Real.log (199292714623 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (199292714623 / 62500000000) = -Real.log (62500000000 / 199292714623) := by
    rw [show ((199292714623 / 62500000000) : ℝ) = ((62500000000 / 199292714623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (842355121 / 1000000000) ≤ -Real.log (500000000000 / 1160914366577) ∧
    -Real.log (500000000000 / 1160914366577) ≤ (842355123 / 1000000000) := by
  have h := checkLog_sound (w := (160914366577 / 2160914366577)) (n := 12)
    (lo := (149207941 / 1000000000)) (hi := (74603971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160914366577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160914366577 / 1000000000000) = 1/(500000000000 / 1160914366577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (842355121 / 1000000000) (842355123 / 1000000000) (Real.log (1160914366577 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1160914366577 / 500000000000) = -Real.log (500000000000 / 1160914366577) := by
    rw [show ((1160914366577 / 500000000000) : ℝ) = ((500000000000 / 1160914366577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (846214761 / 1000000000) ≤ -Real.log (500000000000 / 1165403735501) ∧
    -Real.log (500000000000 / 1165403735501) ≤ (846214763 / 1000000000) := by
  have h := checkLog_sound (w := (165403735501 / 2165403735501)) (n := 12)
    (lo := (153067581 / 1000000000)) (hi := (76533791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165403735501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165403735501 / 1000000000000) = 1/(500000000000 / 1165403735501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (846214761 / 1000000000) (846214763 / 1000000000) (Real.log (1165403735501 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1165403735501 / 500000000000) = -Real.log (500000000000 / 1165403735501) := by
    rw [show ((1165403735501 / 500000000000) : ℝ) = ((500000000000 / 1165403735501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0131
