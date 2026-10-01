import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0113
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

theorem reflection_log_1_neg : (334375211 / 500000000) ≤ -Real.log (12800 / 24983) ∧
    -Real.log (12800 / 24983) ≤ (668750423 / 1000000000) := by
  have h := checkLog_sound (w := (12183 / 37783)) (n := 12)
    (lo := (334375211 / 500000000)) (hi := (668750423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24983 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24983 / 12800) = 1/(12800 / 24983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (334375211 / 500000000) (668750423 / 1000000000) (Real.log (24983 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24983 / 12800) = -Real.log (12800 / 24983) := by
    rw [show ((24983 / 12800) : ℝ) = ((12800 / 24983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3032331423 / 1000000000) ≤ -Real.log (617 / 12800) ∧
    -Real.log (617 / 12800) ≤ (758082857 / 250000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 617) = 1/(617 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-758082857 / 250000000) (-3032331423 / 1000000000) (Real.log (617 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (668370091 / 1000000000) ≤ -Real.log (25600 / 49947) ∧
    -Real.log (25600 / 49947) ≤ (167092523 / 250000000) := by
  have h := checkLog_sound (w := (24347 / 75547)) (n := 12)
    (lo := (668370091 / 1000000000)) (hi := (167092523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49947 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49947 / 25600) = 1/(25600 / 49947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (668370091 / 1000000000) (167092523 / 250000000) (Real.log (49947 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49947 / 25600) = -Real.log (25600 / 49947) := by
    rw [show ((49947 / 25600) : ℝ) = ((25600 / 49947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3017051673 / 1000000000) ≤ -Real.log (1253 / 25600) ∧
    -Real.log (1253 / 25600) ≤ (1508525839 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1253) = 1/(1253 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1508525839 / 500000000) (-3017051673 / 1000000000) (Real.log (1253 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (643743547 / 1000000000) ≤ -Real.log (6400 / 12183) ∧
    -Real.log (6400 / 12183) ≤ (160935887 / 250000000) := by
  have h := checkLog_sound (w := (5783 / 18583)) (n := 12)
    (lo := (643743547 / 1000000000)) (hi := (160935887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12183 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12183 / 6400) = 1/(6400 / 12183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (643743547 / 1000000000) (160935887 / 250000000) (Real.log (12183 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12183 / 6400) = -Real.log (6400 / 12183) := by
    rw [show ((12183 / 6400) : ℝ) = ((6400 / 12183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2339184243 / 1000000000) ≤ -Real.log (617 / 6400) ∧
    -Real.log (617 / 6400) ≤ (2339184247 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 617) = 1/(617 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2339184247 / 1000000000) (-2339184243 / 1000000000) (Real.log (617 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (642963467 / 1000000000) ≤ -Real.log (12800 / 24347) ∧
    -Real.log (12800 / 24347) ≤ (160740867 / 250000000) := by
  have h := checkLog_sound (w := (11547 / 37147)) (n := 12)
    (lo := (642963467 / 1000000000)) (hi := (160740867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24347 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24347 / 12800) = 1/(12800 / 24347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (642963467 / 1000000000) (160740867 / 250000000) (Real.log (24347 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24347 / 12800) = -Real.log (12800 / 24347) := by
    rw [show ((24347 / 12800) : ℝ) = ((12800 / 24347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2323904493 / 1000000000) ≤ -Real.log (1253 / 12800) ∧
    -Real.log (1253 / 12800) ≤ (2323904497 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1253) = 1/(1253 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2323904497 / 1000000000) (-2323904493 / 1000000000) (Real.log (1253 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168258311 / 250000000) ≤ -Real.log (500000 / 980087) ∧
    -Real.log (500000 / 980087) ≤ (134606649 / 200000000) := by
  have h := checkLog_sound (w := (480087 / 1480087)) (n := 12)
    (lo := (168258311 / 250000000)) (hi := (134606649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980087 / 500000) = 1/(500000 / 980087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168258311 / 250000000) (134606649 / 200000000) (Real.log (980087 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980087 / 500000) = -Real.log (500000 / 980087) := by
    rw [show ((980087 / 500000) : ℝ) = ((500000 / 980087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3223235311 / 1000000000) ≤ -Real.log (19913 / 500000) ∧
    -Real.log (19913 / 500000) ≤ (805808829 / 250000000) := by
  have h := checkLog_sound (w := (11337 / 51163)) (n := 12)
    (lo := (450646591 / 1000000000)) (hi := (7041353 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19913) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19913) = 1/(19913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-805808829 / 250000000) (-3223235311 / 1000000000) (Real.log (19913 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (673322463 / 1000000000) ≤ -Real.log (1000000 / 1960741) ∧
    -Real.log (1000000 / 1960741) ≤ (21041327 / 31250000) := by
  have h := checkLog_sound (w := (960741 / 2960741)) (n := 12)
    (lo := (673322463 / 1000000000)) (hi := (21041327 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960741 / 1000000) = 1/(1000000 / 1960741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (673322463 / 1000000000) (21041327 / 31250000) (Real.log (1960741 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1960741 / 1000000) = -Real.log (1000000 / 1960741) := by
    rw [show ((1960741 / 1000000) : ℝ) = ((1000000 / 1960741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3237574559 / 1000000000) ≤ -Real.log (39259 / 1000000) ∧
    -Real.log (39259 / 1000000) ≤ (809393641 / 250000000) := by
  have h := checkLog_sound (w := (23241 / 101759)) (n := 12)
    (lo := (464985839 / 1000000000)) (hi := (5812323 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39259) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39259) = 1/(39259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-809393641 / 250000000) (-3237574559 / 1000000000) (Real.log (39259 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26912003 / 40000000) ≤ -Real.log (1000000 / 1959717) ∧
    -Real.log (1000000 / 1959717) ≤ (168200019 / 250000000) := by
  have h := checkLog_sound (w := (959717 / 2959717)) (n := 12)
    (lo := (26912003 / 40000000)) (hi := (168200019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959717 / 1000000) = 1/(1000000 / 1959717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26912003 / 40000000) (168200019 / 250000000) (Real.log (1959717 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1959717 / 1000000) = -Real.log (1000000 / 1959717) := by
    rw [show ((1959717 / 1000000) : ℝ) = ((1000000 / 1959717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3211825733 / 1000000000) ≤ -Real.log (40283 / 1000000) ∧
    -Real.log (40283 / 1000000) ≤ (1605912869 / 500000000) := by
  have h := checkLog_sound (w := (22217 / 102783)) (n := 12)
    (lo := (439237013 / 1000000000)) (hi := (219618507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40283) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40283) = 1/(40283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1605912869 / 500000000) (-3211825733 / 1000000000) (Real.log (40283 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (168274253 / 250000000) ≤ -Real.log (1000000 / 1960299) ∧
    -Real.log (1000000 / 1960299) ≤ (673097013 / 1000000000) := by
  have h := checkLog_sound (w := (960299 / 2960299)) (n := 12)
    (lo := (168274253 / 250000000)) (hi := (673097013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960299 / 1000000) = 1/(1000000 / 1960299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (168274253 / 250000000) (673097013 / 1000000000) (Real.log (1960299 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1960299 / 1000000) = -Real.log (1000000 / 1960299) := by
    rw [show ((1960299 / 1000000) : ℝ) = ((1000000 / 1960299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (32263789 / 10000000) ≤ -Real.log (39701 / 1000000) ∧
    -Real.log (39701 / 1000000) ≤ (645275781 / 200000000) := by
  have h := checkLog_sound (w := (22799 / 102201)) (n := 12)
    (lo := (22689509 / 50000000)) (hi := (453790181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39701) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39701) = 1/(39701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-645275781 / 200000000) (-32263789 / 10000000) (Real.log (39701 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (779253711 / 200000000) ≤ -Real.log (15625000000 / 769038285291) ∧
    -Real.log (15625000000 / 769038285291) ≤ (3896268561 / 1000000000) := by
  have h := checkLog_sound (w := (269038285291 / 1269038285291)) (n := 12)
    (lo := (86106531 / 200000000)) (hi := (26908291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769038285291 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(769038285291 / 500000000000) = 1/(15625000000 / 769038285291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (779253711 / 200000000) (3896268561 / 1000000000) (Real.log (769038285291 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (769038285291 / 15625000000) = -Real.log (15625000000 / 769038285291) := by
    rw [show ((769038285291 / 15625000000) : ℝ) = ((15625000000 / 769038285291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3910897021 / 1000000000) ≤ -Real.log (250000000000 / 12485933161823) ∧
    -Real.log (250000000000 / 12485933161823) ≤ (3910897027 / 1000000000) := by
  have h := checkLog_sound (w := (4485933161823 / 20485933161823)) (n := 12)
    (lo := (445161121 / 1000000000)) (hi := (222580561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12485933161823 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12485933161823 / 8000000000000) = 1/(250000000000 / 12485933161823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3910897021 / 1000000000) (3910897027 / 1000000000) (Real.log (12485933161823 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12485933161823 / 250000000000) = -Real.log (250000000000 / 12485933161823) := by
    rw [show ((12485933161823 / 250000000000) : ℝ) = ((250000000000 / 12485933161823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3884625807 / 1000000000) ≤ -Real.log (100000000000 / 4864873519847) ∧
    -Real.log (100000000000 / 4864873519847) ≤ (3884625813 / 1000000000) := by
  have h := checkLog_sound (w := (1664873519847 / 8064873519847)) (n := 12)
    (lo := (418889907 / 1000000000)) (hi := (104722477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4864873519847 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4864873519847 / 3200000000000) = 1/(100000000000 / 4864873519847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3884625807 / 1000000000) (3884625813 / 1000000000) (Real.log (4864873519847 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4864873519847 / 100000000000) = -Real.log (100000000000 / 4864873519847) := by
    rw [show ((4864873519847 / 100000000000) : ℝ) = ((100000000000 / 4864873519847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (487434489 / 125000000) ≤ -Real.log (500000000000 / 24688282411023) ∧
    -Real.log (500000000000 / 24688282411023) ≤ (1949737959 / 500000000) := by
  have h := checkLog_sound (w := (8688282411023 / 40688282411023)) (n := 12)
    (lo := (108435003 / 250000000)) (hi := (433740013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24688282411023 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24688282411023 / 16000000000000) = 1/(500000000000 / 24688282411023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (487434489 / 125000000) (1949737959 / 500000000) (Real.log (24688282411023 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24688282411023 / 500000000000) = -Real.log (500000000000 / 24688282411023) := by
    rw [show ((24688282411023 / 500000000000) : ℝ) = ((500000000000 / 24688282411023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0113
