import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0129
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

theorem reflection_log_1_neg : (662647701 / 1000000000) ≤ -Real.log (12800 / 24831) ∧
    -Real.log (12800 / 24831) ≤ (331323851 / 500000000) := by
  have h := checkLog_sound (w := (12031 / 37631)) (n := 12)
    (lo := (662647701 / 1000000000)) (hi := (331323851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24831 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24831 / 12800) = 1/(12800 / 24831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (662647701 / 1000000000) (331323851 / 500000000) (Real.log (24831 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24831 / 12800) = -Real.log (12800 / 24831) := by
    rw [show ((24831 / 12800) : ℝ) = ((12800 / 24831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1406054739 / 500000000) ≤ -Real.log (769 / 12800) ∧
    -Real.log (769 / 12800) ≤ (2812109483 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 769) = 1/(769 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2812109483 / 1000000000) (-1406054739 / 500000000) (Real.log (769 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331132521 / 500000000) ≤ -Real.log (25600 / 49643) ∧
    -Real.log (25600 / 49643) ≤ (662265043 / 1000000000) := by
  have h := checkLog_sound (w := (24043 / 75243)) (n := 12)
    (lo := (331132521 / 500000000)) (hi := (662265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49643 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49643 / 25600) = 1/(25600 / 49643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331132521 / 500000000) (662265043 / 1000000000) (Real.log (49643 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49643 / 25600) = -Real.log (25600 / 49643) := by
    rw [show ((49643 / 25600) : ℝ) = ((25600 / 49643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (87494733 / 31250000) ≤ -Real.log (1557 / 25600) ∧
    -Real.log (1557 / 25600) ≤ (2799831461 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1557) = 1/(1557 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2799831461 / 1000000000) (-87494733 / 31250000) (Real.log (1557 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (631188661 / 1000000000) ≤ -Real.log (6400 / 12031) ∧
    -Real.log (6400 / 12031) ≤ (315594331 / 500000000) := by
  have h := checkLog_sound (w := (5631 / 18431)) (n := 12)
    (lo := (631188661 / 1000000000)) (hi := (315594331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12031 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12031 / 6400) = 1/(6400 / 12031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (631188661 / 1000000000) (315594331 / 500000000) (Real.log (12031 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12031 / 6400) = -Real.log (6400 / 12031) := by
    rw [show ((12031 / 6400) : ℝ) = ((6400 / 12031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1059481149 / 500000000) ≤ -Real.log (769 / 6400) ∧
    -Real.log (769 / 6400) ≤ (1059481151 / 500000000) := by
  have h := checkLog_sound (w := (31 / 1569)) (n := 12)
    (lo := (19760379 / 500000000)) (hi := (39520759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 769) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 769) = 1/(769 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1059481151 / 500000000) (-1059481149 / 500000000) (Real.log (769 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (315199361 / 500000000) ≤ -Real.log (12800 / 24043) ∧
    -Real.log (12800 / 24043) ≤ (630398723 / 1000000000) := by
  have h := checkLog_sound (w := (11243 / 36843)) (n := 12)
    (lo := (315199361 / 500000000)) (hi := (630398723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24043 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24043 / 12800) = 1/(12800 / 24043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (315199361 / 500000000) (630398723 / 1000000000) (Real.log (24043 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24043 / 12800) = -Real.log (12800 / 24043) := by
    rw [show ((24043 / 12800) : ℝ) = ((12800 / 24043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (526671069 / 250000000) ≤ -Real.log (1557 / 12800) ∧
    -Real.log (1557 / 12800) ≤ (52667107 / 25000000) := by
  have h := checkLog_sound (w := (43 / 3157)) (n := 12)
    (lo := (1702671 / 62500000)) (hi := (27242737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1557) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1557) = 1/(1557 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52667107 / 25000000) (-526671069 / 250000000) (Real.log (1557 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8355871 / 12500000) ≤ -Real.log (1000000 / 1951249) ∧
    -Real.log (1000000 / 1951249) ≤ (668469681 / 1000000000) := by
  have h := checkLog_sound (w := (951249 / 2951249)) (n := 12)
    (lo := (8355871 / 12500000)) (hi := (668469681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951249 / 1000000) = 1/(1000000 / 1951249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8355871 / 12500000) (668469681 / 1000000000) (Real.log (1951249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1951249 / 1000000) = -Real.log (1000000 / 1951249) := by
    rw [show ((1951249 / 1000000) : ℝ) = ((1000000 / 1951249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1510514783 / 500000000) ≤ -Real.log (48751 / 1000000) ∧
    -Real.log (48751 / 1000000) ≤ (3021029571 / 1000000000) := by
  have h := checkLog_sound (w := (13749 / 111251)) (n := 12)
    (lo := (124220423 / 500000000)) (hi := (248440847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48751) = 1/(48751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3021029571 / 1000000000) (-1510514783 / 500000000) (Real.log (48751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83594067 / 125000000) ≤ -Real.log (1000000 / 1951801) ∧
    -Real.log (1000000 / 1951801) ≤ (668752537 / 1000000000) := by
  have h := checkLog_sound (w := (951801 / 2951801)) (n := 12)
    (lo := (83594067 / 125000000)) (hi := (668752537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951801 / 1000000) = 1/(1000000 / 1951801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83594067 / 125000000) (668752537 / 1000000000) (Real.log (1951801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1951801 / 1000000) = -Real.log (1000000 / 1951801) := by
    rw [show ((1951801 / 1000000) : ℝ) = ((1000000 / 1951801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1516208501 / 500000000) ≤ -Real.log (48199 / 1000000) ∧
    -Real.log (48199 / 1000000) ≤ (3032417007 / 1000000000) := by
  have h := checkLog_sound (w := (14301 / 110699)) (n := 12)
    (lo := (129914141 / 500000000)) (hi := (259828283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48199) = 1/(48199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3032417007 / 1000000000) (-1516208501 / 500000000) (Real.log (48199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668085237 / 1000000000) ≤ -Real.log (1000000 / 1950499) ∧
    -Real.log (1000000 / 1950499) ≤ (334042619 / 500000000) := by
  have h := checkLog_sound (w := (950499 / 2950499)) (n := 12)
    (lo := (668085237 / 1000000000)) (hi := (334042619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950499 / 1000000) = 1/(1000000 / 1950499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668085237 / 1000000000) (334042619 / 500000000) (Real.log (1950499 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1950499 / 1000000) = -Real.log (1000000 / 1950499) := by
    rw [show ((1950499 / 1000000) : ℝ) = ((1000000 / 1950499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601152481 / 200000000) ≤ -Real.log (49501 / 1000000) ∧
    -Real.log (49501 / 1000000) ≤ (300576241 / 100000000) := by
  have h := checkLog_sound (w := (12999 / 112001)) (n := 12)
    (lo := (46634737 / 200000000)) (hi := (116586843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49501) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49501) = 1/(49501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300576241 / 100000000) (-601152481 / 200000000) (Real.log (49501 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (133675793 / 200000000) ≤ -Real.log (31250 / 60971) ∧
    -Real.log (31250 / 60971) ≤ (334189483 / 500000000) := by
  have h := checkLog_sound (w := (29721 / 92221)) (n := 12)
    (lo := (133675793 / 200000000)) (hi := (334189483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60971 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60971 / 31250) = 1/(31250 / 60971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (133675793 / 200000000) (334189483 / 500000000) (Real.log (60971 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (60971 / 31250) = -Real.log (31250 / 60971) := by
    rw [show ((60971 / 31250) : ℝ) = ((31250 / 60971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1508702723 / 500000000) ≤ -Real.log (1529 / 31250) ∧
    -Real.log (1529 / 31250) ≤ (3017405451 / 1000000000) := by
  have h := checkLog_sound (w := (3393 / 27857)) (n := 12)
    (lo := (122408363 / 500000000)) (hi := (244816727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12232) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12232) = 1/(1529 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3017405451 / 1000000000) (-1508702723 / 500000000) (Real.log (1529 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1844749623 / 500000000) ≤ -Real.log (250000000000 / 10006199872823) ∧
    -Real.log (250000000000 / 10006199872823) ≤ (922374813 / 250000000) := by
  have h := checkLog_sound (w := (2006199872823 / 18006199872823)) (n := 12)
    (lo := (111881673 / 500000000)) (hi := (223763347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10006199872823 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10006199872823 / 8000000000000) = 1/(250000000000 / 10006199872823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1844749623 / 500000000) (922374813 / 250000000) (Real.log (10006199872823 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10006199872823 / 250000000000) = -Real.log (250000000000 / 10006199872823) := by
    rw [show ((10006199872823 / 250000000000) : ℝ) = ((250000000000 / 10006199872823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1850584769 / 500000000) ≤ -Real.log (62500000000 / 2530914801137) ∧
    -Real.log (62500000000 / 2530914801137) ≤ (462646193 / 125000000) := by
  have h := checkLog_sound (w := (530914801137 / 4530914801137)) (n := 12)
    (lo := (117716819 / 500000000)) (hi := (235433639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2530914801137 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2530914801137 / 2000000000000) = 1/(62500000000 / 2530914801137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1850584769 / 500000000) (462646193 / 125000000) (Real.log (2530914801137 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2530914801137 / 62500000000) = -Real.log (62500000000 / 2530914801137) := by
    rw [show ((2530914801137 / 62500000000) : ℝ) = ((62500000000 / 2530914801137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1836923821 / 500000000) ≤ -Real.log (125000000000 / 4925403022161) ∧
    -Real.log (125000000000 / 4925403022161) ≤ (114807739 / 31250000) := by
  have h := checkLog_sound (w := (925403022161 / 8925403022161)) (n := 12)
    (lo := (104055871 / 500000000)) (hi := (208111743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4925403022161 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4925403022161 / 4000000000000) = 1/(125000000000 / 4925403022161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1836923821 / 500000000) (114807739 / 31250000) (Real.log (4925403022161 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4925403022161 / 125000000000) = -Real.log (125000000000 / 4925403022161) := by
    rw [show ((4925403022161 / 125000000000) : ℝ) = ((125000000000 / 4925403022161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3685784411 / 1000000000) ≤ -Real.log (500000000000 / 19938194898627) ∧
    -Real.log (500000000000 / 19938194898627) ≤ (3685784417 / 1000000000) := by
  have h := checkLog_sound (w := (3938194898627 / 35938194898627)) (n := 12)
    (lo := (220048511 / 1000000000)) (hi := (1719129 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19938194898627 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19938194898627 / 16000000000000) = 1/(500000000000 / 19938194898627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3685784411 / 1000000000) (3685784417 / 1000000000) (Real.log (19938194898627 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19938194898627 / 500000000000) = -Real.log (500000000000 / 19938194898627) := by
    rw [show ((19938194898627 / 500000000000) : ℝ) = ((500000000000 / 19938194898627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0129
