import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0127
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

theorem reflection_log_1_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331515107 / 500000000) ≤ -Real.log (25600 / 49681) ∧
    -Real.log (25600 / 49681) ≤ (132606043 / 200000000) := by
  have h := checkLog_sound (w := (24081 / 75281)) (n := 12)
    (lo := (331515107 / 500000000)) (hi := (132606043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49681 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49681 / 25600) = 1/(25600 / 49681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331515107 / 500000000) (132606043 / 200000000) (Real.log (49681 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49681 / 25600) = -Real.log (25600 / 49681) := by
    rw [show ((49681 / 25600) : ℝ) = ((25600 / 49681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22596321 / 8000000) ≤ -Real.log (1519 / 25600) ∧
    -Real.log (1519 / 25600) ≤ (282454013 / 100000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1519) = 1/(1519 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-282454013 / 100000000) (-22596321 / 8000000) (Real.log (1519 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78997247 / 125000000) ≤ -Real.log (12800 / 24081) ∧
    -Real.log (12800 / 24081) ≤ (631977977 / 1000000000) := by
  have h := checkLog_sound (w := (11281 / 36881)) (n := 12)
    (lo := (78997247 / 125000000)) (hi := (631977977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24081 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24081 / 12800) = 1/(12800 / 24081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78997247 / 125000000) (631977977 / 1000000000) (Real.log (24081 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24081 / 12800) = -Real.log (12800 / 24081) := by
    rw [show ((24081 / 12800) : ℝ) = ((12800 / 24081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (426278589 / 200000000) ≤ -Real.log (1519 / 12800) ∧
    -Real.log (1519 / 12800) ≤ (2131392949 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 3119)) (n := 12)
    (lo := (10390281 / 200000000)) (hi := (25975703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1519) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1519) = 1/(1519 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2131392949 / 1000000000) (-426278589 / 200000000) (Real.log (1519 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669034799 / 1000000000) ≤ -Real.log (31250 / 61011) ∧
    -Real.log (31250 / 61011) ≤ (1672587 / 2500000) := by
  have h := checkLog_sound (w := (29761 / 92261)) (n := 12)
    (lo := (669034799 / 1000000000)) (hi := (1672587 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61011 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61011 / 31250) = 1/(31250 / 61011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669034799 / 1000000000) (1672587 / 2500000) (Real.log (61011 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61011 / 31250) = -Real.log (31250 / 61011) := by
    rw [show ((61011 / 31250) : ℝ) = ((31250 / 61011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152195731 / 50000000) ≤ -Real.log (1489 / 31250) ∧
    -Real.log (1489 / 31250) ≤ (24351317 / 8000000) := by
  have h := checkLog_sound (w := (3713 / 27537)) (n := 12)
    (lo := (2713259 / 10000000)) (hi := (271325901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11912) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11912) = 1/(1489 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24351317 / 8000000) (-152195731 / 50000000) (Real.log (1489 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669318519 / 1000000000) ≤ -Real.log (500000 / 976453) ∧
    -Real.log (500000 / 976453) ≤ (16732963 / 25000000) := by
  have h := checkLog_sound (w := (476453 / 1476453)) (n := 12)
    (lo := (669318519 / 1000000000)) (hi := (16732963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976453 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976453 / 500000) = 1/(500000 / 976453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669318519 / 1000000000) (16732963 / 25000000) (Real.log (976453 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (976453 / 500000) = -Real.log (500000 / 976453) := by
    rw [show ((976453 / 500000) : ℝ) = ((500000 / 976453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (381951209 / 125000000) ≤ -Real.log (23547 / 500000) ∧
    -Real.log (23547 / 500000) ≤ (3055609677 / 1000000000) := by
  have h := checkLog_sound (w := (7703 / 54797)) (n := 12)
    (lo := (35377619 / 125000000)) (hi := (283020953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23547) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 23547) = 1/(23547 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3055609677 / 1000000000) (-381951209 / 125000000) (Real.log (23547 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668671581 / 1000000000) ≤ -Real.log (1000000 / 1951643) ∧
    -Real.log (1000000 / 1951643) ≤ (334335791 / 500000000) := by
  have h := checkLog_sound (w := (951643 / 2951643)) (n := 12)
    (lo := (668671581 / 1000000000)) (hi := (334335791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951643 / 1000000) = 1/(1000000 / 1951643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668671581 / 1000000000) (334335791 / 500000000) (Real.log (1951643 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1951643 / 1000000) = -Real.log (1000000 / 1951643) := by
    rw [show ((1951643 / 1000000) : ℝ) = ((1000000 / 1951643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3029144287 / 1000000000) ≤ -Real.log (48357 / 1000000) ∧
    -Real.log (48357 / 1000000) ≤ (757286073 / 250000000) := by
  have h := checkLog_sound (w := (14143 / 110857)) (n := 12)
    (lo := (256555567 / 1000000000)) (hi := (16034723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48357) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48357) = 1/(48357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-757286073 / 250000000) (-3029144287 / 1000000000) (Real.log (48357 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (668965649 / 1000000000) ≤ -Real.log (1000000 / 1952217) ∧
    -Real.log (1000000 / 1952217) ≤ (13379313 / 20000000) := by
  have h := checkLog_sound (w := (952217 / 2952217)) (n := 12)
    (lo := (668965649 / 1000000000)) (hi := (13379313 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952217 / 1000000) = 1/(1000000 / 1952217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (668965649 / 1000000000) (13379313 / 20000000) (Real.log (1952217 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1952217 / 1000000) = -Real.log (1000000 / 1952217) := by
    rw [show ((1952217 / 1000000) : ℝ) = ((1000000 / 1952217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3041085349 / 1000000000) ≤ -Real.log (47783 / 1000000) ∧
    -Real.log (47783 / 1000000) ≤ (1520542677 / 500000000) := by
  have h := checkLog_sound (w := (14717 / 110283)) (n := 12)
    (lo := (268496629 / 1000000000)) (hi := (26849663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47783) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47783) = 1/(47783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1520542677 / 500000000) (-3041085349 / 1000000000) (Real.log (47783 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3712949419 / 1000000000) ≤ -Real.log (250000000000 / 10243619879113) ∧
    -Real.log (250000000000 / 10243619879113) ≤ (148517977 / 40000000) := by
  have h := checkLog_sound (w := (2243619879113 / 18243619879113)) (n := 12)
    (lo := (247213519 / 1000000000)) (hi := (3090169 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10243619879113 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10243619879113 / 8000000000000) = 1/(250000000000 / 10243619879113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3712949419 / 1000000000) (148517977 / 40000000) (Real.log (10243619879113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10243619879113 / 250000000000) = -Real.log (250000000000 / 10243619879113) := by
    rw [show ((10243619879113 / 250000000000) : ℝ) = ((250000000000 / 10243619879113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3724928191 / 1000000000) ≤ -Real.log (250000000000 / 10367063744851) ∧
    -Real.log (250000000000 / 10367063744851) ≤ (3724928197 / 1000000000) := by
  have h := checkLog_sound (w := (2367063744851 / 18367063744851)) (n := 12)
    (lo := (259192291 / 1000000000)) (hi := (64798073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10367063744851 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10367063744851 / 8000000000000) = 1/(250000000000 / 10367063744851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3724928191 / 1000000000) (3724928197 / 1000000000) (Real.log (10367063744851 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10367063744851 / 250000000000) = -Real.log (250000000000 / 10367063744851) := by
    rw [show ((10367063744851 / 250000000000) : ℝ) = ((250000000000 / 10367063744851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3697815869 / 1000000000) ≤ -Real.log (62500000000 / 2522441166739) ∧
    -Real.log (62500000000 / 2522441166739) ≤ (29582527 / 8000000) := by
  have h := checkLog_sound (w := (522441166739 / 4522441166739)) (n := 12)
    (lo := (232079969 / 1000000000)) (hi := (23207997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2522441166739 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2522441166739 / 2000000000000) = 1/(62500000000 / 2522441166739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3697815869 / 1000000000) (29582527 / 8000000) (Real.log (2522441166739 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2522441166739 / 62500000000) = -Real.log (62500000000 / 2522441166739) := by
    rw [show ((2522441166739 / 62500000000) : ℝ) = ((62500000000 / 2522441166739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1855025499 / 500000000) ≤ -Real.log (500000000000 / 20427945085073) ∧
    -Real.log (500000000000 / 20427945085073) ≤ (927512751 / 250000000) := by
  have h := checkLog_sound (w := (4427945085073 / 36427945085073)) (n := 12)
    (lo := (122157549 / 500000000)) (hi := (244315099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20427945085073 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20427945085073 / 16000000000000) = 1/(500000000000 / 20427945085073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1855025499 / 500000000) (927512751 / 250000000) (Real.log (20427945085073 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20427945085073 / 500000000000) = -Real.log (500000000000 / 20427945085073) := by
    rw [show ((20427945085073 / 500000000000) : ℝ) = ((500000000000 / 20427945085073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0127
