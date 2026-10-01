import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0128
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

theorem reflection_log_1_neg : (331515107 / 500000000) ≤ -Real.log (25600 / 49681) ∧
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


theorem reflection_log_1 : Bounds (331515107 / 500000000) (132606043 / 200000000) (Real.log (49681 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49681 / 25600) = -Real.log (25600 / 49681) := by
    rw [show ((49681 / 25600) : ℝ) = ((25600 / 49681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22596321 / 8000000) ≤ -Real.log (1519 / 25600) ∧
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


theorem reflection_log_2 : Bounds (-282454013 / 100000000) (-22596321 / 8000000) (Real.log (1519 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (662647701 / 1000000000) ≤ -Real.log (12800 / 24831) ∧
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


theorem reflection_log_3 : Bounds (662647701 / 1000000000) (331323851 / 500000000) (Real.log (24831 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24831 / 12800) = -Real.log (12800 / 24831) := by
    rw [show ((24831 / 12800) : ℝ) = ((12800 / 24831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1406054739 / 500000000) ≤ -Real.log (769 / 12800) ∧
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


theorem reflection_log_4 : Bounds (-2812109483 / 1000000000) (-1406054739 / 500000000) (Real.log (769 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78997247 / 125000000) ≤ -Real.log (12800 / 24081) ∧
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


theorem reflection_log_5 : Bounds (78997247 / 125000000) (631977977 / 1000000000) (Real.log (24081 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24081 / 12800) = -Real.log (12800 / 24081) := by
    rw [show ((24081 / 12800) : ℝ) = ((12800 / 24081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (426278589 / 200000000) ≤ -Real.log (1519 / 12800) ∧
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


theorem reflection_log_6 : Bounds (-2131392949 / 1000000000) (-426278589 / 200000000) (Real.log (1519 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (631188661 / 1000000000) ≤ -Real.log (6400 / 12031) ∧
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


theorem reflection_log_7 : Bounds (631188661 / 1000000000) (315594331 / 500000000) (Real.log (12031 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12031 / 6400) = -Real.log (6400 / 12031) := by
    rw [show ((12031 / 6400) : ℝ) = ((6400 / 12031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1059481149 / 500000000) ≤ -Real.log (769 / 6400) ∧
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


theorem reflection_log_8 : Bounds (-1059481151 / 500000000) (-1059481149 / 500000000) (Real.log (769 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (668752023 / 1000000000) ≤ -Real.log (5000 / 9759) ∧
    -Real.log (5000 / 9759) ≤ (83594003 / 125000000) := by
  have h := checkLog_sound (w := (4759 / 14759)) (n := 12)
    (lo := (668752023 / 1000000000)) (hi := (83594003 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9759 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9759 / 5000) = 1/(5000 / 9759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (668752023 / 1000000000) (83594003 / 125000000) (Real.log (9759 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (9759 / 5000) = -Real.log (5000 / 9759) := by
    rw [show ((9759 / 5000) : ℝ) = ((5000 / 9759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (606479251 / 200000000) ≤ -Real.log (241 / 5000) ∧
    -Real.log (241 / 5000) ≤ (151619813 / 50000000) := by
  have h := checkLog_sound (w := (143 / 1107)) (n := 12)
    (lo := (51961507 / 200000000)) (hi := (16237971 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 482) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 482) = 1/(241 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151619813 / 50000000) (-606479251 / 200000000) (Real.log (241 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669035311 / 1000000000) ≤ -Real.log (1000000 / 1952353) ∧
    -Real.log (1000000 / 1952353) ≤ (41814707 / 62500000) := by
  have h := checkLog_sound (w := (952353 / 2952353)) (n := 12)
    (lo := (669035311 / 1000000000)) (hi := (41814707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952353 / 1000000) = 1/(1000000 / 1952353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669035311 / 1000000000) (41814707 / 62500000) (Real.log (1952353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1952353 / 1000000) = -Real.log (1000000 / 1952353) := by
    rw [show ((1952353 / 1000000) : ℝ) = ((1000000 / 1952353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3043935607 / 1000000000) ≤ -Real.log (47647 / 1000000) ∧
    -Real.log (47647 / 1000000) ≤ (760983903 / 250000000) := by
  have h := checkLog_sound (w := (14853 / 110147)) (n := 12)
    (lo := (271346887 / 1000000000)) (hi := (33918361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47647) = 1/(47647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-760983903 / 250000000) (-3043935607 / 1000000000) (Real.log (47647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167094613 / 250000000) ≤ -Real.log (1000000 / 1951071) ∧
    -Real.log (1000000 / 1951071) ≤ (668378453 / 1000000000) := by
  have h := checkLog_sound (w := (951071 / 2951071)) (n := 12)
    (lo := (167094613 / 250000000)) (hi := (668378453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951071 / 1000000) = 1/(1000000 / 1951071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167094613 / 250000000) (668378453 / 1000000000) (Real.log (1951071 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1951071 / 1000000) = -Real.log (1000000 / 1951071) := by
    rw [show ((1951071 / 1000000) : ℝ) = ((1000000 / 1951071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3017385009 / 1000000000) ≤ -Real.log (48929 / 1000000) ∧
    -Real.log (48929 / 1000000) ≤ (1508692507 / 500000000) := by
  have h := checkLog_sound (w := (13571 / 111429)) (n := 12)
    (lo := (244796289 / 1000000000)) (hi := (24479629 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48929) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 48929) = 1/(48929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1508692507 / 500000000) (-3017385009 / 1000000000) (Real.log (48929 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334336047 / 500000000) ≤ -Real.log (250000 / 487911) ∧
    -Real.log (250000 / 487911) ≤ (133734419 / 200000000) := by
  have h := checkLog_sound (w := (237911 / 737911)) (n := 12)
    (lo := (334336047 / 500000000)) (hi := (133734419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487911 / 250000) = 1/(250000 / 487911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334336047 / 500000000) (133734419 / 200000000) (Real.log (487911 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (487911 / 250000) = -Real.log (250000 / 487911) := by
    rw [show ((487911 / 250000) : ℝ) = ((250000 / 487911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3029164967 / 1000000000) ≤ -Real.log (12089 / 250000) ∧
    -Real.log (12089 / 250000) ≤ (757291243 / 250000000) := by
  have h := checkLog_sound (w := (1768 / 13857)) (n := 12)
    (lo := (256576247 / 1000000000)) (hi := (32072031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12089) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12089) = 1/(12089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-757291243 / 250000000) (-3029164967 / 1000000000) (Real.log (12089 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1850574139 / 500000000) ≤ -Real.log (125000000000 / 5061721991701) ∧
    -Real.log (125000000000 / 5061721991701) ≤ (925287071 / 250000000) := by
  have h := checkLog_sound (w := (1061721991701 / 9061721991701)) (n := 12)
    (lo := (117706189 / 500000000)) (hi := (235412379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5061721991701 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5061721991701 / 4000000000000) = 1/(125000000000 / 5061721991701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1850574139 / 500000000) (925287071 / 250000000) (Real.log (5061721991701 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5061721991701 / 125000000000) = -Real.log (125000000000 / 5061721991701) := by
    rw [show ((5061721991701 / 125000000000) : ℝ) = ((125000000000 / 5061721991701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1856485459 / 500000000) ≤ -Real.log (62500000000 / 2560960028963) ∧
    -Real.log (62500000000 / 2560960028963) ≤ (928242731 / 250000000) := by
  have h := checkLog_sound (w := (560960028963 / 4560960028963)) (n := 12)
    (lo := (123617509 / 500000000)) (hi := (247235019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560960028963 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2560960028963 / 2000000000000) = 1/(62500000000 / 2560960028963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1856485459 / 500000000) (928242731 / 250000000) (Real.log (2560960028963 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2560960028963 / 62500000000) = -Real.log (62500000000 / 2560960028963) := by
    rw [show ((2560960028963 / 62500000000) : ℝ) = ((62500000000 / 2560960028963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3685763461 / 1000000000) ≤ -Real.log (500000000000 / 19937777187353) ∧
    -Real.log (500000000000 / 19937777187353) ≤ (3685763467 / 1000000000) := by
  have h := checkLog_sound (w := (3937777187353 / 35937777187353)) (n := 12)
    (lo := (220027561 / 1000000000)) (hi := (110013781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19937777187353 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19937777187353 / 16000000000000) = 1/(500000000000 / 19937777187353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3685763461 / 1000000000) (3685763467 / 1000000000) (Real.log (19937777187353 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19937777187353 / 500000000000) = -Real.log (500000000000 / 19937777187353) := by
    rw [show ((19937777187353 / 500000000000) : ℝ) = ((500000000000 / 19937777187353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3697837061 / 1000000000) ≤ -Real.log (50000000000 / 2017995698569) ∧
    -Real.log (50000000000 / 2017995698569) ≤ (3697837067 / 1000000000) := by
  have h := checkLog_sound (w := (417995698569 / 3617995698569)) (n := 12)
    (lo := (232101161 / 1000000000)) (hi := (116050581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017995698569 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2017995698569 / 1600000000000) = 1/(50000000000 / 2017995698569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3697837061 / 1000000000) (3697837067 / 1000000000) (Real.log (2017995698569 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2017995698569 / 50000000000) = -Real.log (50000000000 / 2017995698569) := by
    rw [show ((2017995698569 / 50000000000) : ℝ) = ((50000000000 / 2017995698569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0128
