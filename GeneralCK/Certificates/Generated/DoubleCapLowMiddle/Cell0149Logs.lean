import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0149
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

theorem reflection_log_1_neg : (654195181 / 1000000000) ≤ -Real.log (6400 / 12311) ∧
    -Real.log (6400 / 12311) ≤ (327097591 / 500000000) := by
  have h := checkLog_sound (w := (5911 / 18711)) (n := 12)
    (lo := (654195181 / 1000000000)) (hi := (327097591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12311 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12311 / 6400) = 1/(6400 / 12311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (654195181 / 1000000000) (327097591 / 500000000) (Real.log (12311 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12311 / 6400) = -Real.log (6400 / 12311) := by
    rw [show ((12311 / 6400) : ℝ) = ((6400 / 12311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1285845389 / 500000000) ≤ -Real.log (489 / 6400) ∧
    -Real.log (489 / 6400) ≤ (1285845391 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 489) = 1/(489 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1285845391 / 500000000) (-1285845389 / 500000000) (Real.log (489 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130684643 / 200000000) ≤ -Real.log (12800 / 24603) ∧
    -Real.log (12800 / 24603) ≤ (40838951 / 62500000) := by
  have h := checkLog_sound (w := (11803 / 37403)) (n := 12)
    (lo := (130684643 / 200000000)) (hi := (40838951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 12800) = 1/(12800 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130684643 / 200000000) (40838951 / 62500000) (Real.log (24603 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24603 / 12800) = -Real.log (12800 / 24603) := by
    rw [show ((24603 / 12800) : ℝ) = ((12800 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1276224839 / 500000000) ≤ -Real.log (997 / 12800) ∧
    -Real.log (997 / 12800) ≤ (1276224841 / 500000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 997) = 1/(997 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1276224841 / 500000000) (-1276224839 / 500000000) (Real.log (997 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (153416053 / 250000000) ≤ -Real.log (3200 / 5911) ∧
    -Real.log (3200 / 5911) ≤ (613664213 / 1000000000) := by
  have h := checkLog_sound (w := (2711 / 9111)) (n := 12)
    (lo := (153416053 / 250000000)) (hi := (613664213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5911 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5911 / 3200) = 1/(3200 / 5911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (153416053 / 250000000) (613664213 / 1000000000) (Real.log (5911 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5911 / 3200) = -Real.log (3200 / 5911) := by
    rw [show ((5911 / 3200) : ℝ) = ((3200 / 5911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (939271799 / 500000000) ≤ -Real.log (489 / 3200) ∧
    -Real.log (489 / 3200) ≤ (1878543601 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 489) = 1/(489 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1878543601 / 1000000000) (-939271799 / 500000000) (Real.log (489 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (306027873 / 500000000) ≤ -Real.log (6400 / 11803) ∧
    -Real.log (6400 / 11803) ≤ (612055747 / 1000000000) := by
  have h := checkLog_sound (w := (5403 / 18203)) (n := 12)
    (lo := (306027873 / 500000000)) (hi := (612055747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 6400) = 1/(6400 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (306027873 / 500000000) (612055747 / 1000000000) (Real.log (11803 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11803 / 6400) = -Real.log (6400 / 11803) := by
    rw [show ((11803 / 6400) : ℝ) = ((6400 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (929651249 / 500000000) ≤ -Real.log (997 / 6400) ∧
    -Real.log (997 / 6400) ≤ (1859302501 / 1000000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 997) = 1/(997 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1859302501 / 1000000000) (-929651249 / 500000000) (Real.log (997 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (662077477 / 1000000000) ≤ -Real.log (15625 / 30294) ∧
    -Real.log (15625 / 30294) ≤ (331038739 / 500000000) := by
  have h := checkLog_sound (w := (14669 / 45919)) (n := 12)
    (lo := (662077477 / 1000000000)) (hi := (331038739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30294 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30294 / 15625) = 1/(15625 / 30294) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (662077477 / 1000000000) (331038739 / 500000000) (Real.log (30294 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (30294 / 15625) = -Real.log (15625 / 30294) := by
    rw [show ((30294 / 15625) : ℝ) = ((15625 / 30294) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2793869559 / 1000000000) ≤ -Real.log (956 / 15625) ∧
    -Real.log (956 / 15625) ≤ (698467391 / 250000000) := by
  have h := checkLog_sound (w := (329 / 30921)) (n := 12)
    (lo := (21280839 / 1000000000)) (hi := (532021 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15296) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15296) = 1/(956 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-698467391 / 250000000) (-2793869559 / 1000000000) (Real.log (956 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132525223 / 200000000) ≤ -Real.log (25000 / 48497) ∧
    -Real.log (25000 / 48497) ≤ (165656529 / 250000000) := by
  have h := checkLog_sound (w := (23497 / 73497)) (n := 12)
    (lo := (132525223 / 200000000)) (hi := (165656529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48497 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48497 / 25000) = 1/(25000 / 48497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132525223 / 200000000) (165656529 / 250000000) (Real.log (48497 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (48497 / 25000) = -Real.log (25000 / 48497) := by
    rw [show ((48497 / 25000) : ℝ) = ((25000 / 48497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2811412711 / 1000000000) ≤ -Real.log (1503 / 25000) ∧
    -Real.log (1503 / 25000) ≤ (702853179 / 250000000) := by
  have h := checkLog_sound (w := (119 / 6131)) (n := 12)
    (lo := (38823991 / 1000000000)) (hi := (4852999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3006) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 3006) = 1/(1503 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-702853179 / 250000000) (-2811412711 / 1000000000) (Real.log (1503 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (661393837 / 1000000000) ≤ -Real.log (1000000 / 1937491) ∧
    -Real.log (1000000 / 1937491) ≤ (330696919 / 500000000) := by
  have h := checkLog_sound (w := (937491 / 2937491)) (n := 12)
    (lo := (661393837 / 1000000000)) (hi := (330696919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1937491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1937491 / 1000000) = 1/(1000000 / 1937491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (661393837 / 1000000000) (330696919 / 500000000) (Real.log (1937491 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1937491 / 1000000) = -Real.log (1000000 / 1937491) := by
    rw [show ((1937491 / 1000000) : ℝ) = ((1000000 / 1937491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (277244473 / 100000000) ≤ -Real.log (62509 / 1000000) ∧
    -Real.log (62509 / 1000000) ≤ (1386222367 / 500000000) := by
  have h := checkLog_sound (w := (62491 / 187509)) (n := 12)
    (lo := (69300319 / 100000000)) (hi := (693003191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 62509) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 62509) = 1/(62509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1386222367 / 500000000) (-277244473 / 100000000) (Real.log (62509 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20686649 / 31250000) ≤ -Real.log (1000000 / 1938613) ∧
    -Real.log (1000000 / 1938613) ≤ (661972769 / 1000000000) := by
  have h := checkLog_sound (w := (938613 / 2938613)) (n := 12)
    (lo := (20686649 / 31250000)) (hi := (661972769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1938613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1938613 / 1000000) = 1/(1000000 / 1938613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20686649 / 31250000) (661972769 / 1000000000) (Real.log (1938613 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1938613 / 1000000) = -Real.log (1000000 / 1938613) := by
    rw [show ((1938613 / 1000000) : ℝ) = ((1000000 / 1938613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279055719 / 100000000) ≤ -Real.log (61387 / 1000000) ∧
    -Real.log (61387 / 1000000) ≤ (558111439 / 200000000) := by
  have h := checkLog_sound (w := (1113 / 123887)) (n := 12)
    (lo := (1796847 / 100000000)) (hi := (17968471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61387) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 61387) = 1/(61387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-558111439 / 200000000) (-279055719 / 100000000) (Real.log (61387 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (863986759 / 250000000) ≤ -Real.log (250000000000 / 7922071129707) ∧
    -Real.log (250000000000 / 7922071129707) ≤ (3455947041 / 1000000000) := by
  have h := checkLog_sound (w := (3922071129707 / 11922071129707)) (n := 12)
    (lo := (170839579 / 250000000)) (hi := (683358317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7922071129707 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7922071129707 / 4000000000000) = 1/(250000000000 / 7922071129707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (863986759 / 250000000) (3455947041 / 1000000000) (Real.log (7922071129707 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7922071129707 / 250000000000) = -Real.log (250000000000 / 7922071129707) := by
    rw [show ((7922071129707 / 250000000000) : ℝ) = ((250000000000 / 7922071129707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1737019413 / 500000000) ≤ -Real.log (500000000000 / 16133399866933) ∧
    -Real.log (500000000000 / 16133399866933) ≤ (217127427 / 62500000) := by
  have h := checkLog_sound (w := (133399866933 / 32133399866933)) (n := 12)
    (lo := (4151463 / 500000000)) (hi := (8302927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16133399866933 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16133399866933 / 16000000000000) = 1/(500000000000 / 16133399866933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1737019413 / 500000000) (217127427 / 62500000) (Real.log (16133399866933 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16133399866933 / 500000000000) = -Real.log (500000000000 / 16133399866933) := by
    rw [show ((16133399866933 / 500000000000) : ℝ) = ((500000000000 / 16133399866933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3433838567 / 1000000000) ≤ -Real.log (31250000000 / 968606020733) ∧
    -Real.log (31250000000 / 968606020733) ≤ (858459643 / 250000000) := by
  have h := checkLog_sound (w := (468606020733 / 1468606020733)) (n := 12)
    (lo := (661249847 / 1000000000)) (hi := (82656231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968606020733 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(968606020733 / 500000000000) = 1/(31250000000 / 968606020733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3433838567 / 1000000000) (858459643 / 250000000) (Real.log (968606020733 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (968606020733 / 31250000000) = -Real.log (31250000000 / 968606020733) := by
    rw [show ((968606020733 / 31250000000) : ℝ) = ((31250000000 / 968606020733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3452529959 / 1000000000) ≤ -Real.log (500000000000 / 15790093993843) ∧
    -Real.log (500000000000 / 15790093993843) ≤ (863132491 / 250000000) := by
  have h := checkLog_sound (w := (7790093993843 / 23790093993843)) (n := 12)
    (lo := (679941239 / 1000000000)) (hi := (16998531 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15790093993843 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15790093993843 / 8000000000000) = 1/(500000000000 / 15790093993843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3452529959 / 1000000000) (863132491 / 250000000) (Real.log (15790093993843 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (15790093993843 / 500000000000) = -Real.log (500000000000 / 15790093993843) := by
    rw [show ((15790093993843 / 500000000000) : ℝ) = ((500000000000 / 15790093993843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0149
