import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062
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

theorem reflection_log_1_neg : (169482359 / 250000000) ≤ -Real.log (102400 / 201707) ∧
    -Real.log (102400 / 201707) ≤ (677929437 / 1000000000) := by
  have h := checkLog_sound (w := (99307 / 304107)) (n := 12)
    (lo := (169482359 / 250000000)) (hi := (677929437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201707 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201707 / 102400) = 1/(102400 / 201707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169482359 / 250000000) (677929437 / 1000000000) (Real.log (201707 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201707 / 102400) = -Real.log (102400 / 201707) := by
    rw [show ((201707 / 102400) : ℝ) = ((102400 / 201707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (54683519 / 15625000) ≤ -Real.log (3093 / 102400) ∧
    -Real.log (3093 / 102400) ≤ (1749872611 / 500000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3093) = 1/(3093 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1749872611 / 500000000) (-54683519 / 15625000) (Real.log (3093 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169458809 / 250000000) ≤ -Real.log (12800 / 25211) ∧
    -Real.log (12800 / 25211) ≤ (677835237 / 1000000000) := by
  have h := checkLog_sound (w := (12411 / 38011)) (n := 12)
    (lo := (169458809 / 250000000)) (hi := (677835237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25211 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25211 / 12800) = 1/(12800 / 25211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169458809 / 250000000) (677835237 / 1000000000) (Real.log (25211 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25211 / 12800) = -Real.log (12800 / 25211) := by
    rw [show ((25211 / 12800) : ℝ) = ((12800 / 25211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3493621103 / 1000000000) ≤ -Real.log (389 / 12800) ∧
    -Real.log (389 / 12800) ≤ (3493621109 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 389) = 1/(389 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3493621109 / 1000000000) (-3493621103 / 1000000000) (Real.log (389 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (662476529 / 1000000000) ≤ -Real.log (51200 / 99307) ∧
    -Real.log (51200 / 99307) ≤ (66247653 / 100000000) := by
  have h := checkLog_sound (w := (48107 / 150507)) (n := 12)
    (lo := (662476529 / 1000000000)) (hi := (66247653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99307 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99307 / 51200) = 1/(51200 / 99307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (662476529 / 1000000000) (66247653 / 100000000) (Real.log (99307 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99307 / 51200) = -Real.log (51200 / 99307) := by
    rw [show ((99307 / 51200) : ℝ) = ((51200 / 99307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (701649509 / 250000000) ≤ -Real.log (3093 / 51200) ∧
    -Real.log (3093 / 51200) ≤ (2806598041 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3093) = 1/(3093 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2806598041 / 1000000000) (-701649509 / 250000000) (Real.log (3093 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132457037 / 200000000) ≤ -Real.log (6400 / 12411) ∧
    -Real.log (6400 / 12411) ≤ (331142593 / 500000000) := by
  have h := checkLog_sound (w := (6011 / 18811)) (n := 12)
    (lo := (132457037 / 200000000)) (hi := (331142593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 6400) = 1/(6400 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132457037 / 200000000) (331142593 / 500000000) (Real.log (12411 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12411 / 6400) = -Real.log (6400 / 12411) := by
    rw [show ((12411 / 6400) : ℝ) = ((6400 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2800473923 / 1000000000) ≤ -Real.log (389 / 6400) ∧
    -Real.log (389 / 6400) ≤ (350059241 / 125000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 389) = 1/(389 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-350059241 / 125000000) (-2800473923 / 1000000000) (Real.log (389 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170092601 / 250000000) ≤ -Real.log (1000000 / 1974609) ∧
    -Real.log (1000000 / 1974609) ≤ (136074081 / 200000000) := by
  have h := checkLog_sound (w := (974609 / 2974609)) (n := 12)
    (lo := (170092601 / 250000000)) (hi := (136074081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974609 / 1000000) = 1/(1000000 / 1974609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170092601 / 250000000) (136074081 / 200000000) (Real.log (1974609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974609 / 1000000) = -Real.log (1000000 / 1974609) := by
    rw [show ((1974609 / 1000000) : ℝ) = ((1000000 / 1974609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (734672099 / 200000000) ≤ -Real.log (25391 / 1000000) ∧
    -Real.log (25391 / 1000000) ≤ (3673360501 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 56641)) (n := 12)
    (lo := (41524919 / 200000000)) (hi := (51906149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25391) = 1/(25391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3673360501 / 1000000000) (-734672099 / 200000000) (Real.log (25391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680445859 / 1000000000) ≤ -Real.log (500000 / 987379) ∧
    -Real.log (500000 / 987379) ≤ (34022293 / 50000000) := by
  have h := checkLog_sound (w := (487379 / 1487379)) (n := 12)
    (lo := (680445859 / 1000000000)) (hi := (34022293 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987379 / 500000) = 1/(500000 / 987379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680445859 / 1000000000) (34022293 / 50000000) (Real.log (987379 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (987379 / 500000) = -Real.log (500000 / 987379) := by
    rw [show ((987379 / 500000) : ℝ) = ((500000 / 987379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1839623001 / 500000000) ≤ -Real.log (12621 / 500000) ∧
    -Real.log (12621 / 500000) ≤ (459905751 / 125000000) := by
  have h := checkLog_sound (w := (1502 / 14123)) (n := 12)
    (lo := (106755051 / 500000000)) (hi := (213510103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12621) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12621) = 1/(12621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-459905751 / 125000000) (-1839623001 / 500000000) (Real.log (12621 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680291397 / 1000000000) ≤ -Real.log (1000000 / 1974453) ∧
    -Real.log (1000000 / 1974453) ≤ (340145699 / 500000000) := by
  have h := checkLog_sound (w := (974453 / 2974453)) (n := 12)
    (lo := (680291397 / 1000000000)) (hi := (340145699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974453 / 1000000) = 1/(1000000 / 1974453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680291397 / 1000000000) (340145699 / 500000000) (Real.log (1974453 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974453 / 1000000) = -Real.log (1000000 / 1974453) := by
    rw [show ((1974453 / 1000000) : ℝ) = ((1000000 / 1974453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3667235383 / 1000000000) ≤ -Real.log (25547 / 1000000) ∧
    -Real.log (25547 / 1000000) ≤ (3667235389 / 1000000000) := by
  have h := checkLog_sound (w := (5703 / 56797)) (n := 12)
    (lo := (201499483 / 1000000000)) (hi := (50374871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25547) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25547) = 1/(25547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3667235389 / 1000000000) (-3667235383 / 1000000000) (Real.log (25547 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136073473 / 200000000) ≤ -Real.log (1000000 / 1974603) ∧
    -Real.log (1000000 / 1974603) ≤ (340183683 / 500000000) := by
  have h := checkLog_sound (w := (974603 / 2974603)) (n := 12)
    (lo := (136073473 / 200000000)) (hi := (340183683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974603 / 1000000) = 1/(1000000 / 1974603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136073473 / 200000000) (340183683 / 500000000) (Real.log (1974603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974603 / 1000000) = -Real.log (1000000 / 1974603) := by
    rw [show ((1974603 / 1000000) : ℝ) = ((1000000 / 1974603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3673124219 / 1000000000) ≤ -Real.log (25397 / 1000000) ∧
    -Real.log (25397 / 1000000) ≤ (146924969 / 40000000) := by
  have h := checkLog_sound (w := (5853 / 56647)) (n := 12)
    (lo := (207388319 / 1000000000)) (hi := (1296177 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25397) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25397) = 1/(25397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-146924969 / 40000000) (-3673124219 / 1000000000) (Real.log (25397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4353730899 / 1000000000) ≤ -Real.log (125000000000 / 9721008428183) ∧
    -Real.log (125000000000 / 9721008428183) ≤ (2176865453 / 500000000) := by
  have h := checkLog_sound (w := (1721008428183 / 17721008428183)) (n := 12)
    (lo := (194847819 / 1000000000)) (hi := (9742391 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9721008428183 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9721008428183 / 8000000000000) = 1/(125000000000 / 9721008428183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4353730899 / 1000000000) (2176865453 / 500000000) (Real.log (9721008428183 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9721008428183 / 125000000000) = -Real.log (125000000000 / 9721008428183) := by
    rw [show ((9721008428183 / 125000000000) : ℝ) = ((125000000000 / 9721008428183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (217984593 / 50000000) ≤ -Real.log (50000000000 / 3911651216227) ∧
    -Real.log (50000000000 / 3911651216227) ≤ (4359691867 / 1000000000) := by
  have h := checkLog_sound (w := (711651216227 / 7111651216227)) (n := 12)
    (lo := (10040439 / 50000000)) (hi := (200808781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911651216227 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3911651216227 / 3200000000000) = 1/(50000000000 / 3911651216227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (217984593 / 50000000) (4359691867 / 1000000000) (Real.log (3911651216227 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3911651216227 / 50000000000) = -Real.log (50000000000 / 3911651216227) := by
    rw [show ((3911651216227 / 50000000000) : ℝ) = ((50000000000 / 3911651216227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217376339 / 50000000) ≤ -Real.log (125000000000 / 9660884839707) ∧
    -Real.log (125000000000 / 9660884839707) ≤ (4347526787 / 1000000000) := by
  have h := checkLog_sound (w := (1660884839707 / 17660884839707)) (n := 12)
    (lo := (1886437 / 10000000)) (hi := (188643701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9660884839707 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9660884839707 / 8000000000000) = 1/(125000000000 / 9660884839707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217376339 / 50000000) (4347526787 / 1000000000) (Real.log (9660884839707 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9660884839707 / 125000000000) = -Real.log (125000000000 / 9660884839707) := by
    rw [show ((9660884839707 / 125000000000) : ℝ) = ((125000000000 / 9660884839707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (34011653 / 7812500) ≤ -Real.log (500000000000 / 38874729298737) ∧
    -Real.log (500000000000 / 38874729298737) ≤ (4353491591 / 1000000000) := by
  have h := checkLog_sound (w := (6874729298737 / 70874729298737)) (n := 12)
    (lo := (24326063 / 125000000)) (hi := (38921701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38874729298737 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38874729298737 / 32000000000000) = 1/(500000000000 / 38874729298737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (34011653 / 7812500) (4353491591 / 1000000000) (Real.log (38874729298737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38874729298737 / 500000000000) = -Real.log (500000000000 / 38874729298737) := by
    rw [show ((38874729298737 / 500000000000) : ℝ) = ((500000000000 / 38874729298737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062
