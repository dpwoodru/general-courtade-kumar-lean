import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0090
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

theorem reflection_log_1_neg : (336651573 / 500000000) ≤ -Real.log (12800 / 25097) ∧
    -Real.log (12800 / 25097) ≤ (673303147 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 37897)) (n := 12)
    (lo := (336651573 / 500000000)) (hi := (673303147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25097 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25097 / 12800) = 1/(12800 / 25097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336651573 / 500000000) (673303147 / 1000000000) (Real.log (25097 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25097 / 12800) = -Real.log (12800 / 25097) := by
    rw [show ((25097 / 12800) : ℝ) = ((12800 / 25097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3236610277 / 1000000000) ≤ -Real.log (503 / 12800) ∧
    -Real.log (503 / 12800) ≤ (1618305141 / 500000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 503) = 1/(503 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1618305141 / 500000000) (-3236610277 / 1000000000) (Real.log (503 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336556931 / 500000000) ≤ -Real.log (51200 / 100369) ∧
    -Real.log (51200 / 100369) ≤ (673113863 / 1000000000) := by
  have h := checkLog_sound (w := (49169 / 151569)) (n := 12)
    (lo := (336556931 / 500000000)) (hi := (673113863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100369 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100369 / 51200) = 1/(51200 / 100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336556931 / 500000000) (673113863 / 1000000000) (Real.log (100369 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100369 / 51200) = -Real.log (51200 / 100369) := by
    rw [show ((100369 / 51200) : ℝ) = ((51200 / 100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3227211247 / 1000000000) ≤ -Real.log (2031 / 51200) ∧
    -Real.log (2031 / 51200) ≤ (806802813 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2031) = 1/(2031 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-806802813 / 250000000) (-3227211247 / 1000000000) (Real.log (2031 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653057339 / 1000000000) ≤ -Real.log (6400 / 12297) ∧
    -Real.log (6400 / 12297) ≤ (32652867 / 50000000) := by
  have h := checkLog_sound (w := (5897 / 18697)) (n := 12)
    (lo := (653057339 / 1000000000)) (hi := (32652867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 6400) = 1/(6400 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653057339 / 1000000000) (32652867 / 50000000) (Real.log (12297 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12297 / 6400) = -Real.log (6400 / 12297) := by
    rw [show ((12297 / 6400) : ℝ) = ((6400 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2543463097 / 1000000000) ≤ -Real.log (503 / 6400) ∧
    -Real.log (503 / 6400) ≤ (2543463101 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 503) = 1/(503 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2543463101 / 1000000000) (-2543463097 / 1000000000) (Real.log (503 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40791937 / 62500000) ≤ -Real.log (25600 / 49169) ∧
    -Real.log (25600 / 49169) ≤ (652670993 / 1000000000) := by
  have h := checkLog_sound (w := (23569 / 74769)) (n := 12)
    (lo := (40791937 / 62500000)) (hi := (652670993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49169 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49169 / 25600) = 1/(25600 / 49169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40791937 / 62500000) (652670993 / 1000000000) (Real.log (49169 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49169 / 25600) = -Real.log (25600 / 49169) := by
    rw [show ((49169 / 25600) : ℝ) = ((25600 / 49169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2534064067 / 1000000000) ≤ -Real.log (2031 / 25600) ∧
    -Real.log (2031 / 25600) ≤ (2534064071 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2031) = 1/(2031 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2534064071 / 1000000000) (-2534064067 / 1000000000) (Real.log (2031 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169167163 / 250000000) ≤ -Real.log (1000000 / 1967313) ∧
    -Real.log (1000000 / 1967313) ≤ (676668653 / 1000000000) := by
  have h := checkLog_sound (w := (967313 / 2967313)) (n := 12)
    (lo := (169167163 / 250000000)) (hi := (676668653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967313 / 1000000) = 1/(1000000 / 1967313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169167163 / 250000000) (676668653 / 1000000000) (Real.log (1967313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1967313 / 1000000) = -Real.log (1000000 / 1967313) := by
    rw [show ((1967313 / 1000000) : ℝ) = ((1000000 / 1967313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3420777831 / 1000000000) ≤ -Real.log (32687 / 1000000) ∧
    -Real.log (32687 / 1000000) ≤ (855194459 / 250000000) := by
  have h := checkLog_sound (w := (29813 / 95187)) (n := 12)
    (lo := (648189111 / 1000000000)) (hi := (81023639 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32687) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32687) = 1/(32687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-855194459 / 250000000) (-3420777831 / 1000000000) (Real.log (32687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13536321 / 20000000) ≤ -Real.log (1000000 / 1967603) ∧
    -Real.log (1000000 / 1967603) ≤ (676816051 / 1000000000) := by
  have h := checkLog_sound (w := (967603 / 2967603)) (n := 12)
    (lo := (13536321 / 20000000)) (hi := (676816051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967603 / 1000000) = 1/(1000000 / 1967603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13536321 / 20000000) (676816051 / 1000000000) (Real.log (1967603 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1967603 / 1000000) = -Real.log (1000000 / 1967603) := by
    rw [show ((1967603 / 1000000) : ℝ) = ((1000000 / 1967603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (68593789 / 20000000) ≤ -Real.log (32397 / 1000000) ∧
    -Real.log (32397 / 1000000) ≤ (685937891 / 200000000) := by
  have h := checkLog_sound (w := (30103 / 94897)) (n := 12)
    (lo := (65710073 / 100000000)) (hi := (657100731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32397) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32397) = 1/(32397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-685937891 / 200000000) (-68593789 / 20000000) (Real.log (32397 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338262141 / 500000000) ≤ -Real.log (1000000 / 1967029) ∧
    -Real.log (1000000 / 1967029) ≤ (676524283 / 1000000000) := by
  have h := checkLog_sound (w := (967029 / 2967029)) (n := 12)
    (lo := (338262141 / 500000000)) (hi := (676524283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967029 / 1000000) = 1/(1000000 / 1967029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338262141 / 500000000) (676524283 / 1000000000) (Real.log (1967029 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1967029 / 1000000) = -Real.log (1000000 / 1967029) := by
    rw [show ((1967029 / 1000000) : ℝ) = ((1000000 / 1967029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3412126889 / 1000000000) ≤ -Real.log (32971 / 1000000) ∧
    -Real.log (32971 / 1000000) ≤ (1706063447 / 500000000) := by
  have h := checkLog_sound (w := (29529 / 95471)) (n := 12)
    (lo := (639538169 / 1000000000)) (hi := (63953817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32971) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32971) = 1/(32971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1706063447 / 500000000) (-3412126889 / 1000000000) (Real.log (32971 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676674751 / 1000000000) ≤ -Real.log (40000 / 78693) ∧
    -Real.log (40000 / 78693) ≤ (10573043 / 15625000) := by
  have h := checkLog_sound (w := (38693 / 118693)) (n := 12)
    (lo := (676674751 / 1000000000)) (hi := (10573043 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78693 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78693 / 40000) = 1/(40000 / 78693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676674751 / 1000000000) (10573043 / 15625000) (Real.log (78693 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78693 / 40000) = -Real.log (40000 / 78693) := by
    rw [show ((78693 / 40000) : ℝ) = ((40000 / 78693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3421145017 / 1000000000) ≤ -Real.log (1307 / 40000) ∧
    -Real.log (1307 / 40000) ≤ (1710572511 / 500000000) := by
  have h := checkLog_sound (w := (1193 / 3807)) (n := 12)
    (lo := (648556297 / 1000000000)) (hi := (324278149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1307) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1307) = 1/(1307 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1710572511 / 500000000) (-3421145017 / 1000000000) (Real.log (1307 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4097446483 / 1000000000) ≤ -Real.log (500000000000 / 30093202190473) ∧
    -Real.log (500000000000 / 30093202190473) ≤ (4097446489 / 1000000000) := by
  have h := checkLog_sound (w := (14093202190473 / 46093202190473)) (n := 12)
    (lo := (631710583 / 1000000000)) (hi := (78963823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30093202190473 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30093202190473 / 16000000000000) = 1/(500000000000 / 30093202190473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4097446483 / 1000000000) (4097446489 / 1000000000) (Real.log (30093202190473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (30093202190473 / 500000000000) = -Real.log (500000000000 / 30093202190473) := by
    rw [show ((30093202190473 / 500000000000) : ℝ) = ((500000000000 / 30093202190473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8213011 / 2000000) ≤ -Real.log (31250000000 / 1897940974473) ∧
    -Real.log (31250000000 / 1897940974473) ≤ (2053252753 / 500000000) := by
  have h := checkLog_sound (w := (897940974473 / 2897940974473)) (n := 12)
    (lo := (400481 / 625000)) (hi := (640769601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897940974473 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1897940974473 / 1000000000000) = 1/(31250000000 / 1897940974473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8213011 / 2000000) (2053252753 / 500000000) (Real.log (1897940974473 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1897940974473 / 31250000000) = -Real.log (31250000000 / 1897940974473) := by
    rw [show ((1897940974473 / 31250000000) : ℝ) = ((31250000000 / 1897940974473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4088651171 / 1000000000) ≤ -Real.log (500000000000 / 29829683661399) ∧
    -Real.log (500000000000 / 29829683661399) ≤ (4088651177 / 1000000000) := by
  have h := checkLog_sound (w := (13829683661399 / 45829683661399)) (n := 12)
    (lo := (622915271 / 1000000000)) (hi := (77864409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29829683661399 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29829683661399 / 16000000000000) = 1/(500000000000 / 29829683661399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4088651171 / 1000000000) (4088651177 / 1000000000) (Real.log (29829683661399 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (29829683661399 / 500000000000) = -Real.log (500000000000 / 29829683661399) := by
    rw [show ((29829683661399 / 500000000000) : ℝ) = ((500000000000 / 29829683661399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (512227471 / 125000000) ≤ -Real.log (500000000000 / 30104437643459) ∧
    -Real.log (500000000000 / 30104437643459) ≤ (2048909887 / 500000000) := by
  have h := checkLog_sound (w := (14104437643459 / 46104437643459)) (n := 12)
    (lo := (158020967 / 250000000)) (hi := (632083869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30104437643459 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30104437643459 / 16000000000000) = 1/(500000000000 / 30104437643459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (512227471 / 125000000) (2048909887 / 500000000) (Real.log (30104437643459 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30104437643459 / 500000000000) = -Real.log (500000000000 / 30104437643459) := by
    rw [show ((30104437643459 / 500000000000) : ℝ) = ((500000000000 / 30104437643459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0090
