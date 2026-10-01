import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0133
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

theorem reflection_log_1_neg : (82639523 / 125000000) ≤ -Real.log (12800 / 24793) ∧
    -Real.log (12800 / 24793) ≤ (132223237 / 200000000) := by
  have h := checkLog_sound (w := (11993 / 37593)) (n := 12)
    (lo := (82639523 / 125000000)) (hi := (132223237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24793 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24793 / 12800) = 1/(12800 / 24793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82639523 / 125000000) (132223237 / 200000000) (Real.log (24793 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24793 / 12800) = -Real.log (12800 / 24793) := by
    rw [show ((24793 / 12800) : ℝ) = ((12800 / 24793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2763876779 / 1000000000) ≤ -Real.log (807 / 12800) ∧
    -Real.log (807 / 12800) ≤ (2763876783 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 807) = 1/(807 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2763876783 / 1000000000) (-2763876779 / 1000000000) (Real.log (807 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (330366469 / 500000000) ≤ -Real.log (25600 / 49567) ∧
    -Real.log (25600 / 49567) ≤ (660732939 / 1000000000) := by
  have h := checkLog_sound (w := (23967 / 75167)) (n := 12)
    (lo := (330366469 / 500000000)) (hi := (660732939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49567 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49567 / 25600) = 1/(25600 / 49567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (330366469 / 500000000) (660732939 / 1000000000) (Real.log (49567 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49567 / 25600) = -Real.log (25600 / 49567) := by
    rw [show ((49567 / 25600) : ℝ) = ((25600 / 49567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (550434707 / 200000000) ≤ -Real.log (1633 / 25600) ∧
    -Real.log (1633 / 25600) ≤ (2752173539 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1633) = 1/(1633 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2752173539 / 1000000000) (-550434707 / 200000000) (Real.log (1633 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (125605031 / 200000000) ≤ -Real.log (6400 / 11993) ∧
    -Real.log (6400 / 11993) ≤ (157006289 / 250000000) := by
  have h := checkLog_sound (w := (5593 / 18393)) (n := 12)
    (lo := (125605031 / 200000000)) (hi := (157006289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 6400) = 1/(6400 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (125605031 / 200000000) (157006289 / 250000000) (Real.log (11993 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11993 / 6400) = -Real.log (6400 / 11993) := by
    rw [show ((11993 / 6400) : ℝ) = ((6400 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2070729599 / 1000000000) ≤ -Real.log (807 / 6400) ∧
    -Real.log (807 / 6400) ≤ (1035364801 / 500000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 807) = 1/(807 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1035364801 / 500000000) (-2070729599 / 1000000000) (Real.log (807 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (627232713 / 1000000000) ≤ -Real.log (12800 / 23967) ∧
    -Real.log (12800 / 23967) ≤ (313616357 / 500000000) := by
  have h := checkLog_sound (w := (11167 / 36767)) (n := 12)
    (lo := (627232713 / 1000000000)) (hi := (313616357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23967 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23967 / 12800) = 1/(12800 / 23967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (627232713 / 1000000000) (313616357 / 500000000) (Real.log (23967 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23967 / 12800) = -Real.log (12800 / 23967) := by
    rw [show ((23967 / 12800) : ℝ) = ((12800 / 23967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (411805271 / 200000000) ≤ -Real.log (1633 / 12800) ∧
    -Real.log (1633 / 12800) ≤ (1029513179 / 500000000) := by
  have h := checkLog_sound (w := (1567 / 4833)) (n := 12)
    (lo := (134546399 / 200000000)) (hi := (168182999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1633) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1633) = 1/(1633 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1029513179 / 500000000) (-411805271 / 200000000) (Real.log (1633 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333672063 / 500000000) ≤ -Real.log (500000 / 974527) ∧
    -Real.log (500000 / 974527) ≤ (667344127 / 1000000000) := by
  have h := checkLog_sound (w := (474527 / 1474527)) (n := 12)
    (lo := (333672063 / 500000000)) (hi := (667344127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974527 / 500000) = 1/(500000 / 974527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333672063 / 500000000) (667344127 / 1000000000) (Real.log (974527 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (974527 / 500000) = -Real.log (500000 / 974527) := by
    rw [show ((974527 / 500000) : ℝ) = ((500000 / 974527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (744247257 / 250000000) ≤ -Real.log (25473 / 500000) ∧
    -Real.log (25473 / 500000) ≤ (2976989033 / 1000000000) := by
  have h := checkLog_sound (w := (5777 / 56723)) (n := 12)
    (lo := (51100077 / 250000000)) (hi := (204400309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25473) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25473) = 1/(25473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2976989033 / 1000000000) (-744247257 / 250000000) (Real.log (25473 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (333812881 / 500000000) ≤ -Real.log (1000000 / 1949603) ∧
    -Real.log (1000000 / 1949603) ≤ (667625763 / 1000000000) := by
  have h := checkLog_sound (w := (949603 / 2949603)) (n := 12)
    (lo := (333812881 / 500000000)) (hi := (667625763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1949603 / 1000000) = 1/(1000000 / 1949603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (333812881 / 500000000) (667625763 / 1000000000) (Real.log (1949603 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1949603 / 1000000) = -Real.log (1000000 / 1949603) := by
    rw [show ((1949603 / 1000000) : ℝ) = ((1000000 / 1949603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2987823627 / 1000000000) ≤ -Real.log (50397 / 1000000) ∧
    -Real.log (50397 / 1000000) ≤ (186738977 / 62500000) := by
  have h := checkLog_sound (w := (12103 / 112897)) (n := 12)
    (lo := (215234907 / 1000000000)) (hi := (53808727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50397) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 50397) = 1/(50397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-186738977 / 62500000) (-2987823627 / 1000000000) (Real.log (50397 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133382919 / 200000000) ≤ -Real.log (1000000 / 1948217) ∧
    -Real.log (1000000 / 1948217) ≤ (166728649 / 250000000) := by
  have h := checkLog_sound (w := (948217 / 2948217)) (n := 12)
    (lo := (133382919 / 200000000)) (hi := (166728649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948217 / 1000000) = 1/(1000000 / 1948217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133382919 / 200000000) (166728649 / 250000000) (Real.log (1948217 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1948217 / 1000000) = -Real.log (1000000 / 1948217) := by
    rw [show ((1948217 / 1000000) : ℝ) = ((1000000 / 1948217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1480346683 / 500000000) ≤ -Real.log (51783 / 1000000) ∧
    -Real.log (51783 / 1000000) ≤ (2960693371 / 1000000000) := by
  have h := checkLog_sound (w := (10717 / 114283)) (n := 12)
    (lo := (94052323 / 500000000)) (hi := (188104647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51783) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51783) = 1/(51783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2960693371 / 1000000000) (-1480346683 / 500000000) (Real.log (51783 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16680191 / 25000000) ≤ -Real.log (250000 / 487197) ∧
    -Real.log (250000 / 487197) ≤ (667207641 / 1000000000) := by
  have h := checkLog_sound (w := (237197 / 737197)) (n := 12)
    (lo := (16680191 / 25000000)) (hi := (667207641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487197 / 250000) = 1/(250000 / 487197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16680191 / 25000000) (667207641 / 1000000000) (Real.log (487197 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (487197 / 250000) = -Real.log (250000 / 487197) := by
    rw [show ((487197 / 250000) : ℝ) = ((250000 / 487197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2971781397 / 1000000000) ≤ -Real.log (12803 / 250000) ∧
    -Real.log (12803 / 250000) ≤ (1485890701 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 14214)) (n := 12)
    (lo := (199192677 / 1000000000)) (hi := (99596339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12803) = 1/(12803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1485890701 / 500000000) (-2971781397 / 1000000000) (Real.log (12803 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1822166577 / 500000000) ≤ -Real.log (20000000000 / 765145055549) ∧
    -Real.log (20000000000 / 765145055549) ≤ (91108329 / 25000000) := by
  have h := checkLog_sound (w := (125145055549 / 1405145055549)) (n := 12)
    (lo := (89298627 / 500000000)) (hi := (35719451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765145055549 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(765145055549 / 640000000000) = 1/(20000000000 / 765145055549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1822166577 / 500000000) (91108329 / 25000000) (Real.log (765145055549 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (765145055549 / 20000000000) = -Real.log (20000000000 / 765145055549) := by
    rw [show ((765145055549 / 20000000000) : ℝ) = ((20000000000 / 765145055549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (913862347 / 250000000) ≤ -Real.log (500000000000 / 19342450939541) ∧
    -Real.log (500000000000 / 19342450939541) ≤ (1827724697 / 500000000) := by
  have h := checkLog_sound (w := (3342450939541 / 35342450939541)) (n := 12)
    (lo := (11857093 / 62500000)) (hi := (189713489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19342450939541 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19342450939541 / 16000000000000) = 1/(500000000000 / 19342450939541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (913862347 / 250000000) (1827724697 / 500000000) (Real.log (19342450939541 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (19342450939541 / 500000000000) = -Real.log (500000000000 / 19342450939541) := by
    rw [show ((19342450939541 / 500000000000) : ℝ) = ((500000000000 / 19342450939541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3627607961 / 1000000000) ≤ -Real.log (500000000000 / 18811357009057) ∧
    -Real.log (500000000000 / 18811357009057) ≤ (3627607967 / 1000000000) := by
  have h := checkLog_sound (w := (2811357009057 / 34811357009057)) (n := 12)
    (lo := (161872061 / 1000000000)) (hi := (80936031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18811357009057 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18811357009057 / 16000000000000) = 1/(500000000000 / 18811357009057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3627607961 / 1000000000) (3627607967 / 1000000000) (Real.log (18811357009057 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18811357009057 / 500000000000) = -Real.log (500000000000 / 18811357009057) := by
    rw [show ((18811357009057 / 500000000000) : ℝ) = ((500000000000 / 18811357009057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3638989037 / 1000000000) ≤ -Real.log (250000000000 / 9513336717957) ∧
    -Real.log (250000000000 / 9513336717957) ≤ (3638989043 / 1000000000) := by
  have h := checkLog_sound (w := (1513336717957 / 17513336717957)) (n := 12)
    (lo := (173253137 / 1000000000)) (hi := (86626569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9513336717957 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9513336717957 / 8000000000000) = 1/(250000000000 / 9513336717957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3638989037 / 1000000000) (3638989043 / 1000000000) (Real.log (9513336717957 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9513336717957 / 250000000000) = -Real.log (250000000000 / 9513336717957) := by
    rw [show ((9513336717957 / 250000000000) : ℝ) = ((250000000000 / 9513336717957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0133
