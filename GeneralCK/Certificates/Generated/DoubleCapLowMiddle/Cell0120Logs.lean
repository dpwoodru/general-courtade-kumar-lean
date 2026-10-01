import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0120
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

theorem reflection_log_1_neg : (666085063 / 1000000000) ≤ -Real.log (25600 / 49833) ∧
    -Real.log (25600 / 49833) ≤ (83260633 / 125000000) := by
  have h := checkLog_sound (w := (24233 / 75433)) (n := 12)
    (lo := (666085063 / 1000000000)) (hi := (83260633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49833 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49833 / 25600) = 1/(25600 / 49833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (666085063 / 1000000000) (83260633 / 125000000) (Real.log (49833 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49833 / 25600) = -Real.log (25600 / 49833) := by
    rw [show ((49833 / 25600) : ℝ) = ((25600 / 49833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2929973791 / 1000000000) ≤ -Real.log (1367 / 25600) ∧
    -Real.log (1367 / 25600) ≤ (732493449 / 250000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1367) = 1/(1367 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-732493449 / 250000000) (-2929973791 / 1000000000) (Real.log (1367 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (665703717 / 1000000000) ≤ -Real.log (12800 / 24907) ∧
    -Real.log (12800 / 24907) ≤ (332851859 / 500000000) := by
  have h := checkLog_sound (w := (12107 / 37707)) (n := 12)
    (lo := (665703717 / 1000000000)) (hi := (332851859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24907 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24907 / 12800) = 1/(12800 / 24907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (665703717 / 1000000000) (332851859 / 500000000) (Real.log (24907 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24907 / 12800) = -Real.log (12800 / 24907) := by
    rw [show ((24907 / 12800) : ℝ) = ((12800 / 24907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (182260653 / 62500000) ≤ -Real.log (693 / 12800) ∧
    -Real.log (693 / 12800) ≤ (2916170453 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 693) = 1/(693 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2916170453 / 1000000000) (-182260653 / 62500000) (Real.log (693 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (638270169 / 1000000000) ≤ -Real.log (12800 / 24233) ∧
    -Real.log (12800 / 24233) ≤ (63827017 / 100000000) := by
  have h := checkLog_sound (w := (11433 / 37033)) (n := 12)
    (lo := (638270169 / 1000000000)) (hi := (63827017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24233 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24233 / 12800) = 1/(12800 / 24233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (638270169 / 1000000000) (63827017 / 100000000) (Real.log (24233 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24233 / 12800) = -Real.log (12800 / 24233) := by
    rw [show ((24233 / 12800) : ℝ) = ((12800 / 24233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2236826611 / 1000000000) ≤ -Real.log (1367 / 12800) ∧
    -Real.log (1367 / 12800) ≤ (447365323 / 200000000) := by
  have h := checkLog_sound (w := (233 / 2967)) (n := 12)
    (lo := (157385071 / 1000000000)) (hi := (9836567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1367) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1367) = 1/(1367 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-447365323 / 200000000) (-2236826611 / 1000000000) (Real.log (1367 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (637485807 / 1000000000) ≤ -Real.log (6400 / 12107) ∧
    -Real.log (6400 / 12107) ≤ (39842863 / 62500000) := by
  have h := checkLog_sound (w := (5707 / 18507)) (n := 12)
    (lo := (637485807 / 1000000000)) (hi := (39842863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12107 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12107 / 6400) = 1/(6400 / 12107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (637485807 / 1000000000) (39842863 / 62500000) (Real.log (12107 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12107 / 6400) = -Real.log (6400 / 12107) := by
    rw [show ((12107 / 6400) : ℝ) = ((6400 / 12107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (555755817 / 250000000) ≤ -Real.log (693 / 6400) ∧
    -Real.log (693 / 6400) ≤ (277877909 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 693) = 1/(693 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277877909 / 125000000) (-555755817 / 250000000) (Real.log (693 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335512387 / 500000000) ≤ -Real.log (1000000 / 1956241) ∧
    -Real.log (1000000 / 1956241) ≤ (26840991 / 40000000) := by
  have h := checkLog_sound (w := (956241 / 2956241)) (n := 12)
    (lo := (335512387 / 500000000)) (hi := (26840991 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956241 / 1000000) = 1/(1000000 / 1956241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335512387 / 500000000) (26840991 / 40000000) (Real.log (1956241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1956241 / 1000000) = -Real.log (1000000 / 1956241) := by
    rw [show ((1956241 / 1000000) : ℝ) = ((1000000 / 1956241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (312905797 / 100000000) ≤ -Real.log (43759 / 1000000) ∧
    -Real.log (43759 / 1000000) ≤ (125162319 / 40000000) := by
  have h := checkLog_sound (w := (18741 / 106259)) (n := 12)
    (lo := (1425877 / 4000000)) (hi := (356469251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43759) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43759) = 1/(43759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-125162319 / 40000000) (-312905797 / 100000000) (Real.log (43759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167827749 / 250000000) ≤ -Real.log (1000000 / 1956801) ∧
    -Real.log (1000000 / 1956801) ≤ (671310997 / 1000000000) := by
  have h := checkLog_sound (w := (956801 / 2956801)) (n := 12)
    (lo := (167827749 / 250000000)) (hi := (671310997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956801 / 1000000) = 1/(1000000 / 1956801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167827749 / 250000000) (671310997 / 1000000000) (Real.log (1956801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1956801 / 1000000) = -Real.log (1000000 / 1956801) := by
    rw [show ((1956801 / 1000000) : ℝ) = ((1000000 / 1956801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3141937929 / 1000000000) ≤ -Real.log (43199 / 1000000) ∧
    -Real.log (43199 / 1000000) ≤ (1570968967 / 500000000) := by
  have h := checkLog_sound (w := (19301 / 105699)) (n := 12)
    (lo := (369349209 / 1000000000)) (hi := (36934921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43199) = 1/(43199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1570968967 / 500000000) (-3141937929 / 1000000000) (Real.log (43199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (670730289 / 1000000000) ≤ -Real.log (200000 / 391133) ∧
    -Real.log (200000 / 391133) ≤ (67073029 / 100000000) := by
  have h := checkLog_sound (w := (191133 / 591133)) (n := 12)
    (lo := (670730289 / 1000000000)) (hi := (67073029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391133 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391133 / 200000) = 1/(200000 / 391133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (670730289 / 1000000000) (67073029 / 100000000) (Real.log (391133 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (391133 / 200000) = -Real.log (200000 / 391133) := by
    rw [show ((391133 / 200000) : ℝ) = ((200000 / 391133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3115980843 / 1000000000) ≤ -Real.log (8867 / 200000) ∧
    -Real.log (8867 / 200000) ≤ (194748803 / 62500000) := by
  have h := checkLog_sound (w := (3633 / 21367)) (n := 12)
    (lo := (343392123 / 1000000000)) (hi := (85848031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8867) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 8867) = 1/(8867 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-194748803 / 62500000) (-3115980843 / 1000000000) (Real.log (8867 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671025797 / 1000000000) ≤ -Real.log (1000000 / 1956243) ∧
    -Real.log (1000000 / 1956243) ≤ (335512899 / 500000000) := by
  have h := checkLog_sound (w := (956243 / 2956243)) (n := 12)
    (lo := (671025797 / 1000000000)) (hi := (335512899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956243 / 1000000) = 1/(1000000 / 1956243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671025797 / 1000000000) (335512899 / 500000000) (Real.log (1956243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1956243 / 1000000) = -Real.log (1000000 / 1956243) := by
    rw [show ((1956243 / 1000000) : ℝ) = ((1000000 / 1956243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (782275919 / 250000000) ≤ -Real.log (43757 / 1000000) ∧
    -Real.log (43757 / 1000000) ≤ (3129103681 / 1000000000) := by
  have h := checkLog_sound (w := (18743 / 106257)) (n := 12)
    (lo := (89128739 / 250000000)) (hi := (356514957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43757) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43757) = 1/(43757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3129103681 / 1000000000) (-782275919 / 250000000) (Real.log (43757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (475010343 / 125000000) ≤ -Real.log (125000000000 / 5588110445851) ∧
    -Real.log (125000000000 / 5588110445851) ≤ (15200331 / 4000000) := by
  have h := checkLog_sound (w := (1588110445851 / 9588110445851)) (n := 12)
    (lo := (83586711 / 250000000)) (hi := (66869369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5588110445851 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5588110445851 / 4000000000000) = 1/(125000000000 / 5588110445851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (475010343 / 125000000) (15200331 / 4000000) (Real.log (5588110445851 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5588110445851 / 125000000000) = -Real.log (125000000000 / 5588110445851) := by
    rw [show ((5588110445851 / 125000000000) : ℝ) = ((125000000000 / 5588110445851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1906624463 / 500000000) ≤ -Real.log (100000000000 / 4529736799463) ∧
    -Real.log (100000000000 / 4529736799463) ≤ (953312233 / 250000000) := by
  have h := checkLog_sound (w := (1329736799463 / 7729736799463)) (n := 12)
    (lo := (173756513 / 500000000)) (hi := (347513027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4529736799463 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4529736799463 / 3200000000000) = 1/(100000000000 / 4529736799463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1906624463 / 500000000) (953312233 / 250000000) (Real.log (4529736799463 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4529736799463 / 100000000000) = -Real.log (100000000000 / 4529736799463) := by
    rw [show ((4529736799463 / 100000000000) : ℝ) = ((100000000000 / 4529736799463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (946677783 / 250000000) ≤ -Real.log (250000000000 / 11027771512349) ∧
    -Real.log (250000000000 / 11027771512349) ≤ (1893355569 / 500000000) := by
  have h := checkLog_sound (w := (3027771512349 / 19027771512349)) (n := 12)
    (lo := (2507619 / 7812500)) (hi := (320975233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11027771512349 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11027771512349 / 8000000000000) = 1/(250000000000 / 11027771512349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (946677783 / 250000000) (1893355569 / 500000000) (Real.log (11027771512349 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11027771512349 / 250000000000) = -Real.log (250000000000 / 11027771512349) := by
    rw [show ((11027771512349 / 250000000000) : ℝ) = ((250000000000 / 11027771512349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3800129473 / 1000000000) ≤ -Real.log (100000000000 / 4470697259867) ∧
    -Real.log (100000000000 / 4470697259867) ≤ (3800129479 / 1000000000) := by
  have h := checkLog_sound (w := (1270697259867 / 7670697259867)) (n := 12)
    (lo := (334393573 / 1000000000)) (hi := (167196787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4470697259867 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4470697259867 / 3200000000000) = 1/(100000000000 / 4470697259867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3800129473 / 1000000000) (3800129479 / 1000000000) (Real.log (4470697259867 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4470697259867 / 100000000000) = -Real.log (100000000000 / 4470697259867) := by
    rw [show ((4470697259867 / 100000000000) : ℝ) = ((100000000000 / 4470697259867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0120
