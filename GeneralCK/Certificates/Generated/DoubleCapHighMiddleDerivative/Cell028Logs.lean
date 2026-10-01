import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell028
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (47329147 / 200000000) ≤ -Real.log (5120 / 6487) ∧
    -Real.log (5120 / 6487) ≤ (29580717 / 125000000) := by
  have h := checkLog_sound (w := (1367 / 11607)) (n := 12)
    (lo := (47329147 / 200000000)) (hi := (29580717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6487 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6487 / 5120) = 1/(5120 / 6487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47329147 / 200000000) (29580717 / 125000000) (Real.log (6487 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6487 / 5120) = -Real.log (5120 / 6487) := by
    rw [show ((6487 / 5120) : ℝ) = ((5120 / 6487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155299459 / 500000000) ≤ -Real.log (3753 / 5120) ∧
    -Real.log (3753 / 5120) ≤ (310598919 / 1000000000) := by
  have h := checkLog_sound (w := (1367 / 8873)) (n := 12)
    (lo := (155299459 / 500000000)) (hi := (310598919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3753) = 1/(3753 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-310598919 / 1000000000) (-155299459 / 500000000) (Real.log (3753 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59045791 / 250000000) ≤ -Real.log (1280 / 1621) ∧
    -Real.log (1280 / 1621) ≤ (47236633 / 200000000) := by
  have h := checkLog_sound (w := (341 / 2901)) (n := 12)
    (lo := (59045791 / 250000000)) (hi := (47236633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1621 / 1280) = 1/(1280 / 1621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59045791 / 250000000) (47236633 / 200000000) (Real.log (1621 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1621 / 1280) = -Real.log (1280 / 1621) := by
    rw [show ((1621 / 1280) : ℝ) = ((1280 / 1621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (309799877 / 1000000000) ≤ -Real.log (939 / 1280) ∧
    -Real.log (939 / 1280) ≤ (154899939 / 500000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 939) = 1/(939 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-154899939 / 500000000) (-309799877 / 1000000000) (Real.log (939 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (34614281 / 200000000) ≤ -Real.log (1000000 / 1188951) ∧
    -Real.log (1000000 / 1188951) ≤ (86535703 / 500000000) := by
  have h := checkLog_sound (w := (188951 / 2188951)) (n := 12)
    (lo := (34614281 / 200000000)) (hi := (86535703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188951 / 1000000) = 1/(1000000 / 1188951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (34614281 / 200000000) (86535703 / 500000000) (Real.log (1188951 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1188951 / 1000000) = -Real.log (1000000 / 1188951) := by
    rw [show ((1188951 / 1000000) : ℝ) = ((1000000 / 1188951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209426807 / 1000000000) ≤ -Real.log (811049 / 1000000) ∧
    -Real.log (811049 / 1000000) ≤ (26178351 / 125000000) := by
  have h := checkLog_sound (w := (188951 / 1811049)) (n := 12)
    (lo := (209426807 / 1000000000)) (hi := (26178351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811049) = 1/(811049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26178351 / 125000000) (-209426807 / 1000000000) (Real.log (811049 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34684919 / 200000000) ≤ -Real.log (1000000 / 1189371) ∧
    -Real.log (1000000 / 1189371) ≤ (43356149 / 250000000) := by
  have h := checkLog_sound (w := (189371 / 2189371)) (n := 12)
    (lo := (34684919 / 200000000)) (hi := (43356149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189371 / 1000000) = 1/(1000000 / 1189371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34684919 / 200000000) (43356149 / 250000000) (Real.log (1189371 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1189371 / 1000000) = -Real.log (1000000 / 1189371) := by
    rw [show ((1189371 / 1000000) : ℝ) = ((1000000 / 1189371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209944789 / 1000000000) ≤ -Real.log (810629 / 1000000) ∧
    -Real.log (810629 / 1000000) ≤ (20994479 / 100000000) := by
  have h := checkLog_sound (w := (189371 / 1810629)) (n := 12)
    (lo := (209944789 / 1000000000)) (hi := (20994479 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810629) = 1/(810629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20994479 / 100000000) (-209944789 / 1000000000) (Real.log (810629 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12658331 / 100000000) ≤ -Real.log (31250 / 35467) ∧
    -Real.log (31250 / 35467) ≤ (126583311 / 1000000000) := by
  have h := checkLog_sound (w := (4217 / 66717)) (n := 12)
    (lo := (12658331 / 100000000)) (hi := (126583311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35467 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35467 / 31250) = 1/(31250 / 35467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12658331 / 100000000) (126583311 / 1000000000) (Real.log (35467 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (35467 / 31250) = -Real.log (31250 / 35467) := by
    rw [show ((35467 / 31250) : ℝ) = ((31250 / 35467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72480517 / 500000000) ≤ -Real.log (27033 / 31250) ∧
    -Real.log (27033 / 31250) ≤ (28992207 / 200000000) := by
  have h := checkLog_sound (w := (4217 / 58283)) (n := 12)
    (lo := (72480517 / 500000000)) (hi := (28992207 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27033) = 1/(27033 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28992207 / 200000000) (-72480517 / 500000000) (Real.log (27033 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (12685289 / 100000000) ≤ -Real.log (4000 / 4541) ∧
    -Real.log (4000 / 4541) ≤ (126852891 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 8541)) (n := 12)
    (lo := (12685289 / 100000000)) (hi := (126852891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4541 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4541 / 4000) = 1/(4000 / 4541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (12685289 / 100000000) (126852891 / 1000000000) (Real.log (4541 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4541 / 4000) = -Real.log (4000 / 4541) := by
    rw [show ((4541 / 4000) : ℝ) = ((4000 / 4541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145314831 / 1000000000) ≤ -Real.log (3459 / 4000) ∧
    -Real.log (3459 / 4000) ≤ (9082177 / 62500000) := by
  have h := checkLog_sound (w := (541 / 7459)) (n := 12)
    (lo := (145314831 / 1000000000)) (hi := (9082177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3459) = 1/(3459 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9082177 / 62500000) (-145314831 / 1000000000) (Real.log (3459 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272991521 / 500000000) ≤ -Real.log (500000000000 / 863152289669) ∧
    -Real.log (500000000000 / 863152289669) ≤ (545983043 / 1000000000) := by
  have h := checkLog_sound (w := (363152289669 / 1363152289669)) (n := 12)
    (lo := (272991521 / 500000000)) (hi := (545983043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863152289669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863152289669 / 500000000000) = 1/(500000000000 / 863152289669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272991521 / 500000000) (545983043 / 1000000000) (Real.log (863152289669 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (863152289669 / 500000000000) = -Real.log (500000000000 / 863152289669) := by
    rw [show ((863152289669 / 500000000000) : ℝ) = ((500000000000 / 863152289669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273622327 / 500000000) ≤ -Real.log (250000000000 / 432120969891) ∧
    -Real.log (250000000000 / 432120969891) ≤ (109448931 / 200000000) := by
  have h := checkLog_sound (w := (182120969891 / 682120969891)) (n := 12)
    (lo := (273622327 / 500000000)) (hi := (109448931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432120969891 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432120969891 / 250000000000) = 1/(250000000000 / 432120969891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (273622327 / 500000000) (109448931 / 200000000) (Real.log (432120969891 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (432120969891 / 250000000000) = -Real.log (250000000000 / 432120969891) := by
    rw [show ((432120969891 / 250000000000) : ℝ) = ((250000000000 / 432120969891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (382498213 / 1000000000) ≤ -Real.log (100000000000 / 146594225503) ∧
    -Real.log (100000000000 / 146594225503) ≤ (191249107 / 500000000) := by
  have h := checkLog_sound (w := (46594225503 / 246594225503)) (n := 12)
    (lo := (382498213 / 1000000000)) (hi := (191249107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146594225503 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146594225503 / 100000000000) = 1/(100000000000 / 146594225503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (382498213 / 1000000000) (191249107 / 500000000) (Real.log (146594225503 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (146594225503 / 100000000000) = -Real.log (100000000000 / 146594225503) := by
    rw [show ((146594225503 / 100000000000) : ℝ) = ((100000000000 / 146594225503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76673877 / 200000000) ≤ -Real.log (100000000000 / 146721989961) ∧
    -Real.log (100000000000 / 146721989961) ≤ (191684693 / 500000000) := by
  have h := checkLog_sound (w := (46721989961 / 246721989961)) (n := 12)
    (lo := (76673877 / 200000000)) (hi := (191684693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146721989961 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146721989961 / 100000000000) = 1/(100000000000 / 146721989961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76673877 / 200000000) (191684693 / 500000000) (Real.log (146721989961 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (146721989961 / 100000000000) = -Real.log (100000000000 / 146721989961) := by
    rw [show ((146721989961 / 100000000000) : ℝ) = ((100000000000 / 146721989961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (33943043 / 125000000) ≤ -Real.log (500000000000 / 655994525209) ∧
    -Real.log (500000000000 / 655994525209) ≤ (54308869 / 200000000) := by
  have h := checkLog_sound (w := (155994525209 / 1155994525209)) (n := 12)
    (lo := (33943043 / 125000000)) (hi := (54308869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655994525209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655994525209 / 500000000000) = 1/(500000000000 / 655994525209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33943043 / 125000000) (54308869 / 200000000) (Real.log (655994525209 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655994525209 / 500000000000) = -Real.log (500000000000 / 655994525209) := by
    rw [show ((655994525209 / 500000000000) : ℝ) = ((500000000000 / 655994525209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (136083861 / 500000000) ≤ -Real.log (125000000000 / 164100896213) ∧
    -Real.log (125000000000 / 164100896213) ≤ (272167723 / 1000000000) := by
  have h := checkLog_sound (w := (39100896213 / 289100896213)) (n := 12)
    (lo := (136083861 / 500000000)) (hi := (272167723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164100896213 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164100896213 / 125000000000) = 1/(125000000000 / 164100896213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (136083861 / 500000000) (272167723 / 1000000000) (Real.log (164100896213 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164100896213 / 125000000000) = -Real.log (125000000000 / 164100896213) := by
    rw [show ((164100896213 / 125000000000) : ℝ) = ((125000000000 / 164100896213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (923097 / 50000000) ≤ -Real.log (15707319 / 16000000) ∧
    -Real.log (15707319 / 16000000) ≤ (18461941 / 1000000000) := by
  have h := checkLog_sound (w := (292681 / 31707319)) (n := 12)
    (lo := (923097 / 50000000)) (hi := (18461941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15707319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15707319) = 1/(15707319 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18461941 / 1000000000) (-923097 / 50000000) (Real.log (15707319 / 16000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18377723 / 1000000000) ≤ -Real.log (958779411 / 976562500) ∧
    -Real.log (958779411 / 976562500) ≤ (4594431 / 250000000) := by
  have h := checkLog_sound (w := (17783089 / 1935341911)) (n := 12)
    (lo := (18377723 / 1000000000)) (hi := (4594431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 958779411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 958779411) = 1/(958779411 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4594431 / 250000000) (-18377723 / 1000000000) (Real.log (958779411 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell028
