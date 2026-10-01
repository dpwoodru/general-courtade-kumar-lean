import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0134
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

theorem reflection_log_1_neg : (330366469 / 500000000) ≤ -Real.log (25600 / 49567) ∧
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


theorem reflection_log_1 : Bounds (330366469 / 500000000) (660732939 / 1000000000) (Real.log (49567 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49567 / 25600) = -Real.log (25600 / 49567) := by
    rw [show ((49567 / 25600) : ℝ) = ((25600 / 49567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (550434707 / 200000000) ≤ -Real.log (1633 / 25600) ∧
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


theorem reflection_log_2 : Bounds (-2752173539 / 1000000000) (-550434707 / 200000000) (Real.log (1633 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132069909 / 200000000) ≤ -Real.log (6400 / 12387) ∧
    -Real.log (6400 / 12387) ≤ (330174773 / 500000000) := by
  have h := checkLog_sound (w := (5987 / 18787)) (n := 12)
    (lo := (132069909 / 200000000)) (hi := (330174773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 6400) = 1/(6400 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132069909 / 200000000) (330174773 / 500000000) (Real.log (12387 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12387 / 6400) = -Real.log (6400 / 12387) := by
    rw [show ((12387 / 6400) : ℝ) = ((6400 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1370302837 / 500000000) ≤ -Real.log (413 / 6400) ∧
    -Real.log (413 / 6400) ≤ (1370302839 / 500000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 413) = 1/(413 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1370302839 / 500000000) (-1370302837 / 500000000) (Real.log (413 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (627232713 / 1000000000) ≤ -Real.log (12800 / 23967) ∧
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


theorem reflection_log_5 : Bounds (627232713 / 1000000000) (313616357 / 500000000) (Real.log (23967 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23967 / 12800) = -Real.log (12800 / 23967) := by
    rw [show ((23967 / 12800) : ℝ) = ((12800 / 23967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (411805271 / 200000000) ≤ -Real.log (1633 / 12800) ∧
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


theorem reflection_log_6 : Bounds (-1029513179 / 500000000) (-411805271 / 200000000) (Real.log (1633 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (313219821 / 500000000) ≤ -Real.log (3200 / 5987) ∧
    -Real.log (3200 / 5987) ≤ (626439643 / 1000000000) := by
  have h := checkLog_sound (w := (2787 / 9187)) (n := 12)
    (lo := (313219821 / 500000000)) (hi := (626439643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5987 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5987 / 3200) = 1/(3200 / 5987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (313219821 / 500000000) (626439643 / 1000000000) (Real.log (5987 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5987 / 3200) = -Real.log (3200 / 5987) := by
    rw [show ((5987 / 3200) : ℝ) = ((3200 / 5987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1023729247 / 500000000) ≤ -Real.log (413 / 3200) ∧
    -Real.log (413 / 3200) ≤ (2047458497 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 413) = 1/(413 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2047458497 / 1000000000) (-1023729247 / 500000000) (Real.log (413 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333531719 / 500000000) ≤ -Real.log (1000000 / 1948507) ∧
    -Real.log (1000000 / 1948507) ≤ (667063439 / 1000000000) := by
  have h := checkLog_sound (w := (948507 / 2948507)) (n := 12)
    (lo := (333531719 / 500000000)) (hi := (667063439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948507 / 1000000) = 1/(1000000 / 1948507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333531719 / 500000000) (667063439 / 1000000000) (Real.log (1948507 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1948507 / 1000000) = -Real.log (1000000 / 1948507) := by
    rw [show ((1948507 / 1000000) : ℝ) = ((1000000 / 1948507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (14831547 / 5000000) ≤ -Real.log (51493 / 1000000) ∧
    -Real.log (51493 / 1000000) ≤ (593261881 / 200000000) := by
  have h := checkLog_sound (w := (11007 / 113993)) (n := 12)
    (lo := (4843017 / 25000000)) (hi := (193720681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51493) = 1/(51493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-593261881 / 200000000) (-14831547 / 5000000) (Real.log (51493 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (667344639 / 1000000000) ≤ -Real.log (200000 / 389811) ∧
    -Real.log (200000 / 389811) ≤ (521363 / 781250) := by
  have h := checkLog_sound (w := (189811 / 589811)) (n := 12)
    (lo := (667344639 / 1000000000)) (hi := (521363 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389811 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389811 / 200000) = 1/(200000 / 389811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (667344639 / 1000000000) (521363 / 781250) (Real.log (389811 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (389811 / 200000) = -Real.log (200000 / 389811) := by
    rw [show ((389811 / 200000) : ℝ) = ((200000 / 389811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2977008657 / 1000000000) ≤ -Real.log (10189 / 200000) ∧
    -Real.log (10189 / 200000) ≤ (1488504331 / 500000000) := by
  have h := checkLog_sound (w := (2311 / 22689)) (n := 12)
    (lo := (204419937 / 1000000000)) (hi := (102209969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10189) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 10189) = 1/(10189 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1488504331 / 500000000) (-2977008657 / 1000000000) (Real.log (10189 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (66662249 / 100000000) ≤ -Real.log (15625 / 30432) ∧
    -Real.log (15625 / 30432) ≤ (666622491 / 1000000000) := by
  have h := checkLog_sound (w := (14807 / 46057)) (n := 12)
    (lo := (66662249 / 100000000)) (hi := (666622491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30432 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30432 / 15625) = 1/(15625 / 30432) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (66662249 / 100000000) (666622491 / 1000000000) (Real.log (30432 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30432 / 15625) = -Real.log (15625 / 30432) := by
    rw [show ((30432 / 15625) : ℝ) = ((15625 / 30432) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (589953027 / 200000000) ≤ -Real.log (818 / 15625) ∧
    -Real.log (818 / 15625) ≤ (147488257 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 28713)) (n := 12)
    (lo := (35435283 / 200000000)) (hi := (5536763 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13088) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13088) = 1/(818 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-147488257 / 50000000) (-589953027 / 200000000) (Real.log (818 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166728777 / 250000000) ≤ -Real.log (500000 / 974109) ∧
    -Real.log (500000 / 974109) ≤ (666915109 / 1000000000) := by
  have h := checkLog_sound (w := (474109 / 1474109)) (n := 12)
    (lo := (166728777 / 250000000)) (hi := (666915109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974109 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974109 / 500000) = 1/(500000 / 974109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166728777 / 250000000) (666915109 / 1000000000) (Real.log (974109 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (974109 / 500000) = -Real.log (500000 / 974109) := by
    rw [show ((974109 / 500000) : ℝ) = ((500000 / 974109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1480356339 / 500000000) ≤ -Real.log (25891 / 500000) ∧
    -Real.log (25891 / 500000) ≤ (2960712683 / 1000000000) := by
  have h := checkLog_sound (w := (5359 / 57141)) (n := 12)
    (lo := (94061979 / 500000000)) (hi := (188123959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25891) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25891) = 1/(25891 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2960712683 / 1000000000) (-1480356339 / 500000000) (Real.log (25891 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1816686419 / 500000000) ≤ -Real.log (100000000000 / 3784023071097) ∧
    -Real.log (100000000000 / 3784023071097) ≤ (908343211 / 250000000) := by
  have h := checkLog_sound (w := (584023071097 / 6984023071097)) (n := 12)
    (lo := (83818469 / 500000000)) (hi := (167636939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3784023071097 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3784023071097 / 3200000000000) = 1/(100000000000 / 3784023071097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1816686419 / 500000000) (908343211 / 250000000) (Real.log (3784023071097 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3784023071097 / 100000000000) = -Real.log (100000000000 / 3784023071097) := by
    rw [show ((3784023071097 / 100000000000) : ℝ) = ((100000000000 / 3784023071097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (227772081 / 62500000) ≤ -Real.log (250000000000 / 9564505839631) ∧
    -Real.log (250000000000 / 9564505839631) ≤ (1822176651 / 500000000) := by
  have h := checkLog_sound (w := (1564505839631 / 17564505839631)) (n := 12)
    (lo := (44654349 / 250000000)) (hi := (178617397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9564505839631 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9564505839631 / 8000000000000) = 1/(250000000000 / 9564505839631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (227772081 / 62500000) (1822176651 / 500000000) (Real.log (9564505839631 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9564505839631 / 250000000000) = -Real.log (250000000000 / 9564505839631) := by
    rw [show ((9564505839631 / 250000000000) : ℝ) = ((250000000000 / 9564505839631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28931101 / 8000000) ≤ -Real.log (100000000000 / 3720293398533) ∧
    -Real.log (100000000000 / 3720293398533) ≤ (3616387631 / 1000000000) := by
  have h := checkLog_sound (w := (520293398533 / 6920293398533)) (n := 12)
    (lo := (6026069 / 40000000)) (hi := (75325863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3720293398533 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3720293398533 / 3200000000000) = 1/(100000000000 / 3720293398533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (28931101 / 8000000) (3616387631 / 1000000000) (Real.log (3720293398533 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3720293398533 / 100000000000) = -Real.log (100000000000 / 3720293398533) := by
    rw [show ((3720293398533 / 100000000000) : ℝ) = ((100000000000 / 3720293398533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1813813893 / 500000000) ≤ -Real.log (500000000000 / 18811729944769) ∧
    -Real.log (500000000000 / 18811729944769) ≤ (226726737 / 62500000) := by
  have h := checkLog_sound (w := (2811729944769 / 34811729944769)) (n := 12)
    (lo := (80945943 / 500000000)) (hi := (161891887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18811729944769 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18811729944769 / 16000000000000) = 1/(500000000000 / 18811729944769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1813813893 / 500000000) (226726737 / 62500000) (Real.log (18811729944769 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18811729944769 / 500000000000) = -Real.log (500000000000 / 18811729944769) := by
    rw [show ((18811729944769 / 500000000000) : ℝ) = ((500000000000 / 18811729944769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0134
