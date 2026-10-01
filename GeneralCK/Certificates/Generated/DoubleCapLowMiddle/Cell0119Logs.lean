import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0119
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

theorem reflection_log_1_neg : (83308283 / 125000000) ≤ -Real.log (6400 / 12463) ∧
    -Real.log (6400 / 12463) ≤ (133293253 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 18863)) (n := 12)
    (lo := (83308283 / 125000000)) (hi := (133293253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12463 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12463 / 6400) = 1/(6400 / 12463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83308283 / 125000000) (133293253 / 200000000) (Real.log (12463 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12463 / 6400) = -Real.log (6400 / 12463) := by
    rw [show ((12463 / 6400) : ℝ) = ((6400 / 12463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (91999073 / 31250000) ≤ -Real.log (337 / 6400) ∧
    -Real.log (337 / 6400) ≤ (2943970341 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 337) = 1/(337 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2943970341 / 1000000000) (-91999073 / 31250000) (Real.log (337 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (666085063 / 1000000000) ≤ -Real.log (25600 / 49833) ∧
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


theorem reflection_log_3 : Bounds (666085063 / 1000000000) (83260633 / 125000000) (Real.log (49833 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49833 / 25600) = -Real.log (25600 / 49833) := by
    rw [show ((49833 / 25600) : ℝ) = ((25600 / 49833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2929973791 / 1000000000) ≤ -Real.log (1367 / 25600) ∧
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


theorem reflection_log_4 : Bounds (-732493449 / 250000000) (-2929973791 / 1000000000) (Real.log (1367 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (639053917 / 1000000000) ≤ -Real.log (3200 / 6063) ∧
    -Real.log (3200 / 6063) ≤ (319526959 / 500000000) := by
  have h := checkLog_sound (w := (2863 / 9263)) (n := 12)
    (lo := (639053917 / 1000000000)) (hi := (319526959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6063 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6063 / 3200) = 1/(3200 / 6063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (639053917 / 1000000000) (319526959 / 500000000) (Real.log (6063 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6063 / 3200) = -Real.log (3200 / 6063) := by
    rw [show ((6063 / 3200) : ℝ) = ((3200 / 6063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (562705789 / 250000000) ≤ -Real.log (337 / 3200) ∧
    -Real.log (337 / 3200) ≤ (56270579 / 25000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 337) = 1/(337 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56270579 / 25000000) (-562705789 / 250000000) (Real.log (337 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (638270169 / 1000000000) ≤ -Real.log (12800 / 24233) ∧
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


theorem reflection_log_7 : Bounds (638270169 / 1000000000) (63827017 / 100000000) (Real.log (24233 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24233 / 12800) = -Real.log (12800 / 24233) := by
    rw [show ((24233 / 12800) : ℝ) = ((12800 / 24233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2236826611 / 1000000000) ≤ -Real.log (1367 / 12800) ∧
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


theorem reflection_log_8 : Bounds (-447365323 / 200000000) (-2236826611 / 1000000000) (Real.log (1367 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134262097 / 200000000) ≤ -Real.log (625 / 1223) ∧
    -Real.log (625 / 1223) ≤ (335655243 / 500000000) := by
  have h := checkLog_sound (w := (299 / 924)) (n := 12)
    (lo := (134262097 / 200000000)) (hi := (335655243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 625) = 1/(625 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134262097 / 200000000) (335655243 / 500000000) (Real.log (1223 / 625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1223 / 625) = -Real.log (625 / 1223) := by
    rw [show ((1223 / 625) : ℝ) = ((625 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3141914781 / 1000000000) ≤ -Real.log (27 / 625) ∧
    -Real.log (27 / 625) ≤ (1570957393 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1057)) (n := 12)
    (lo := (369326061 / 1000000000)) (hi := (184663031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 432) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 432) = 1/(27 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1570957393 / 500000000) (-3141914781 / 1000000000) (Real.log (27 / 625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (671597137 / 1000000000) ≤ -Real.log (1000000 / 1957361) ∧
    -Real.log (1000000 / 1957361) ≤ (335798569 / 500000000) := by
  have h := checkLog_sound (w := (957361 / 2957361)) (n := 12)
    (lo := (671597137 / 1000000000)) (hi := (335798569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957361 / 1000000) = 1/(1000000 / 1957361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (671597137 / 1000000000) (335798569 / 500000000) (Real.log (1957361 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1957361 / 1000000) = -Real.log (1000000 / 1957361) := by
    rw [show ((1957361 / 1000000) : ℝ) = ((1000000 / 1957361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3154985949 / 1000000000) ≤ -Real.log (42639 / 1000000) ∧
    -Real.log (42639 / 1000000) ≤ (1577492977 / 500000000) := by
  have h := checkLog_sound (w := (19861 / 105139)) (n := 12)
    (lo := (382397229 / 1000000000)) (hi := (38239723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42639) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42639) = 1/(42639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1577492977 / 500000000) (-3154985949 / 1000000000) (Real.log (42639 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (134205057 / 200000000) ≤ -Real.log (500000 / 978121) ∧
    -Real.log (500000 / 978121) ≤ (335512643 / 500000000) := by
  have h := checkLog_sound (w := (478121 / 1478121)) (n := 12)
    (lo := (134205057 / 200000000)) (hi := (335512643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978121 / 500000) = 1/(500000 / 978121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (134205057 / 200000000) (335512643 / 500000000) (Real.log (978121 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (978121 / 500000) = -Real.log (500000 / 978121) := by
    rw [show ((978121 / 500000) : ℝ) = ((500000 / 978121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3129080823 / 1000000000) ≤ -Real.log (21879 / 500000) ∧
    -Real.log (21879 / 500000) ≤ (782270207 / 250000000) := by
  have h := checkLog_sound (w := (9371 / 53129)) (n := 12)
    (lo := (356492103 / 1000000000)) (hi := (44561513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21879) = 1/(21879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-782270207 / 250000000) (-3129080823 / 1000000000) (Real.log (21879 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671321217 / 1000000000) ≤ -Real.log (1000000 / 1956821) ∧
    -Real.log (1000000 / 1956821) ≤ (335660609 / 500000000) := by
  have h := checkLog_sound (w := (956821 / 2956821)) (n := 12)
    (lo := (671321217 / 1000000000)) (hi := (335660609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1956821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1956821 / 1000000) = 1/(1000000 / 1956821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671321217 / 1000000000) (335660609 / 500000000) (Real.log (1956821 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1956821 / 1000000) = -Real.log (1000000 / 1956821) := by
    rw [show ((1956821 / 1000000) : ℝ) = ((1000000 / 1956821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (314240101 / 100000000) ≤ -Real.log (43179 / 1000000) ∧
    -Real.log (43179 / 1000000) ≤ (628480203 / 200000000) := by
  have h := checkLog_sound (w := (19321 / 105679)) (n := 12)
    (lo := (36981229 / 100000000)) (hi := (369812291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43179) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 43179) = 1/(43179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-628480203 / 200000000) (-314240101 / 100000000) (Real.log (43179 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1906612633 / 500000000) ≤ -Real.log (125000000000 / 5662037037037) ∧
    -Real.log (125000000000 / 5662037037037) ≤ (476653159 / 125000000) := by
  have h := checkLog_sound (w := (1662037037037 / 9662037037037)) (n := 12)
    (lo := (173744683 / 500000000)) (hi := (347489367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5662037037037 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5662037037037 / 4000000000000) = 1/(125000000000 / 5662037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1906612633 / 500000000) (476653159 / 125000000) (Real.log (5662037037037 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5662037037037 / 125000000000) = -Real.log (125000000000 / 5662037037037) := by
    rw [show ((5662037037037 / 125000000000) : ℝ) = ((125000000000 / 5662037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1913291543 / 500000000) ≤ -Real.log (100000000000 / 4590541523019) ∧
    -Real.log (100000000000 / 4590541523019) ≤ (956645773 / 250000000) := by
  have h := checkLog_sound (w := (1390541523019 / 7790541523019)) (n := 12)
    (lo := (180423593 / 500000000)) (hi := (360847187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4590541523019 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4590541523019 / 3200000000000) = 1/(100000000000 / 4590541523019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1913291543 / 500000000) (956645773 / 250000000) (Real.log (4590541523019 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4590541523019 / 100000000000) = -Real.log (100000000000 / 4590541523019) := by
    rw [show ((4590541523019 / 100000000000) : ℝ) = ((100000000000 / 4590541523019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (950026527 / 250000000) ≤ -Real.log (250000000000 / 11176482014717) ∧
    -Real.log (250000000000 / 11176482014717) ≤ (1900053057 / 500000000) := by
  have h := checkLog_sound (w := (3176482014717 / 19176482014717)) (n := 12)
    (lo := (10449069 / 31250000)) (hi := (334370209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176482014717 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11176482014717 / 8000000000000) = 1/(250000000000 / 11176482014717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (950026527 / 250000000) (1900053057 / 500000000) (Real.log (11176482014717 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11176482014717 / 250000000000) = -Real.log (250000000000 / 11176482014717) := by
    rw [show ((11176482014717 / 250000000000) : ℝ) = ((250000000000 / 11176482014717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3813722227 / 1000000000) ≤ -Real.log (250000000000 / 11329703096413) ∧
    -Real.log (250000000000 / 11329703096413) ≤ (3813722233 / 1000000000) := by
  have h := checkLog_sound (w := (3329703096413 / 19329703096413)) (n := 12)
    (lo := (347986327 / 1000000000)) (hi := (43498291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11329703096413 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11329703096413 / 8000000000000) = 1/(250000000000 / 11329703096413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3813722227 / 1000000000) (3813722233 / 1000000000) (Real.log (11329703096413 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11329703096413 / 250000000000) = -Real.log (250000000000 / 11329703096413) := by
    rw [show ((11329703096413 / 250000000000) : ℝ) = ((250000000000 / 11329703096413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0119
