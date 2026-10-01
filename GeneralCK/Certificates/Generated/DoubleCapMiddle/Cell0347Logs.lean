import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0347
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

theorem reflection_log_1_neg : (42571289 / 200000000) ≤ -Real.log (10240 / 12669) ∧
    -Real.log (10240 / 12669) ≤ (106428223 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 22909)) (n := 12)
    (lo := (42571289 / 200000000)) (hi := (106428223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12669 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12669 / 10240) = 1/(10240 / 12669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42571289 / 200000000) (106428223 / 500000000) (Real.log (12669 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12669 / 10240) = -Real.log (10240 / 12669) := by
    rw [show ((12669 / 10240) : ℝ) = ((10240 / 12669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135384311 / 500000000) ≤ -Real.log (7811 / 10240) ∧
    -Real.log (7811 / 10240) ≤ (270768623 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 18051)) (n := 12)
    (lo := (135384311 / 500000000)) (hi := (270768623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7811) = 1/(7811 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270768623 / 1000000000) (-135384311 / 500000000) (Real.log (7811 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (106309809 / 500000000) ≤ -Real.log (5120 / 6333) ∧
    -Real.log (5120 / 6333) ≤ (212619619 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 11453)) (n := 12)
    (lo := (106309809 / 500000000)) (hi := (212619619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6333 / 5120) = 1/(5120 / 6333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (106309809 / 500000000) (212619619 / 1000000000) (Real.log (6333 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6333 / 5120) = -Real.log (5120 / 6333) := by
    rw [show ((6333 / 5120) : ℝ) = ((5120 / 6333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135192311 / 500000000) ≤ -Real.log (3907 / 5120) ∧
    -Real.log (3907 / 5120) ≤ (270384623 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 9027)) (n := 12)
    (lo := (135192311 / 500000000)) (hi := (270384623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3907) = 1/(3907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270384623 / 1000000000) (-135192311 / 500000000) (Real.log (3907 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77652133 / 200000000) ≤ -Real.log (5120 / 7549) ∧
    -Real.log (5120 / 7549) ≤ (194130333 / 500000000) := by
  have h := checkLog_sound (w := (2429 / 12669)) (n := 12)
    (lo := (77652133 / 200000000)) (hi := (194130333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7549 / 5120) = 1/(5120 / 7549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77652133 / 200000000) (194130333 / 500000000) (Real.log (7549 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7549 / 5120) = -Real.log (5120 / 7549) := by
    rw [show ((7549 / 5120) : ℝ) = ((5120 / 7549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (643241567 / 1000000000) ≤ -Real.log (2691 / 5120) ∧
    -Real.log (2691 / 5120) ≤ (20101299 / 31250000) := by
  have h := checkLog_sound (w := (2429 / 7811)) (n := 12)
    (lo := (643241567 / 1000000000)) (hi := (20101299 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2691) = 1/(2691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20101299 / 31250000) (-643241567 / 1000000000) (Real.log (2691 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193931591 / 500000000) ≤ -Real.log (2560 / 3773) ∧
    -Real.log (2560 / 3773) ≤ (387863183 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 6333)) (n := 12)
    (lo := (193931591 / 500000000)) (hi := (387863183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3773 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3773 / 2560) = 1/(2560 / 3773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193931591 / 500000000) (387863183 / 1000000000) (Real.log (3773 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3773 / 2560) = -Real.log (2560 / 3773) := by
    rw [show ((3773 / 2560) : ℝ) = ((2560 / 3773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (642127361 / 1000000000) ≤ -Real.log (1347 / 2560) ∧
    -Real.log (1347 / 2560) ≤ (321063681 / 500000000) := by
  have h := checkLog_sound (w := (1213 / 3907)) (n := 12)
    (lo := (642127361 / 1000000000)) (hi := (321063681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1347) = 1/(1347 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-321063681 / 500000000) (-642127361 / 1000000000) (Real.log (1347 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2277807 / 7812500) ≤ -Real.log (1000000 / 1338513) ∧
    -Real.log (1000000 / 1338513) ≤ (291559297 / 1000000000) := by
  have h := checkLog_sound (w := (338513 / 2338513)) (n := 12)
    (lo := (2277807 / 7812500)) (hi := (291559297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338513 / 1000000) = 1/(1000000 / 1338513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2277807 / 7812500) (291559297 / 1000000000) (Real.log (1338513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1338513 / 1000000) = -Real.log (1000000 / 1338513) := by
    rw [show ((1338513 / 1000000) : ℝ) = ((1000000 / 1338513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (413264947 / 1000000000) ≤ -Real.log (661487 / 1000000) ∧
    -Real.log (661487 / 1000000) ≤ (103316237 / 250000000) := by
  have h := checkLog_sound (w := (338513 / 1661487)) (n := 12)
    (lo := (413264947 / 1000000000)) (hi := (103316237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661487) = 1/(661487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-103316237 / 250000000) (-413264947 / 1000000000) (Real.log (661487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18242531 / 62500000) ≤ -Real.log (1000000 / 1338943) ∧
    -Real.log (1000000 / 1338943) ≤ (291880497 / 1000000000) := by
  have h := checkLog_sound (w := (338943 / 2338943)) (n := 12)
    (lo := (18242531 / 62500000)) (hi := (291880497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338943 / 1000000) = 1/(1000000 / 1338943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18242531 / 62500000) (291880497 / 1000000000) (Real.log (1338943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1338943 / 1000000) = -Real.log (1000000 / 1338943) := by
    rw [show ((1338943 / 1000000) : ℝ) = ((1000000 / 1338943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (413915209 / 1000000000) ≤ -Real.log (661057 / 1000000) ∧
    -Real.log (661057 / 1000000) ≤ (41391521 / 100000000) := by
  have h := checkLog_sound (w := (338943 / 1661057)) (n := 12)
    (lo := (413915209 / 1000000000)) (hi := (41391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661057) = 1/(661057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41391521 / 100000000) (-413915209 / 1000000000) (Real.log (661057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (44180849 / 200000000) ≤ -Real.log (250000 / 311801) ∧
    -Real.log (250000 / 311801) ≤ (110452123 / 500000000) := by
  have h := checkLog_sound (w := (61801 / 561801)) (n := 12)
    (lo := (44180849 / 200000000)) (hi := (110452123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311801 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311801 / 250000) = 1/(250000 / 311801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (44180849 / 200000000) (110452123 / 500000000) (Real.log (311801 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (311801 / 250000) = -Real.log (250000 / 311801) := by
    rw [show ((311801 / 250000) : ℝ) = ((250000 / 311801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70990251 / 250000000) ≤ -Real.log (188199 / 250000) ∧
    -Real.log (188199 / 250000) ≤ (56792201 / 200000000) := by
  have h := checkLog_sound (w := (61801 / 438199)) (n := 12)
    (lo := (70990251 / 250000000)) (hi := (56792201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188199) = 1/(188199 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56792201 / 200000000) (-70990251 / 250000000) (Real.log (188199 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221172009 / 1000000000) ≤ -Real.log (500000 / 623769) ∧
    -Real.log (500000 / 623769) ≤ (22117201 / 100000000) := by
  have h := checkLog_sound (w := (123769 / 1123769)) (n := 12)
    (lo := (221172009 / 1000000000)) (hi := (22117201 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623769 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623769 / 500000) = 1/(500000 / 623769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221172009 / 1000000000) (22117201 / 100000000) (Real.log (623769 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (623769 / 500000) = -Real.log (500000 / 623769) := by
    rw [show ((623769 / 500000) : ℝ) = ((500000 / 623769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (284404781 / 1000000000) ≤ -Real.log (376231 / 500000) ∧
    -Real.log (376231 / 500000) ≤ (142202391 / 500000000) := by
  have h := checkLog_sound (w := (123769 / 876231)) (n := 12)
    (lo := (284404781 / 1000000000)) (hi := (142202391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376231) = 1/(376231 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142202391 / 500000000) (-284404781 / 1000000000) (Real.log (376231 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (704824243 / 1000000000) ≤ -Real.log (250000000000 / 505872753357) ∧
    -Real.log (250000000000 / 505872753357) ≤ (140964849 / 200000000) := by
  have h := checkLog_sound (w := (5872753357 / 1005872753357)) (n := 12)
    (lo := (11677063 / 1000000000)) (hi := (1459633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505872753357 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(505872753357 / 500000000000) = 1/(250000000000 / 505872753357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (704824243 / 1000000000) (140964849 / 200000000) (Real.log (505872753357 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (505872753357 / 250000000000) = -Real.log (250000000000 / 505872753357) := by
    rw [show ((505872753357 / 250000000000) : ℝ) = ((250000000000 / 505872753357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (352897853 / 500000000) ≤ -Real.log (500000000000 / 1012728856967) ∧
    -Real.log (500000000000 / 1012728856967) ≤ (176448927 / 250000000) := by
  have h := checkLog_sound (w := (12728856967 / 2012728856967)) (n := 12)
    (lo := (6324263 / 500000000)) (hi := (12648527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012728856967 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1012728856967 / 1000000000000) = 1/(500000000000 / 1012728856967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (352897853 / 500000000) (176448927 / 250000000) (Real.log (1012728856967 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1012728856967 / 500000000000) = -Real.log (500000000000 / 1012728856967) := by
    rw [show ((1012728856967 / 500000000000) : ℝ) = ((500000000000 / 1012728856967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2019461 / 4000000) ≤ -Real.log (250000000000 / 414190564243) ∧
    -Real.log (250000000000 / 414190564243) ≤ (504865251 / 1000000000) := by
  have h := checkLog_sound (w := (164190564243 / 664190564243)) (n := 12)
    (lo := (2019461 / 4000000)) (hi := (504865251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414190564243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414190564243 / 250000000000) = 1/(250000000000 / 414190564243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2019461 / 4000000) (504865251 / 1000000000) (Real.log (414190564243 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (414190564243 / 250000000000) = -Real.log (250000000000 / 414190564243) := by
    rw [show ((414190564243 / 250000000000) : ℝ) = ((250000000000 / 414190564243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (505576791 / 1000000000) ≤ -Real.log (250000000000 / 414485382651) ∧
    -Real.log (250000000000 / 414485382651) ≤ (63197099 / 125000000) := by
  have h := checkLog_sound (w := (164485382651 / 664485382651)) (n := 12)
    (lo := (505576791 / 1000000000)) (hi := (63197099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414485382651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414485382651 / 250000000000) = 1/(250000000000 / 414485382651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (505576791 / 1000000000) (63197099 / 125000000) (Real.log (414485382651 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (414485382651 / 250000000000) = -Real.log (250000000000 / 414485382651) := by
    rw [show ((414485382651 / 250000000000) : ℝ) = ((250000000000 / 414485382651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0347
