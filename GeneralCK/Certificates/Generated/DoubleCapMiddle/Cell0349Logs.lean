import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0349
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

theorem reflection_log_1_neg : (42476547 / 200000000) ≤ -Real.log (10240 / 12663) ∧
    -Real.log (10240 / 12663) ≤ (13273921 / 62500000) := by
  have h := checkLog_sound (w := (2423 / 22903)) (n := 12)
    (lo := (42476547 / 200000000)) (hi := (13273921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12663 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12663 / 10240) = 1/(10240 / 12663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42476547 / 200000000) (13273921 / 62500000) (Real.log (12663 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12663 / 10240) = -Real.log (10240 / 12663) := by
    rw [show ((12663 / 10240) : ℝ) = ((10240 / 12663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27000077 / 100000000) ≤ -Real.log (7817 / 10240) ∧
    -Real.log (7817 / 10240) ≤ (270000771 / 1000000000) := by
  have h := checkLog_sound (w := (2423 / 18057)) (n := 12)
    (lo := (27000077 / 100000000)) (hi := (270000771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7817) = 1/(7817 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270000771 / 1000000000) (-27000077 / 100000000) (Real.log (7817 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (212145797 / 1000000000) ≤ -Real.log (512 / 633) ∧
    -Real.log (512 / 633) ≤ (106072899 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1145)) (n := 12)
    (lo := (212145797 / 1000000000)) (hi := (106072899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633 / 512) = 1/(512 / 633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (212145797 / 1000000000) (106072899 / 500000000) (Real.log (633 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (633 / 512) = -Real.log (512 / 633) := by
    rw [show ((633 / 512) : ℝ) = ((512 / 633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53923413 / 200000000) ≤ -Real.log (391 / 512) ∧
    -Real.log (391 / 512) ≤ (134808533 / 500000000) := by
  have h := checkLog_sound (w := (121 / 903)) (n := 12)
    (lo := (53923413 / 200000000)) (hi := (134808533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 391) = 1/(391 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-134808533 / 500000000) (-53923413 / 200000000) (Real.log (391 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (387465541 / 1000000000) ≤ -Real.log (5120 / 7543) ∧
    -Real.log (5120 / 7543) ≤ (193732771 / 500000000) := by
  have h := checkLog_sound (w := (2423 / 12663)) (n := 12)
    (lo := (387465541 / 1000000000)) (hi := (193732771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7543 / 5120) = 1/(5120 / 7543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (387465541 / 1000000000) (193732771 / 500000000) (Real.log (7543 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7543 / 5120) = -Real.log (5120 / 7543) := by
    rw [show ((7543 / 5120) : ℝ) = ((5120 / 7543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320507197 / 500000000) ≤ -Real.log (2697 / 5120) ∧
    -Real.log (2697 / 5120) ≤ (128202879 / 200000000) := by
  have h := checkLog_sound (w := (2423 / 7817)) (n := 12)
    (lo := (320507197 / 500000000)) (hi := (128202879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2697) = 1/(2697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128202879 / 200000000) (-320507197 / 500000000) (Real.log (2697 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193533871 / 500000000) ≤ -Real.log (256 / 377) ∧
    -Real.log (256 / 377) ≤ (387067743 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 633)) (n := 12)
    (lo := (193533871 / 500000000)) (hi := (387067743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 256) = 1/(256 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193533871 / 500000000) (387067743 / 1000000000) (Real.log (377 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (377 / 256) = -Real.log (256 / 377) := by
    rw [show ((377 / 256) : ℝ) = ((256 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (319951333 / 500000000) ≤ -Real.log (135 / 256) ∧
    -Real.log (135 / 256) ≤ (639902667 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 391)) (n := 12)
    (lo := (319951333 / 500000000)) (hi := (639902667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 135) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 135) = 1/(135 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-639902667 / 1000000000) (-319951333 / 500000000) (Real.log (135 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36364947 / 125000000) ≤ -Real.log (1000000 / 1337657) ∧
    -Real.log (1000000 / 1337657) ≤ (290919577 / 1000000000) := by
  have h := checkLog_sound (w := (337657 / 2337657)) (n := 12)
    (lo := (36364947 / 125000000)) (hi := (290919577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337657 / 1000000) = 1/(1000000 / 1337657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36364947 / 125000000) (290919577 / 1000000000) (Real.log (1337657 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1337657 / 1000000) = -Real.log (1000000 / 1337657) := by
    rw [show ((1337657 / 1000000) : ℝ) = ((1000000 / 1337657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41197173 / 100000000) ≤ -Real.log (662343 / 1000000) ∧
    -Real.log (662343 / 1000000) ≤ (411971731 / 1000000000) := by
  have h := checkLog_sound (w := (337657 / 1662343)) (n := 12)
    (lo := (41197173 / 100000000)) (hi := (411971731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662343) = 1/(662343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-411971731 / 1000000000) (-41197173 / 100000000) (Real.log (662343 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145620117 / 500000000) ≤ -Real.log (500000 / 669043) ∧
    -Real.log (500000 / 669043) ≤ (58248047 / 200000000) := by
  have h := checkLog_sound (w := (169043 / 1169043)) (n := 12)
    (lo := (145620117 / 500000000)) (hi := (58248047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669043 / 500000) = 1/(500000 / 669043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145620117 / 500000000) (58248047 / 200000000) (Real.log (669043 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (669043 / 500000) = -Real.log (500000 / 669043) := by
    rw [show ((669043 / 500000) : ℝ) = ((500000 / 669043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10315491 / 25000000) ≤ -Real.log (330957 / 500000) ∧
    -Real.log (330957 / 500000) ≤ (412619641 / 1000000000) := by
  have h := checkLog_sound (w := (169043 / 830957)) (n := 12)
    (lo := (10315491 / 25000000)) (hi := (412619641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330957) = 1/(330957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-412619641 / 1000000000) (-10315491 / 25000000) (Real.log (330957 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55092527 / 250000000) ≤ -Real.log (500000 / 623269) ∧
    -Real.log (500000 / 623269) ≤ (220370109 / 1000000000) := by
  have h := checkLog_sound (w := (123269 / 1123269)) (n := 12)
    (lo := (55092527 / 250000000)) (hi := (220370109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623269 / 500000) = 1/(500000 / 623269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55092527 / 250000000) (220370109 / 1000000000) (Real.log (623269 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (623269 / 500000) = -Real.log (500000 / 623269) := by
    rw [show ((623269 / 500000) : ℝ) = ((500000 / 623269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (283076693 / 1000000000) ≤ -Real.log (376731 / 500000) ∧
    -Real.log (376731 / 500000) ≤ (141538347 / 500000000) := by
  have h := checkLog_sound (w := (123269 / 876731)) (n := 12)
    (lo := (283076693 / 1000000000)) (hi := (141538347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376731) = 1/(376731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-141538347 / 500000000) (-283076693 / 1000000000) (Real.log (376731 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (44127603 / 200000000) ≤ -Real.log (125000 / 155859) ∧
    -Real.log (125000 / 155859) ≤ (3447469 / 15625000) := by
  have h := checkLog_sound (w := (30859 / 280859)) (n := 12)
    (lo := (44127603 / 200000000)) (hi := (3447469 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155859 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155859 / 125000) = 1/(125000 / 155859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44127603 / 200000000) (3447469 / 15625000) (Real.log (155859 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (155859 / 125000) = -Real.log (125000 / 155859) := by
    rw [show ((155859 / 125000) : ℝ) = ((125000 / 155859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (141760039 / 500000000) ≤ -Real.log (94141 / 125000) ∧
    -Real.log (94141 / 125000) ≤ (283520079 / 1000000000) := by
  have h := checkLog_sound (w := (30859 / 219141)) (n := 12)
    (lo := (141760039 / 500000000)) (hi := (283520079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94141) = 1/(94141 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283520079 / 1000000000) (-141760039 / 500000000) (Real.log (94141 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (140578261 / 200000000) ≤ -Real.log (500000000000 / 1009791754423) ∧
    -Real.log (500000000000 / 1009791754423) ≤ (702891307 / 1000000000) := by
  have h := checkLog_sound (w := (9791754423 / 2009791754423)) (n := 12)
    (lo := (77953 / 8000000)) (hi := (4872063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009791754423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1009791754423 / 1000000000000) = 1/(500000000000 / 1009791754423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (140578261 / 200000000) (702891307 / 1000000000) (Real.log (1009791754423 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1009791754423 / 500000000000) = -Real.log (500000000000 / 1009791754423) := by
    rw [show ((1009791754423 / 500000000000) : ℝ) = ((500000000000 / 1009791754423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (351929937 / 500000000) ≤ -Real.log (62500000000 / 126346285167) ∧
    -Real.log (62500000000 / 126346285167) ≤ (175964969 / 250000000) := by
  have h := checkLog_sound (w := (1346285167 / 251346285167)) (n := 12)
    (lo := (5356347 / 500000000)) (hi := (2142539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126346285167 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126346285167 / 125000000000) = 1/(62500000000 / 126346285167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (351929937 / 500000000) (175964969 / 250000000) (Real.log (126346285167 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (126346285167 / 62500000000) = -Real.log (62500000000 / 126346285167) := by
    rw [show ((126346285167 / 62500000000) : ℝ) = ((62500000000 / 126346285167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (251723401 / 500000000) ≤ -Real.log (50000000000 / 82720694607) ∧
    -Real.log (50000000000 / 82720694607) ≤ (503446803 / 1000000000) := by
  have h := checkLog_sound (w := (32720694607 / 132720694607)) (n := 12)
    (lo := (251723401 / 500000000)) (hi := (503446803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82720694607 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82720694607 / 50000000000) = 1/(50000000000 / 82720694607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (251723401 / 500000000) (503446803 / 1000000000) (Real.log (82720694607 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (82720694607 / 50000000000) = -Real.log (50000000000 / 82720694607) := by
    rw [show ((82720694607 / 50000000000) : ℝ) = ((50000000000 / 82720694607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (504158093 / 1000000000) ≤ -Real.log (125000000000 / 206948885183) ∧
    -Real.log (125000000000 / 206948885183) ≤ (252079047 / 500000000) := by
  have h := checkLog_sound (w := (81948885183 / 331948885183)) (n := 12)
    (lo := (504158093 / 1000000000)) (hi := (252079047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206948885183 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206948885183 / 125000000000) = 1/(125000000000 / 206948885183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (504158093 / 1000000000) (252079047 / 500000000) (Real.log (206948885183 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (206948885183 / 125000000000) = -Real.log (125000000000 / 206948885183) := by
    rw [show ((206948885183 / 125000000000) : ℝ) = ((125000000000 / 206948885183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0349
