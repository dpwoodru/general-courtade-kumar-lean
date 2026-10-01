import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0425
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

theorem reflection_log_1_neg : (194213457 / 1000000000) ≤ -Real.log (2048 / 2487) ∧
    -Real.log (2048 / 2487) ≤ (97106729 / 500000000) := by
  have h := checkLog_sound (w := (439 / 4535)) (n := 12)
    (lo := (194213457 / 1000000000)) (hi := (97106729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2048) = 1/(2048 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194213457 / 1000000000) (97106729 / 500000000) (Real.log (2487 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2487 / 2048) = -Real.log (2048 / 2487) := by
    rw [show ((2487 / 2048) : ℝ) = ((2048 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241250839 / 1000000000) ≤ -Real.log (1609 / 2048) ∧
    -Real.log (1609 / 2048) ≤ (6031271 / 25000000) := by
  have h := checkLog_sound (w := (439 / 3657)) (n := 12)
    (lo := (241250839 / 1000000000)) (hi := (6031271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1609) = 1/(1609 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6031271 / 25000000) (-241250839 / 1000000000) (Real.log (1609 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (96986087 / 500000000) ≤ -Real.log (640 / 777) ∧
    -Real.log (640 / 777) ≤ (7758887 / 40000000) := by
  have h := checkLog_sound (w := (137 / 1417)) (n := 12)
    (lo := (96986087 / 500000000)) (hi := (7758887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 640) = 1/(640 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (96986087 / 500000000) (7758887 / 40000000) (Real.log (777 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (777 / 640) = -Real.log (640 / 777) := by
    rw [show ((777 / 640) : ℝ) = ((640 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120439003 / 500000000) ≤ -Real.log (503 / 640) ∧
    -Real.log (503 / 640) ≤ (240878007 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1143)) (n := 12)
    (lo := (120439003 / 500000000)) (hi := (240878007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 503) = 1/(503 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240878007 / 1000000000) (-120439003 / 500000000) (Real.log (503 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71354519 / 200000000) ≤ -Real.log (1024 / 1463) ∧
    -Real.log (1024 / 1463) ≤ (89193149 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2487)) (n := 12)
    (lo := (71354519 / 200000000)) (hi := (89193149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1024) = 1/(1024 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71354519 / 200000000) (89193149 / 250000000) (Real.log (1463 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1463 / 1024) = -Real.log (1024 / 1463) := by
    rw [show ((1463 / 1024) : ℝ) = ((1024 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279929979 / 500000000) ≤ -Real.log (585 / 1024) ∧
    -Real.log (585 / 1024) ≤ (559859959 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1609)) (n := 12)
    (lo := (279929979 / 500000000)) (hi := (559859959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 585) = 1/(585 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-559859959 / 1000000000) (-279929979 / 500000000) (Real.log (585 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71272479 / 200000000) ≤ -Real.log (320 / 457) ∧
    -Real.log (320 / 457) ≤ (89090599 / 250000000) := by
  have h := checkLog_sound (w := (137 / 777)) (n := 12)
    (lo := (71272479 / 200000000)) (hi := (89090599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457 / 320) = 1/(320 / 457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71272479 / 200000000) (89090599 / 250000000) (Real.log (457 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (457 / 320) = -Real.log (320 / 457) := by
    rw [show ((457 / 320) : ℝ) = ((320 / 457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279417421 / 500000000) ≤ -Real.log (183 / 320) ∧
    -Real.log (183 / 320) ≤ (558834843 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 183) = 1/(183 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-558834843 / 1000000000) (-279417421 / 500000000) (Real.log (183 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (266384633 / 1000000000) ≤ -Real.log (1000000 / 1305237) ∧
    -Real.log (1000000 / 1305237) ≤ (133192317 / 500000000) := by
  have h := checkLog_sound (w := (305237 / 2305237)) (n := 12)
    (lo := (266384633 / 1000000000)) (hi := (133192317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305237 / 1000000) = 1/(1000000 / 1305237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (266384633 / 1000000000) (133192317 / 500000000) (Real.log (1305237 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1305237 / 1000000) = -Real.log (1000000 / 1305237) := by
    rw [show ((1305237 / 1000000) : ℝ) = ((1000000 / 1305237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182092249 / 500000000) ≤ -Real.log (694763 / 1000000) ∧
    -Real.log (694763 / 1000000) ≤ (364184499 / 1000000000) := by
  have h := checkLog_sound (w := (305237 / 1694763)) (n := 12)
    (lo := (182092249 / 500000000)) (hi := (364184499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694763) = 1/(694763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-364184499 / 1000000000) (-182092249 / 500000000) (Real.log (694763 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266710957 / 1000000000) ≤ -Real.log (1000000 / 1305663) ∧
    -Real.log (1000000 / 1305663) ≤ (133355479 / 500000000) := by
  have h := checkLog_sound (w := (305663 / 2305663)) (n := 12)
    (lo := (266710957 / 1000000000)) (hi := (133355479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305663 / 1000000) = 1/(1000000 / 1305663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266710957 / 1000000000) (133355479 / 500000000) (Real.log (1305663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1305663 / 1000000) = -Real.log (1000000 / 1305663) := by
    rw [show ((1305663 / 1000000) : ℝ) = ((1000000 / 1305663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (72959569 / 200000000) ≤ -Real.log (694337 / 1000000) ∧
    -Real.log (694337 / 1000000) ≤ (182398923 / 500000000) := by
  have h := checkLog_sound (w := (305663 / 1694337)) (n := 12)
    (lo := (72959569 / 200000000)) (hi := (182398923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694337) = 1/(694337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182398923 / 500000000) (-72959569 / 200000000) (Real.log (694337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6253767 / 31250000) ≤ -Real.log (20000 / 24431) ∧
    -Real.log (20000 / 24431) ≤ (40024109 / 200000000) := by
  have h := checkLog_sound (w := (4431 / 44431)) (n := 12)
    (lo := (6253767 / 31250000)) (hi := (40024109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24431 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24431 / 20000) = 1/(20000 / 24431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6253767 / 31250000) (40024109 / 200000000) (Real.log (24431 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24431 / 20000) = -Real.log (20000 / 24431) := by
    rw [show ((24431 / 20000) : ℝ) = ((20000 / 24431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50090103 / 200000000) ≤ -Real.log (15569 / 20000) ∧
    -Real.log (15569 / 20000) ≤ (62612629 / 250000000) := by
  have h := checkLog_sound (w := (4431 / 35569)) (n := 12)
    (lo := (50090103 / 200000000)) (hi := (62612629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15569) = 1/(15569 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62612629 / 250000000) (-50090103 / 200000000) (Real.log (15569 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100193691 / 500000000) ≤ -Real.log (250000 / 305469) ∧
    -Real.log (250000 / 305469) ≤ (200387383 / 1000000000) := by
  have h := checkLog_sound (w := (55469 / 555469)) (n := 12)
    (lo := (100193691 / 500000000)) (hi := (200387383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305469 / 250000) = 1/(250000 / 305469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100193691 / 500000000) (200387383 / 1000000000) (Real.log (305469 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305469 / 250000) = -Real.log (250000 / 305469) := by
    rw [show ((305469 / 250000) : ℝ) = ((250000 / 305469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31358673 / 125000000) ≤ -Real.log (194531 / 250000) ∧
    -Real.log (194531 / 250000) ≤ (50173877 / 200000000) := by
  have h := checkLog_sound (w := (55469 / 444531)) (n := 12)
    (lo := (31358673 / 125000000)) (hi := (50173877 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194531) = 1/(194531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-50173877 / 200000000) (-31358673 / 125000000) (Real.log (194531 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (157642283 / 250000000) ≤ -Real.log (500000000000 / 939339746071) ∧
    -Real.log (500000000000 / 939339746071) ≤ (630569133 / 1000000000) := by
  have h := checkLog_sound (w := (439339746071 / 1439339746071)) (n := 12)
    (lo := (157642283 / 250000000)) (hi := (630569133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939339746071 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939339746071 / 500000000000) = 1/(500000000000 / 939339746071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (157642283 / 250000000) (630569133 / 1000000000) (Real.log (939339746071 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (939339746071 / 500000000000) = -Real.log (500000000000 / 939339746071) := by
    rw [show ((939339746071 / 500000000000) : ℝ) = ((500000000000 / 939339746071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (631508803 / 1000000000) ≤ -Real.log (500000000000 / 940222831277) ∧
    -Real.log (500000000000 / 940222831277) ≤ (157877201 / 250000000) := by
  have h := checkLog_sound (w := (440222831277 / 1440222831277)) (n := 12)
    (lo := (631508803 / 1000000000)) (hi := (157877201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940222831277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940222831277 / 500000000000) = 1/(500000000000 / 940222831277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (631508803 / 1000000000) (157877201 / 250000000) (Real.log (940222831277 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (940222831277 / 500000000000) = -Real.log (500000000000 / 940222831277) := by
    rw [show ((940222831277 / 500000000000) : ℝ) = ((500000000000 / 940222831277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22528553 / 50000000) ≤ -Real.log (50000000000 / 78460402081) ∧
    -Real.log (50000000000 / 78460402081) ≤ (450571061 / 1000000000) := by
  have h := checkLog_sound (w := (28460402081 / 128460402081)) (n := 12)
    (lo := (22528553 / 50000000)) (hi := (450571061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78460402081 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78460402081 / 50000000000) = 1/(50000000000 / 78460402081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (22528553 / 50000000) (450571061 / 1000000000) (Real.log (78460402081 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (78460402081 / 50000000000) = -Real.log (50000000000 / 78460402081) := by
    rw [show ((78460402081 / 50000000000) : ℝ) = ((50000000000 / 78460402081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (451256767 / 1000000000) ≤ -Real.log (250000000000 / 392571106919) ∧
    -Real.log (250000000000 / 392571106919) ≤ (7050887 / 15625000) := by
  have h := checkLog_sound (w := (142571106919 / 642571106919)) (n := 12)
    (lo := (451256767 / 1000000000)) (hi := (7050887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392571106919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392571106919 / 250000000000) = 1/(250000000000 / 392571106919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (451256767 / 1000000000) (7050887 / 15625000) (Real.log (392571106919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (392571106919 / 250000000000) = -Real.log (250000000000 / 392571106919) := by
    rw [show ((392571106919 / 250000000000) : ℝ) = ((250000000000 / 392571106919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0425
