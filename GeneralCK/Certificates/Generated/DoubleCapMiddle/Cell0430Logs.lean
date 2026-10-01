import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0430
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

theorem reflection_log_1_neg : (24125807 / 125000000) ≤ -Real.log (512 / 621) ∧
    -Real.log (512 / 621) ≤ (193006457 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1133)) (n := 12)
    (lo := (24125807 / 125000000)) (hi := (193006457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 512) = 1/(512 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24125807 / 125000000) (193006457 / 1000000000) (Real.log (621 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (621 / 512) = -Real.log (512 / 621) := by
    rw [show ((621 / 512) : ℝ) = ((512 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (239388063 / 1000000000) ≤ -Real.log (403 / 512) ∧
    -Real.log (403 / 512) ≤ (7480877 / 31250000) := by
  have h := checkLog_sound (w := (109 / 915)) (n := 12)
    (lo := (239388063 / 1000000000)) (hi := (7480877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 403) = 1/(403 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7480877 / 31250000) (-239388063 / 1000000000) (Real.log (403 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192764881 / 1000000000) ≤ -Real.log (10240 / 12417) ∧
    -Real.log (10240 / 12417) ≤ (96382441 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 22657)) (n := 12)
    (lo := (192764881 / 1000000000)) (hi := (96382441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12417 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12417 / 10240) = 1/(10240 / 12417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192764881 / 1000000000) (96382441 / 500000000) (Real.log (12417 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12417 / 10240) = -Real.log (10240 / 12417) := by
    rw [show ((12417 / 10240) : ℝ) = ((10240 / 12417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (239015923 / 1000000000) ≤ -Real.log (8063 / 10240) ∧
    -Real.log (8063 / 10240) ≤ (59753981 / 250000000) := by
  have h := checkLog_sound (w := (2177 / 18303)) (n := 12)
    (lo := (239015923 / 1000000000)) (hi := (59753981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8063) = 1/(8063 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59753981 / 250000000) (-239015923 / 1000000000) (Real.log (8063 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (354719909 / 1000000000) ≤ -Real.log (256 / 365) ∧
    -Real.log (256 / 365) ≤ (35471991 / 100000000) := by
  have h := checkLog_sound (w := (109 / 621)) (n := 12)
    (lo := (354719909 / 1000000000)) (hi := (35471991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365 / 256) = 1/(256 / 365) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (354719909 / 1000000000) (35471991 / 100000000) (Real.log (365 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (365 / 256) = -Real.log (256 / 365) := by
    rw [show ((365 / 256) : ℝ) = ((256 / 365) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (554744857 / 1000000000) ≤ -Real.log (147 / 256) ∧
    -Real.log (147 / 256) ≤ (277372429 / 500000000) := by
  have h := checkLog_sound (w := (109 / 403)) (n := 12)
    (lo := (554744857 / 1000000000)) (hi := (277372429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 147) = 1/(147 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277372429 / 500000000) (-554744857 / 1000000000) (Real.log (147 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (70861773 / 200000000) ≤ -Real.log (5120 / 7297) ∧
    -Real.log (5120 / 7297) ≤ (177154433 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 12417)) (n := 12)
    (lo := (70861773 / 200000000)) (hi := (177154433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7297 / 5120) = 1/(5120 / 7297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (70861773 / 200000000) (177154433 / 500000000) (Real.log (7297 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7297 / 5120) = -Real.log (5120 / 7297) := by
    rw [show ((7297 / 5120) : ℝ) = ((5120 / 7297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (553724969 / 1000000000) ≤ -Real.log (2943 / 5120) ∧
    -Real.log (2943 / 5120) ≤ (55372497 / 100000000) := by
  have h := checkLog_sound (w := (2177 / 8063)) (n := 12)
    (lo := (553724969 / 1000000000)) (hi := (55372497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2943) = 1/(2943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55372497 / 100000000) (-553724969 / 1000000000) (Real.log (2943 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132377241 / 500000000) ≤ -Real.log (1000000 / 1303111) ∧
    -Real.log (1000000 / 1303111) ≤ (264754483 / 1000000000) := by
  have h := checkLog_sound (w := (303111 / 2303111)) (n := 12)
    (lo := (132377241 / 500000000)) (hi := (264754483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303111 / 1000000) = 1/(1000000 / 1303111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132377241 / 500000000) (264754483 / 1000000000) (Real.log (1303111 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1303111 / 1000000) = -Real.log (1000000 / 1303111) := by
    rw [show ((1303111 / 1000000) : ℝ) = ((1000000 / 1303111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (180564567 / 500000000) ≤ -Real.log (696889 / 1000000) ∧
    -Real.log (696889 / 1000000) ≤ (72225827 / 200000000) := by
  have h := checkLog_sound (w := (303111 / 1696889)) (n := 12)
    (lo := (180564567 / 500000000)) (hi := (72225827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696889) = 1/(696889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72225827 / 200000000) (-180564567 / 500000000) (Real.log (696889 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265081339 / 1000000000) ≤ -Real.log (1000000 / 1303537) ∧
    -Real.log (1000000 / 1303537) ≤ (13254067 / 50000000) := by
  have h := checkLog_sound (w := (303537 / 2303537)) (n := 12)
    (lo := (265081339 / 1000000000)) (hi := (13254067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303537 / 1000000) = 1/(1000000 / 1303537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265081339 / 1000000000) (13254067 / 50000000) (Real.log (1303537 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1303537 / 1000000) = -Real.log (1000000 / 1303537) := by
    rw [show ((1303537 / 1000000) : ℝ) = ((1000000 / 1303537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (361740609 / 1000000000) ≤ -Real.log (696463 / 1000000) ∧
    -Real.log (696463 / 1000000) ≤ (36174061 / 100000000) := by
  have h := checkLog_sound (w := (303537 / 1696463)) (n := 12)
    (lo := (361740609 / 1000000000)) (hi := (36174061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696463) = 1/(696463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36174061 / 100000000) (-361740609 / 1000000000) (Real.log (696463 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (198790201 / 1000000000) ≤ -Real.log (500000 / 609963) ∧
    -Real.log (500000 / 609963) ≤ (99395101 / 500000000) := by
  have h := checkLog_sound (w := (109963 / 1109963)) (n := 12)
    (lo := (198790201 / 1000000000)) (hi := (99395101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609963 / 500000) = 1/(500000 / 609963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (198790201 / 1000000000) (99395101 / 500000000) (Real.log (609963 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (609963 / 500000) = -Real.log (500000 / 609963) := by
    rw [show ((609963 / 500000) : ℝ) = ((500000 / 609963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (62091623 / 250000000) ≤ -Real.log (390037 / 500000) ∧
    -Real.log (390037 / 500000) ≤ (248366493 / 1000000000) := by
  have h := checkLog_sound (w := (109963 / 890037)) (n := 12)
    (lo := (62091623 / 250000000)) (hi := (248366493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390037) = 1/(390037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-248366493 / 1000000000) (-62091623 / 250000000) (Real.log (390037 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99528697 / 500000000) ≤ -Real.log (250000 / 305063) ∧
    -Real.log (250000 / 305063) ≤ (39811479 / 200000000) := by
  have h := checkLog_sound (w := (55063 / 555063)) (n := 12)
    (lo := (99528697 / 500000000)) (hi := (39811479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305063 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305063 / 250000) = 1/(250000 / 305063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99528697 / 500000000) (39811479 / 200000000) (Real.log (305063 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305063 / 250000) = -Real.log (250000 / 305063) := by
    rw [show ((305063 / 250000) : ℝ) = ((250000 / 305063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31098061 / 125000000) ≤ -Real.log (194937 / 250000) ∧
    -Real.log (194937 / 250000) ≤ (248784489 / 1000000000) := by
  have h := checkLog_sound (w := (55063 / 444937)) (n := 12)
    (lo := (31098061 / 125000000)) (hi := (248784489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194937) = 1/(194937 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-248784489 / 1000000000) (-31098061 / 125000000) (Real.log (194937 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (625883617 / 1000000000) ≤ -Real.log (100000000000 / 186989750161) ∧
    -Real.log (100000000000 / 186989750161) ≤ (312941809 / 500000000) := by
  have h := checkLog_sound (w := (86989750161 / 286989750161)) (n := 12)
    (lo := (625883617 / 1000000000)) (hi := (312941809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186989750161 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186989750161 / 100000000000) = 1/(100000000000 / 186989750161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (625883617 / 1000000000) (312941809 / 500000000) (Real.log (186989750161 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (186989750161 / 100000000000) = -Real.log (100000000000 / 186989750161) := by
    rw [show ((186989750161 / 100000000000) : ℝ) = ((100000000000 / 186989750161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (626821949 / 1000000000) ≤ -Real.log (500000000000 / 935826454529) ∧
    -Real.log (500000000000 / 935826454529) ≤ (12536439 / 20000000) := by
  have h := checkLog_sound (w := (435826454529 / 1435826454529)) (n := 12)
    (lo := (626821949 / 1000000000)) (hi := (12536439 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935826454529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935826454529 / 500000000000) = 1/(500000000000 / 935826454529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (626821949 / 1000000000) (12536439 / 20000000) (Real.log (935826454529 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (935826454529 / 500000000000) = -Real.log (500000000000 / 935826454529) := by
    rw [show ((935826454529 / 500000000000) : ℝ) = ((500000000000 / 935826454529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (447156693 / 1000000000) ≤ -Real.log (500000000000 / 781929663083) ∧
    -Real.log (500000000000 / 781929663083) ≤ (223578347 / 500000000) := by
  have h := checkLog_sound (w := (281929663083 / 1281929663083)) (n := 12)
    (lo := (447156693 / 1000000000)) (hi := (223578347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781929663083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781929663083 / 500000000000) = 1/(500000000000 / 781929663083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (447156693 / 1000000000) (223578347 / 500000000) (Real.log (781929663083 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (781929663083 / 500000000000) = -Real.log (500000000000 / 781929663083) := by
    rw [show ((781929663083 / 500000000000) : ℝ) = ((500000000000 / 781929663083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (447841883 / 1000000000) ≤ -Real.log (500000000000 / 782465617097) ∧
    -Real.log (500000000000 / 782465617097) ≤ (111960471 / 250000000) := by
  have h := checkLog_sound (w := (282465617097 / 1282465617097)) (n := 12)
    (lo := (447841883 / 1000000000)) (hi := (111960471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782465617097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782465617097 / 500000000000) = 1/(500000000000 / 782465617097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (447841883 / 1000000000) (111960471 / 250000000) (Real.log (782465617097 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (782465617097 / 500000000000) = -Real.log (500000000000 / 782465617097) := by
    rw [show ((782465617097 / 500000000000) : ℝ) = ((500000000000 / 782465617097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0430
