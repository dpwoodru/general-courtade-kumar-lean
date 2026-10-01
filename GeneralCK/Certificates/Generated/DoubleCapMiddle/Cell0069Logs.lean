import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0069
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

theorem reflection_log_1_neg : (35909389 / 100000000) ≤ -Real.log (1280 / 1833) ∧
    -Real.log (1280 / 1833) ≤ (359093891 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3113)) (n := 12)
    (lo := (35909389 / 100000000)) (hi := (359093891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1280) = 1/(1280 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (35909389 / 100000000) (359093891 / 1000000000) (Real.log (1833 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1833 / 1280) = -Real.log (1280 / 1833) := by
    rw [show ((1833 / 1280) : ℝ) = ((1280 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (565688879 / 1000000000) ≤ -Real.log (727 / 1280) ∧
    -Real.log (727 / 1280) ≤ (7071111 / 12500000) := by
  have h := checkLog_sound (w := (553 / 2007)) (n := 12)
    (lo := (565688879 / 1000000000)) (hi := (7071111 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 727) = 1/(727 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) (Real.log (727 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14331009 / 40000000) ≤ -Real.log (2560 / 3663) ∧
    -Real.log (2560 / 3663) ≤ (179137613 / 500000000) := by
  have h := checkLog_sound (w := (1103 / 6223)) (n := 12)
    (lo := (14331009 / 40000000)) (hi := (179137613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3663 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3663 / 2560) = 1/(2560 / 3663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14331009 / 40000000) (179137613 / 500000000) (Real.log (3663 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3663 / 2560) = -Real.log (2560 / 3663) := by
    rw [show ((3663 / 2560) : ℝ) = ((2560 / 3663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (563627731 / 1000000000) ≤ -Real.log (1457 / 2560) ∧
    -Real.log (1457 / 2560) ≤ (140906933 / 250000000) := by
  have h := checkLog_sound (w := (1103 / 4017)) (n := 12)
    (lo := (563627731 / 1000000000)) (hi := (140906933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1457) = 1/(1457 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) (Real.log (1457 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124551649 / 200000000) ≤ -Real.log (640 / 1193) ∧
    -Real.log (640 / 1193) ≤ (311379123 / 500000000) := by
  have h := checkLog_sound (w := (553 / 1833)) (n := 12)
    (lo := (124551649 / 200000000)) (hi := (311379123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 640) = 1/(640 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124551649 / 200000000) (311379123 / 500000000) (Real.log (1193 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1193 / 640) = -Real.log (640 / 1193) := by
    rw [show ((1193 / 640) : ℝ) = ((640 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (249445007 / 125000000) ≤ -Real.log (87 / 640) ∧
    -Real.log (87 / 640) ≤ (1995560059 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 87) = 1/(87 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) (Real.log (87 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15537503 / 25000000) ≤ -Real.log (1280 / 2383) ∧
    -Real.log (1280 / 2383) ≤ (621500121 / 1000000000) := by
  have h := checkLog_sound (w := (1103 / 3663)) (n := 12)
    (lo := (15537503 / 25000000)) (hi := (621500121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 1280) = 1/(1280 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15537503 / 25000000) (621500121 / 1000000000) (Real.log (2383 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2383 / 1280) = -Real.log (1280 / 2383) := by
    rw [show ((2383 / 1280) : ℝ) = ((1280 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1978465623 / 1000000000) ≤ -Real.log (177 / 1280) ∧
    -Real.log (177 / 1280) ≤ (989232813 / 500000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 177) = 1/(177 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) (Real.log (177 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (123495643 / 250000000) ≤ -Real.log (100000 / 163883) ∧
    -Real.log (100000 / 163883) ≤ (493982573 / 1000000000) := by
  have h := checkLog_sound (w := (63883 / 263883)) (n := 12)
    (lo := (123495643 / 250000000)) (hi := (493982573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163883 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163883 / 100000) = 1/(100000 / 163883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (123495643 / 250000000) (493982573 / 1000000000) (Real.log (163883 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (163883 / 100000) = -Real.log (100000 / 163883) := by
    rw [show ((163883 / 100000) : ℝ) = ((100000 / 163883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (254601629 / 250000000) ≤ -Real.log (36117 / 100000) ∧
    -Real.log (36117 / 100000) ≤ (509203259 / 500000000) := by
  have h := checkLog_sound (w := (13883 / 86117)) (n := 12)
    (lo := (40657417 / 125000000)) (hi := (325259337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36117) = 1/(36117 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-509203259 / 500000000) (-254601629 / 250000000) (Real.log (36117 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (495213181 / 1000000000) ≤ -Real.log (62500 / 102553) ∧
    -Real.log (62500 / 102553) ≤ (247606591 / 500000000) := by
  have h := checkLog_sound (w := (40053 / 165053)) (n := 12)
    (lo := (495213181 / 1000000000)) (hi := (247606591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102553 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102553 / 62500) = 1/(62500 / 102553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (495213181 / 1000000000) (247606591 / 500000000) (Real.log (102553 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (102553 / 62500) = -Real.log (62500 / 102553) := by
    rw [show ((102553 / 62500) : ℝ) = ((62500 / 102553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1024009581 / 1000000000) ≤ -Real.log (22447 / 62500) ∧
    -Real.log (22447 / 62500) ≤ (1024009583 / 1000000000) := by
  have h := checkLog_sound (w := (8803 / 53697)) (n := 12)
    (lo := (330862401 / 1000000000)) (hi := (165431201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22447) = 1/(22447 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1024009583 / 1000000000) (-1024009581 / 1000000000) (Real.log (22447 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (82241849 / 200000000) ≤ -Real.log (1000000 / 1508641) ∧
    -Real.log (1000000 / 1508641) ≤ (205604623 / 500000000) := by
  have h := checkLog_sound (w := (508641 / 2508641)) (n := 12)
    (lo := (82241849 / 200000000)) (hi := (205604623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1508641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1508641 / 1000000) = 1/(1000000 / 1508641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (82241849 / 200000000) (205604623 / 500000000) (Real.log (1508641 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1508641 / 1000000) = -Real.log (1000000 / 1508641) := by
    rw [show ((1508641 / 1000000) : ℝ) = ((1000000 / 1508641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (22205633 / 31250000) ≤ -Real.log (491359 / 1000000) ∧
    -Real.log (491359 / 1000000) ≤ (355290129 / 500000000) := by
  have h := checkLog_sound (w := (8641 / 991359)) (n := 12)
    (lo := (4358269 / 250000000)) (hi := (17433077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 491359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 491359) = 1/(491359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-355290129 / 500000000) (-22205633 / 31250000) (Real.log (491359 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (82507607 / 200000000) ≤ -Real.log (1000000 / 1510647) ∧
    -Real.log (1000000 / 1510647) ≤ (103134509 / 250000000) := by
  have h := checkLog_sound (w := (510647 / 2510647)) (n := 12)
    (lo := (82507607 / 200000000)) (hi := (103134509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1510647 / 1000000) = 1/(1000000 / 1510647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (82507607 / 200000000) (103134509 / 250000000) (Real.log (1510647 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1510647 / 1000000) = -Real.log (1000000 / 1510647) := by
    rw [show ((1510647 / 1000000) : ℝ) = ((1000000 / 1510647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (714671167 / 1000000000) ≤ -Real.log (489353 / 1000000) ∧
    -Real.log (489353 / 1000000) ≤ (714671169 / 1000000000) := by
  have h := checkLog_sound (w := (10647 / 989353)) (n := 12)
    (lo := (21523987 / 1000000000)) (hi := (5380997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 489353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 489353) = 1/(489353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-714671169 / 1000000000) (-714671167 / 1000000000) (Real.log (489353 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (47262159 / 31250000) ≤ -Real.log (50000000000 / 226877924523) ∧
    -Real.log (50000000000 / 226877924523) ≤ (1512389091 / 1000000000) := by
  have h := checkLog_sound (w := (26877924523 / 426877924523)) (n := 12)
    (lo := (15761841 / 125000000)) (hi := (126094729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226877924523 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(226877924523 / 200000000000) = 1/(50000000000 / 226877924523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (47262159 / 31250000) (1512389091 / 1000000000) (Real.log (226877924523 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (226877924523 / 50000000000) = -Real.log (50000000000 / 226877924523) := by
    rw [show ((226877924523 / 50000000000) : ℝ) = ((50000000000 / 226877924523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (759611381 / 500000000) ≤ -Real.log (500000000000 / 2284336436941) ∧
    -Real.log (500000000000 / 2284336436941) ≤ (303844553 / 200000000) := by
  have h := checkLog_sound (w := (284336436941 / 4284336436941)) (n := 12)
    (lo := (66464201 / 500000000)) (hi := (132928403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2284336436941 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2284336436941 / 2000000000000) = 1/(500000000000 / 2284336436941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (759611381 / 500000000) (303844553 / 200000000) (Real.log (2284336436941 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2284336436941 / 500000000000) = -Real.log (500000000000 / 2284336436941) := by
    rw [show ((2284336436941 / 500000000000) : ℝ) = ((500000000000 / 2284336436941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (560894751 / 500000000) ≤ -Real.log (250000000000 / 767585919867) ∧
    -Real.log (250000000000 / 767585919867) ≤ (17527961 / 15625000) := by
  have h := checkLog_sound (w := (267585919867 / 1267585919867)) (n := 12)
    (lo := (214321161 / 500000000)) (hi := (428642323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767585919867 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(767585919867 / 500000000000) = 1/(250000000000 / 767585919867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (560894751 / 500000000) (17527961 / 15625000) (Real.log (767585919867 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (767585919867 / 250000000000) = -Real.log (250000000000 / 767585919867) := by
    rw [show ((767585919867 / 250000000000) : ℝ) = ((250000000000 / 767585919867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1127209203 / 1000000000) ≤ -Real.log (500000000000 / 1543514599891) ∧
    -Real.log (500000000000 / 1543514599891) ≤ (225441841 / 200000000) := by
  have h := checkLog_sound (w := (543514599891 / 2543514599891)) (n := 12)
    (lo := (434062023 / 1000000000)) (hi := (54257753 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1543514599891 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1543514599891 / 1000000000000) = 1/(500000000000 / 1543514599891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1127209203 / 1000000000) (225441841 / 200000000) (Real.log (1543514599891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1543514599891 / 500000000000) = -Real.log (500000000000 / 1543514599891) := by
    rw [show ((1543514599891 / 500000000000) : ℝ) = ((500000000000 / 1543514599891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0069
