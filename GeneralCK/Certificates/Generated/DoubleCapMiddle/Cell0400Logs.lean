import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0400
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

theorem reflection_log_1_neg : (12514169 / 62500000) ≤ -Real.log (1024 / 1251) ∧
    -Real.log (1024 / 1251) ≤ (40045341 / 200000000) := by
  have h := checkLog_sound (w := (227 / 2275)) (n := 12)
    (lo := (12514169 / 62500000)) (hi := (40045341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1024) = 1/(1024 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12514169 / 62500000) (40045341 / 200000000) (Real.log (1251 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1251 / 1024) = -Real.log (1024 / 1251) := by
    rw [show ((1251 / 1024) : ℝ) = ((1024 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (125308563 / 500000000) ≤ -Real.log (797 / 1024) ∧
    -Real.log (797 / 1024) ≤ (250617127 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1821)) (n := 12)
    (lo := (125308563 / 500000000)) (hi := (250617127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 797) = 1/(797 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-250617127 / 1000000000) (-125308563 / 500000000) (Real.log (797 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199986867 / 1000000000) ≤ -Real.log (10240 / 12507) ∧
    -Real.log (10240 / 12507) ≤ (49996717 / 250000000) := by
  have h := checkLog_sound (w := (2267 / 22747)) (n := 12)
    (lo := (199986867 / 1000000000)) (hi := (49996717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 10240) = 1/(10240 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199986867 / 1000000000) (49996717 / 250000000) (Real.log (12507 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12507 / 10240) = -Real.log (10240 / 12507) := by
    rw [show ((12507 / 10240) : ℝ) = ((10240 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (125120393 / 500000000) ≤ -Real.log (7973 / 10240) ∧
    -Real.log (7973 / 10240) ≤ (250240787 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 18213)) (n := 12)
    (lo := (125120393 / 500000000)) (hi := (250240787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7973) = 1/(7973 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-250240787 / 1000000000) (-125120393 / 500000000) (Real.log (7973 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73394659 / 200000000) ≤ -Real.log (512 / 739) ∧
    -Real.log (512 / 739) ≤ (22935831 / 62500000) := by
  have h := checkLog_sound (w := (227 / 1251)) (n := 12)
    (lo := (73394659 / 200000000)) (hi := (22935831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 512) = 1/(512 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73394659 / 200000000) (22935831 / 62500000) (Real.log (739 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (739 / 512) = -Real.log (512 / 739) := by
    rw [show ((739 / 512) : ℝ) = ((512 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146458861 / 250000000) ≤ -Real.log (285 / 512) ∧
    -Real.log (285 / 512) ≤ (117167089 / 200000000) := by
  have h := checkLog_sound (w := (227 / 797)) (n := 12)
    (lo := (146458861 / 250000000)) (hi := (117167089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 285) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 285) = 1/(285 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-117167089 / 200000000) (-146458861 / 250000000) (Real.log (285 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (366567259 / 1000000000) ≤ -Real.log (5120 / 7387) ∧
    -Real.log (5120 / 7387) ≤ (18328363 / 50000000) := by
  have h := checkLog_sound (w := (2267 / 12507)) (n := 12)
    (lo := (366567259 / 1000000000)) (hi := (18328363 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7387 / 5120) = 1/(5120 / 7387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (366567259 / 1000000000) (18328363 / 50000000) (Real.log (7387 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7387 / 5120) = -Real.log (5120 / 7387) := by
    rw [show ((7387 / 5120) : ℝ) = ((5120 / 7387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (292391683 / 500000000) ≤ -Real.log (2853 / 5120) ∧
    -Real.log (2853 / 5120) ≤ (584783367 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 7973)) (n := 12)
    (lo := (292391683 / 500000000)) (hi := (584783367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2853) = 1/(2853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-584783367 / 1000000000) (-292391683 / 500000000) (Real.log (2853 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (274504123 / 1000000000) ≤ -Real.log (500000 / 657939) ∧
    -Real.log (500000 / 657939) ≤ (68626031 / 250000000) := by
  have h := checkLog_sound (w := (157939 / 1157939)) (n := 12)
    (lo := (274504123 / 1000000000)) (hi := (68626031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657939 / 500000) = 1/(500000 / 657939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (274504123 / 1000000000) (68626031 / 250000000) (Real.log (657939 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657939 / 500000) = -Real.log (500000 / 657939) := by
    rw [show ((657939 / 500000) : ℝ) = ((500000 / 657939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (189809507 / 500000000) ≤ -Real.log (342061 / 500000) ∧
    -Real.log (342061 / 500000) ≤ (75923803 / 200000000) := by
  have h := checkLog_sound (w := (157939 / 842061)) (n := 12)
    (lo := (189809507 / 500000000)) (hi := (75923803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342061) = 1/(342061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-75923803 / 200000000) (-189809507 / 500000000) (Real.log (342061 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34353571 / 125000000) ≤ -Real.log (200000 / 263261) ∧
    -Real.log (200000 / 263261) ≤ (274828569 / 1000000000) := by
  have h := checkLog_sound (w := (63261 / 463261)) (n := 12)
    (lo := (34353571 / 125000000)) (hi := (274828569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263261 / 200000) = 1/(200000 / 263261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34353571 / 125000000) (274828569 / 1000000000) (Real.log (263261 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (263261 / 200000) = -Real.log (200000 / 263261) := by
    rw [show ((263261 / 200000) : ℝ) = ((200000 / 263261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (380243367 / 1000000000) ≤ -Real.log (136739 / 200000) ∧
    -Real.log (136739 / 200000) ≤ (47530421 / 125000000) := by
  have h := checkLog_sound (w := (63261 / 336739)) (n := 12)
    (lo := (380243367 / 1000000000)) (hi := (47530421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136739) = 1/(136739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-47530421 / 125000000) (-380243367 / 1000000000) (Real.log (136739 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20677349 / 100000000) ≤ -Real.log (125000 / 153713) ∧
    -Real.log (125000 / 153713) ≤ (206773491 / 1000000000) := by
  have h := checkLog_sound (w := (28713 / 278713)) (n := 12)
    (lo := (20677349 / 100000000)) (hi := (206773491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153713 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153713 / 125000) = 1/(125000 / 153713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20677349 / 100000000) (206773491 / 1000000000) (Real.log (153713 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (153713 / 125000) = -Real.log (125000 / 153713) := by
    rw [show ((153713 / 125000) : ℝ) = ((125000 / 153713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130490211 / 500000000) ≤ -Real.log (96287 / 125000) ∧
    -Real.log (96287 / 125000) ≤ (260980423 / 1000000000) := by
  have h := checkLog_sound (w := (28713 / 221287)) (n := 12)
    (lo := (130490211 / 500000000)) (hi := (260980423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96287) = 1/(96287 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260980423 / 1000000000) (-130490211 / 500000000) (Real.log (96287 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (41408037 / 200000000) ≤ -Real.log (62500 / 76877) ∧
    -Real.log (62500 / 76877) ≤ (103520093 / 500000000) := by
  have h := checkLog_sound (w := (14377 / 139377)) (n := 12)
    (lo := (41408037 / 200000000)) (hi := (103520093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76877 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76877 / 62500) = 1/(62500 / 76877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (41408037 / 200000000) (103520093 / 500000000) (Real.log (76877 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76877 / 62500) = -Real.log (62500 / 76877) := by
    rw [show ((76877 / 62500) : ℝ) = ((62500 / 76877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (261406323 / 1000000000) ≤ -Real.log (48123 / 62500) ∧
    -Real.log (48123 / 62500) ≤ (65351581 / 250000000) := by
  have h := checkLog_sound (w := (14377 / 110623)) (n := 12)
    (lo := (261406323 / 1000000000)) (hi := (65351581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48123) = 1/(48123 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-65351581 / 250000000) (-261406323 / 1000000000) (Real.log (48123 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (327061569 / 500000000) ≤ -Real.log (2500000000 / 4808637933) ∧
    -Real.log (2500000000 / 4808637933) ≤ (654123139 / 1000000000) := by
  have h := checkLog_sound (w := (2308637933 / 7308637933)) (n := 12)
    (lo := (327061569 / 500000000)) (hi := (654123139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4808637933 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4808637933 / 2500000000) = 1/(2500000000 / 4808637933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (327061569 / 500000000) (654123139 / 1000000000) (Real.log (4808637933 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4808637933 / 2500000000) = -Real.log (2500000000 / 4808637933) := by
    rw [show ((4808637933 / 2500000000) : ℝ) = ((2500000000 / 4808637933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (10235499 / 15625000) ≤ -Real.log (62500000000 / 120330063113) ∧
    -Real.log (62500000000 / 120330063113) ≤ (655071937 / 1000000000) := by
  have h := checkLog_sound (w := (57830063113 / 182830063113)) (n := 12)
    (lo := (10235499 / 15625000)) (hi := (655071937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120330063113 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120330063113 / 62500000000) = 1/(62500000000 / 120330063113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (10235499 / 15625000) (655071937 / 1000000000) (Real.log (120330063113 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (120330063113 / 62500000000) = -Real.log (62500000000 / 120330063113) := by
    rw [show ((120330063113 / 62500000000) : ℝ) = ((62500000000 / 120330063113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (58469239 / 125000000) ≤ -Real.log (125000000000 / 199550562381) ∧
    -Real.log (125000000000 / 199550562381) ≤ (467753913 / 1000000000) := by
  have h := checkLog_sound (w := (74550562381 / 324550562381)) (n := 12)
    (lo := (58469239 / 125000000)) (hi := (467753913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199550562381 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199550562381 / 125000000000) = 1/(125000000000 / 199550562381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (58469239 / 125000000) (467753913 / 1000000000) (Real.log (199550562381 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (199550562381 / 125000000000) = -Real.log (125000000000 / 199550562381) := by
    rw [show ((199550562381 / 125000000000) : ℝ) = ((125000000000 / 199550562381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117111627 / 250000000) ≤ -Real.log (500000000000 / 798755272947) ∧
    -Real.log (500000000000 / 798755272947) ≤ (468446509 / 1000000000) := by
  have h := checkLog_sound (w := (298755272947 / 1298755272947)) (n := 12)
    (lo := (117111627 / 250000000)) (hi := (468446509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798755272947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798755272947 / 500000000000) = 1/(500000000000 / 798755272947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117111627 / 250000000) (468446509 / 1000000000) (Real.log (798755272947 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (798755272947 / 500000000000) = -Real.log (500000000000 / 798755272947) := by
    rw [show ((798755272947 / 500000000000) : ℝ) = ((500000000000 / 798755272947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0400
