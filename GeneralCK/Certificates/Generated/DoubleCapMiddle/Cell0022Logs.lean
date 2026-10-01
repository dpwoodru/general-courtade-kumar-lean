import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0022
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

theorem reflection_log_1_neg : (198417109 / 500000000) ≤ -Real.log (2560 / 3807) ∧
    -Real.log (2560 / 3807) ≤ (396834219 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 6367)) (n := 12)
    (lo := (198417109 / 500000000)) (hi := (396834219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3807 / 2560) = 1/(2560 / 3807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198417109 / 500000000) (396834219 / 1000000000) (Real.log (3807 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3807 / 2560) = -Real.log (2560 / 3807) := by
    rw [show ((3807 / 2560) : ℝ) = ((2560 / 3807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (667692663 / 1000000000) ≤ -Real.log (1313 / 2560) ∧
    -Real.log (1313 / 2560) ≤ (83461583 / 125000000) := by
  have h := checkLog_sound (w := (1247 / 3873)) (n := 12)
    (lo := (667692663 / 1000000000)) (hi := (83461583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1313) = 1/(1313 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83461583 / 125000000) (-667692663 / 1000000000) (Real.log (1313 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198022943 / 500000000) ≤ -Real.log (640 / 951) ∧
    -Real.log (640 / 951) ≤ (396045887 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1591)) (n := 12)
    (lo := (198022943 / 500000000)) (hi := (396045887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 640) = 1/(640 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198022943 / 500000000) (396045887 / 1000000000) (Real.log (951 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (951 / 640) = -Real.log (640 / 951) := by
    rw [show ((951 / 640) : ℝ) = ((640 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26616417 / 40000000) ≤ -Real.log (329 / 640) ∧
    -Real.log (329 / 640) ≤ (332705213 / 500000000) := by
  have h := checkLog_sound (w := (311 / 969)) (n := 12)
    (lo := (26616417 / 40000000)) (hi := (332705213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 329) = 1/(329 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332705213 / 500000000) (-26616417 / 40000000) (Real.log (329 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2720691 / 4000000) ≤ -Real.log (1280 / 2527) ∧
    -Real.log (1280 / 2527) ≤ (680172751 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 3807)) (n := 12)
    (lo := (2720691 / 4000000)) (hi := (680172751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2527 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2527 / 1280) = 1/(1280 / 2527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2720691 / 4000000) (680172751 / 1000000000) (Real.log (2527 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2527 / 1280) = -Real.log (1280 / 2527) := by
    rw [show ((2527 / 1280) : ℝ) = ((1280 / 2527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (228631737 / 62500000) ≤ -Real.log (33 / 1280) ∧
    -Real.log (33 / 1280) ≤ (1829053899 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 33) = 1/(33 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1829053899 / 500000000) (-228631737 / 62500000) (Real.log (33 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (339492433 / 500000000) ≤ -Real.log (320 / 631) ∧
    -Real.log (320 / 631) ≤ (678984867 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 951)) (n := 12)
    (lo := (339492433 / 500000000)) (hi := (678984867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 320) = 1/(320 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (339492433 / 500000000) (678984867 / 1000000000) (Real.log (631 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631 / 320) = -Real.log (320 / 631) := by
    rw [show ((631 / 320) : ℝ) = ((320 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (714219283 / 200000000) ≤ -Real.log (9 / 320) ∧
    -Real.log (9 / 320) ≤ (3571096421 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10 / 9) = 1/(9 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3571096421 / 1000000000) (-714219283 / 200000000) (Real.log (9 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277799867 / 500000000) ≤ -Real.log (500000 / 871493) ∧
    -Real.log (500000 / 871493) ≤ (111119947 / 200000000) := by
  have h := checkLog_sound (w := (371493 / 1371493)) (n := 12)
    (lo := (277799867 / 500000000)) (hi := (111119947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871493 / 500000) = 1/(500000 / 871493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277799867 / 500000000) (111119947 / 200000000) (Real.log (871493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (871493 / 500000) = -Real.log (500000 / 871493) := by
    rw [show ((871493 / 500000) : ℝ) = ((500000 / 871493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16982809 / 12500000) ≤ -Real.log (128507 / 500000) ∧
    -Real.log (128507 / 500000) ≤ (679312361 / 500000000) := by
  have h := checkLog_sound (w := (121493 / 378507)) (n := 12)
    (lo := (33273877 / 50000000)) (hi := (665477541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 128507) = 1/(128507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-679312361 / 500000000) (-16982809 / 12500000) (Real.log (128507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (557102919 / 1000000000) ≤ -Real.log (125000 / 218201) ∧
    -Real.log (125000 / 218201) ≤ (13927573 / 25000000) := by
  have h := checkLog_sound (w := (93201 / 343201)) (n := 12)
    (lo := (557102919 / 1000000000)) (hi := (13927573 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218201 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218201 / 125000) = 1/(125000 / 218201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (557102919 / 1000000000) (13927573 / 25000000) (Real.log (218201 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (218201 / 125000) = -Real.log (125000 / 218201) := by
    rw [show ((218201 / 125000) : ℝ) = ((125000 / 218201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1368878893 / 1000000000) ≤ -Real.log (31799 / 125000) ∧
    -Real.log (31799 / 125000) ≤ (273775779 / 200000000) := by
  have h := checkLog_sound (w := (30701 / 94299)) (n := 12)
    (lo := (675731713 / 1000000000)) (hi := (337865857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 31799) = 1/(31799 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-273775779 / 200000000) (-1368878893 / 1000000000) (Real.log (31799 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (48114879 / 100000000) ≤ -Real.log (250000 / 404483) ∧
    -Real.log (250000 / 404483) ≤ (481148791 / 1000000000) := by
  have h := checkLog_sound (w := (154483 / 654483)) (n := 12)
    (lo := (48114879 / 100000000)) (hi := (481148791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404483 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404483 / 250000) = 1/(250000 / 404483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (48114879 / 100000000) (481148791 / 1000000000) (Real.log (404483 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (404483 / 250000) = -Real.log (250000 / 404483) := by
    rw [show ((404483 / 250000) : ℝ) = ((250000 / 404483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (38486267 / 40000000) ≤ -Real.log (95517 / 250000) ∧
    -Real.log (95517 / 250000) ≤ (962156677 / 1000000000) := by
  have h := checkLog_sound (w := (29483 / 220517)) (n := 12)
    (lo := (53801899 / 200000000)) (hi := (33626187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 95517) = 1/(95517 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-962156677 / 1000000000) (-38486267 / 40000000) (Real.log (95517 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24146949 / 50000000) ≤ -Real.log (1000000 / 1620831) ∧
    -Real.log (1000000 / 1620831) ≤ (482938981 / 1000000000) := by
  have h := checkLog_sound (w := (620831 / 2620831)) (n := 12)
    (lo := (24146949 / 50000000)) (hi := (482938981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1620831 / 1000000) = 1/(1000000 / 1620831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24146949 / 50000000) (482938981 / 1000000000) (Real.log (1620831 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1620831 / 1000000) = -Real.log (1000000 / 1620831) := by
    rw [show ((1620831 / 1000000) : ℝ) = ((1000000 / 1620831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (484886631 / 500000000) ≤ -Real.log (379169 / 1000000) ∧
    -Real.log (379169 / 1000000) ≤ (60610829 / 62500000) := by
  have h := checkLog_sound (w := (120831 / 879169)) (n := 12)
    (lo := (138313041 / 500000000)) (hi := (276626083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 379169) = 1/(379169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60610829 / 62500000) (-484886631 / 500000000) (Real.log (379169 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (957112227 / 500000000) ≤ -Real.log (250000000000 / 1695419315679) ∧
    -Real.log (250000000000 / 1695419315679) ≤ (1914224457 / 1000000000) := by
  have h := checkLog_sound (w := (695419315679 / 2695419315679)) (n := 12)
    (lo := (263965047 / 500000000)) (hi := (105586019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695419315679 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1695419315679 / 1000000000000) = 1/(250000000000 / 1695419315679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (957112227 / 500000000) (1914224457 / 1000000000) (Real.log (1695419315679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1695419315679 / 250000000000) = -Real.log (250000000000 / 1695419315679) := by
    rw [show ((1695419315679 / 250000000000) : ℝ) = ((250000000000 / 1695419315679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (481495453 / 250000000) ≤ -Real.log (500000000000 / 3430941224567) ∧
    -Real.log (500000000000 / 3430941224567) ≤ (385196363 / 200000000) := by
  have h := checkLog_sound (w := (1430941224567 / 5430941224567)) (n := 12)
    (lo := (134921863 / 250000000)) (hi := (539687453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3430941224567 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3430941224567 / 2000000000000) = 1/(500000000000 / 3430941224567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (481495453 / 250000000) (385196363 / 200000000) (Real.log (3430941224567 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3430941224567 / 500000000000) = -Real.log (500000000000 / 3430941224567) := by
    rw [show ((3430941224567 / 500000000000) : ℝ) = ((500000000000 / 3430941224567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (288661093 / 200000000) ≤ -Real.log (500000000000 / 2117335134059) ∧
    -Real.log (500000000000 / 2117335134059) ≤ (360826367 / 250000000) := by
  have h := checkLog_sound (w := (117335134059 / 4117335134059)) (n := 12)
    (lo := (11402221 / 200000000)) (hi := (28505553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2117335134059 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2117335134059 / 2000000000000) = 1/(500000000000 / 2117335134059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (288661093 / 200000000) (360826367 / 250000000) (Real.log (2117335134059 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2117335134059 / 500000000000) = -Real.log (500000000000 / 2117335134059) := by
    rw [show ((2117335134059 / 500000000000) : ℝ) = ((500000000000 / 2117335134059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (726356121 / 500000000) ≤ -Real.log (500000000000 / 2137346407539) ∧
    -Real.log (500000000000 / 2137346407539) ≤ (290542449 / 200000000) := by
  have h := checkLog_sound (w := (137346407539 / 4137346407539)) (n := 12)
    (lo := (33208941 / 500000000)) (hi := (66417883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137346407539 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2137346407539 / 2000000000000) = 1/(500000000000 / 2137346407539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (726356121 / 500000000) (290542449 / 200000000) (Real.log (2137346407539 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2137346407539 / 500000000000) = -Real.log (500000000000 / 2137346407539) := by
    rw [show ((2137346407539 / 500000000000) : ℝ) = ((500000000000 / 2137346407539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0022
