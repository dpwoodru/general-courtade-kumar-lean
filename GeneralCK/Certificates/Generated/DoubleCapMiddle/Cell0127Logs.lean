import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0127
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

theorem reflection_log_1_neg : (310467379 / 1000000000) ≤ -Real.log (640 / 873) ∧
    -Real.log (640 / 873) ≤ (15523369 / 50000000) := by
  have h := checkLog_sound (w := (233 / 1513)) (n := 12)
    (lo := (310467379 / 1000000000)) (hi := (15523369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 640) = 1/(640 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310467379 / 1000000000) (15523369 / 50000000) (Real.log (873 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (873 / 640) = -Real.log (640 / 873) := by
    rw [show ((873 / 640) : ℝ) = ((640 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (45265499 / 100000000) ≤ -Real.log (407 / 640) ∧
    -Real.log (407 / 640) ≤ (452654991 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 1047)) (n := 12)
    (lo := (45265499 / 100000000)) (hi := (452654991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 407) = 1/(407 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-452654991 / 1000000000) (-45265499 / 100000000) (Real.log (407 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (309607903 / 1000000000) ≤ -Real.log (2560 / 3489) ∧
    -Real.log (2560 / 3489) ≤ (9675247 / 31250000) := by
  have h := checkLog_sound (w := (929 / 6049)) (n := 12)
    (lo := (309607903 / 1000000000)) (hi := (9675247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3489 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3489 / 2560) = 1/(2560 / 3489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (309607903 / 1000000000) (9675247 / 31250000) (Real.log (3489 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3489 / 2560) = -Real.log (2560 / 3489) := by
    rw [show ((3489 / 2560) : ℝ) = ((2560 / 3489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225406967 / 500000000) ≤ -Real.log (1631 / 2560) ∧
    -Real.log (1631 / 2560) ≤ (90162787 / 200000000) := by
  have h := checkLog_sound (w := (929 / 4191)) (n := 12)
    (lo := (225406967 / 500000000)) (hi := (90162787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1631) = 1/(1631 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-90162787 / 200000000) (-225406967 / 500000000) (Real.log (1631 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (109407401 / 200000000) ≤ -Real.log (320 / 553) ∧
    -Real.log (320 / 553) ≤ (273518503 / 500000000) := by
  have h := checkLog_sound (w := (233 / 873)) (n := 12)
    (lo := (109407401 / 200000000)) (hi := (273518503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(553 / 320) = 1/(320 / 553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (109407401 / 200000000) (273518503 / 500000000) (Real.log (553 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (553 / 320) = -Real.log (320 / 553) := by
    rw [show ((553 / 320) : ℝ) = ((320 / 553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325603219 / 250000000) ≤ -Real.log (87 / 320) ∧
    -Real.log (87 / 320) ≤ (651206439 / 500000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 87) = 1/(87 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-651206439 / 500000000) (-325603219 / 250000000) (Real.log (87 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (272839923 / 500000000) ≤ -Real.log (1280 / 2209) ∧
    -Real.log (1280 / 2209) ≤ (545679847 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 3489)) (n := 12)
    (lo := (272839923 / 500000000)) (hi := (545679847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2209 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2209 / 1280) = 1/(1280 / 2209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (272839923 / 500000000) (545679847 / 1000000000) (Real.log (2209 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2209 / 1280) = -Real.log (1280 / 2209) := by
    rw [show ((2209 / 1280) : ℝ) = ((1280 / 2209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323457283 / 250000000) ≤ -Real.log (351 / 1280) ∧
    -Real.log (351 / 1280) ≤ (646914567 / 500000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 351) = 1/(351 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-646914567 / 500000000) (-323457283 / 250000000) (Real.log (351 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42397147 / 100000000) ≤ -Real.log (500000 / 764009) ∧
    -Real.log (500000 / 764009) ≤ (423971471 / 1000000000) := by
  have h := checkLog_sound (w := (264009 / 1264009)) (n := 12)
    (lo := (42397147 / 100000000)) (hi := (423971471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764009 / 500000) = 1/(500000 / 764009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42397147 / 100000000) (423971471 / 1000000000) (Real.log (764009 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (764009 / 500000) = -Real.log (500000 / 764009) := by
    rw [show ((764009 / 500000) : ℝ) = ((500000 / 764009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (750814429 / 1000000000) ≤ -Real.log (235991 / 500000) ∧
    -Real.log (235991 / 500000) ≤ (750814431 / 1000000000) := by
  have h := checkLog_sound (w := (14009 / 485991)) (n := 12)
    (lo := (57667249 / 1000000000)) (hi := (230669 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235991) = 1/(235991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-750814431 / 1000000000) (-750814429 / 1000000000) (Real.log (235991 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (425172959 / 1000000000) ≤ -Real.log (200000 / 305971) ∧
    -Real.log (200000 / 305971) ≤ (2657331 / 6250000) := by
  have h := checkLog_sound (w := (105971 / 505971)) (n := 12)
    (lo := (425172959 / 1000000000)) (hi := (2657331 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305971 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305971 / 200000) = 1/(200000 / 305971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (425172959 / 1000000000) (2657331 / 6250000) (Real.log (305971 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (305971 / 200000) = -Real.log (200000 / 305971) := by
    rw [show ((305971 / 200000) : ℝ) = ((200000 / 305971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18867853 / 25000000) ≤ -Real.log (94029 / 200000) ∧
    -Real.log (94029 / 200000) ≤ (377357061 / 500000000) := by
  have h := checkLog_sound (w := (5971 / 194029)) (n := 12)
    (lo := (3078347 / 50000000)) (hi := (61566941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94029) = 1/(94029 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-377357061 / 500000000) (-18867853 / 25000000) (Real.log (94029 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33963651 / 100000000) ≤ -Real.log (1000000 / 1404437) ∧
    -Real.log (1000000 / 1404437) ≤ (339636511 / 1000000000) := by
  have h := checkLog_sound (w := (404437 / 2404437)) (n := 12)
    (lo := (33963651 / 100000000)) (hi := (339636511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404437 / 1000000) = 1/(1000000 / 1404437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33963651 / 100000000) (339636511 / 1000000000) (Real.log (1404437 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1404437 / 1000000) = -Real.log (1000000 / 1404437) := by
    rw [show ((1404437 / 1000000) : ℝ) = ((1000000 / 1404437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259124051 / 500000000) ≤ -Real.log (595563 / 1000000) ∧
    -Real.log (595563 / 1000000) ≤ (518248103 / 1000000000) := by
  have h := checkLog_sound (w := (404437 / 1595563)) (n := 12)
    (lo := (259124051 / 500000000)) (hi := (518248103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595563) = 1/(595563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-518248103 / 1000000000) (-259124051 / 500000000) (Real.log (595563 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85201067 / 250000000) ≤ -Real.log (500000 / 703039) ∧
    -Real.log (500000 / 703039) ≤ (340804269 / 1000000000) := by
  have h := checkLog_sound (w := (203039 / 1203039)) (n := 12)
    (lo := (85201067 / 250000000)) (hi := (340804269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703039 / 500000) = 1/(500000 / 703039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85201067 / 250000000) (340804269 / 1000000000) (Real.log (703039 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (703039 / 500000) = -Real.log (500000 / 703039) := by
    rw [show ((703039 / 500000) : ℝ) = ((500000 / 703039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (521007281 / 1000000000) ≤ -Real.log (296961 / 500000) ∧
    -Real.log (296961 / 500000) ≤ (260503641 / 500000000) := by
  have h := checkLog_sound (w := (203039 / 796961)) (n := 12)
    (lo := (521007281 / 1000000000)) (hi := (260503641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296961) = 1/(296961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260503641 / 500000000) (-521007281 / 1000000000) (Real.log (296961 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1174785899 / 1000000000) ≤ -Real.log (250000000000 / 809362433313) ∧
    -Real.log (250000000000 / 809362433313) ≤ (1174785901 / 1000000000) := by
  have h := checkLog_sound (w := (309362433313 / 1309362433313)) (n := 12)
    (lo := (481638719 / 1000000000)) (hi := (1505121 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809362433313 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(809362433313 / 500000000000) = 1/(250000000000 / 809362433313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1174785899 / 1000000000) (1174785901 / 1000000000) (Real.log (809362433313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (809362433313 / 250000000000) = -Real.log (250000000000 / 809362433313) := by
    rw [show ((809362433313 / 250000000000) : ℝ) = ((250000000000 / 809362433313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (29497177 / 25000000) ≤ -Real.log (500000000000 / 1627003371301) ∧
    -Real.log (500000000000 / 1627003371301) ≤ (589943541 / 500000000) := by
  have h := checkLog_sound (w := (627003371301 / 2627003371301)) (n := 12)
    (lo := (4867399 / 10000000)) (hi := (486739901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627003371301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1627003371301 / 1000000000000) = 1/(500000000000 / 1627003371301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (29497177 / 25000000) (589943541 / 500000000) (Real.log (1627003371301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1627003371301 / 500000000000) = -Real.log (500000000000 / 1627003371301) := by
    rw [show ((1627003371301 / 500000000000) : ℝ) = ((500000000000 / 1627003371301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (214471153 / 250000000) ≤ -Real.log (125000000000 / 294770872267) ∧
    -Real.log (125000000000 / 294770872267) ≤ (428942307 / 500000000) := by
  have h := checkLog_sound (w := (44770872267 / 544770872267)) (n := 12)
    (lo := (20592179 / 125000000)) (hi := (164737433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294770872267 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(294770872267 / 250000000000) = 1/(125000000000 / 294770872267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (214471153 / 250000000) (428942307 / 500000000) (Real.log (294770872267 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (294770872267 / 125000000000) = -Real.log (125000000000 / 294770872267) := by
    rw [show ((294770872267 / 125000000000) : ℝ) = ((125000000000 / 294770872267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (861811549 / 1000000000) ≤ -Real.log (125000000000 / 295930694603) ∧
    -Real.log (125000000000 / 295930694603) ≤ (861811551 / 1000000000) := by
  have h := checkLog_sound (w := (45930694603 / 545930694603)) (n := 12)
    (lo := (168664369 / 1000000000)) (hi := (16866437 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295930694603 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295930694603 / 250000000000) = 1/(125000000000 / 295930694603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (861811549 / 1000000000) (861811551 / 1000000000) (Real.log (295930694603 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (295930694603 / 125000000000) = -Real.log (125000000000 / 295930694603) := by
    rw [show ((295930694603 / 125000000000) : ℝ) = ((125000000000 / 295930694603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0127
