import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0300
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

theorem reflection_log_1_neg : (13995281 / 62500000) ≤ -Real.log (1024 / 1281) ∧
    -Real.log (1024 / 1281) ≤ (223924497 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2305)) (n := 12)
    (lo := (13995281 / 62500000)) (hi := (223924497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281 / 1024) = 1/(1024 / 1281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13995281 / 62500000) (223924497 / 1000000000) (Real.log (1281 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1281 / 1024) = -Real.log (1024 / 1281) := by
    rw [show ((1281 / 1024) : ℝ) = ((1024 / 1281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (72246251 / 250000000) ≤ -Real.log (767 / 1024) ∧
    -Real.log (767 / 1024) ≤ (57797001 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1791)) (n := 12)
    (lo := (72246251 / 250000000)) (hi := (57797001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 767) = 1/(767 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57797001 / 200000000) (-72246251 / 250000000) (Real.log (767 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55922569 / 250000000) ≤ -Real.log (10240 / 12807) ∧
    -Real.log (10240 / 12807) ≤ (223690277 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 23047)) (n := 12)
    (lo := (55922569 / 250000000)) (hi := (223690277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12807 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12807 / 10240) = 1/(10240 / 12807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55922569 / 250000000) (223690277 / 1000000000) (Real.log (12807 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12807 / 10240) = -Real.log (10240 / 12807) := by
    rw [show ((12807 / 10240) : ℝ) = ((10240 / 12807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144296973 / 500000000) ≤ -Real.log (7673 / 10240) ∧
    -Real.log (7673 / 10240) ≤ (288593947 / 1000000000) := by
  have h := checkLog_sound (w := (2567 / 17913)) (n := 12)
    (lo := (144296973 / 500000000)) (hi := (288593947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7673) = 1/(7673 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-288593947 / 1000000000) (-144296973 / 500000000) (Real.log (7673 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50845793 / 125000000) ≤ -Real.log (512 / 769) ∧
    -Real.log (512 / 769) ≤ (81353269 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1281)) (n := 12)
    (lo := (50845793 / 125000000)) (hi := (81353269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769 / 512) = 1/(512 / 769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50845793 / 125000000) (81353269 / 200000000) (Real.log (769 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (769 / 512) = -Real.log (512 / 769) := by
    rw [show ((769 / 512) : ℝ) = ((512 / 769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697061079 / 1000000000) ≤ -Real.log (255 / 512) ∧
    -Real.log (255 / 512) ≤ (697061081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 511)) (n := 12)
    (lo := (3913899 / 1000000000)) (hi := (39139 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 255) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 255) = 1/(255 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-697061081 / 1000000000) (-697061079 / 1000000000) (Real.log (255 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (406376151 / 1000000000) ≤ -Real.log (5120 / 7687) ∧
    -Real.log (5120 / 7687) ≤ (50797019 / 125000000) := by
  have h := checkLog_sound (w := (2567 / 12807)) (n := 12)
    (lo := (406376151 / 1000000000)) (hi := (50797019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7687 / 5120) = 1/(5120 / 7687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (406376151 / 1000000000) (50797019 / 125000000) (Real.log (7687 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7687 / 5120) = -Real.log (5120 / 7687) := by
    rw [show ((7687 / 5120) : ℝ) = ((5120 / 7687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6958853 / 10000000) ≤ -Real.log (2553 / 5120) ∧
    -Real.log (2553 / 5120) ≤ (347942651 / 500000000) := by
  have h := checkLog_sound (w := (7 / 5113)) (n := 12)
    (lo := (68453 / 25000000)) (hi := (2738121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2553) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2553) = 1/(2553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-347942651 / 500000000) (-6958853 / 10000000) (Real.log (2553 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38314389 / 125000000) ≤ -Real.log (500000 / 679341) ∧
    -Real.log (500000 / 679341) ≤ (306515113 / 1000000000) := by
  have h := checkLog_sound (w := (179341 / 1179341)) (n := 12)
    (lo := (38314389 / 125000000)) (hi := (306515113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679341 / 500000) = 1/(500000 / 679341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38314389 / 125000000) (306515113 / 1000000000) (Real.log (679341 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (679341 / 500000) = -Real.log (500000 / 679341) := by
    rw [show ((679341 / 500000) : ℝ) = ((500000 / 679341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88845969 / 200000000) ≤ -Real.log (320659 / 500000) ∧
    -Real.log (320659 / 500000) ≤ (222114923 / 500000000) := by
  have h := checkLog_sound (w := (179341 / 820659)) (n := 12)
    (lo := (88845969 / 200000000)) (hi := (222114923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320659) = 1/(320659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-222114923 / 500000000) (-88845969 / 200000000) (Real.log (320659 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (306832281 / 1000000000) ≤ -Real.log (1000000 / 1359113) ∧
    -Real.log (1000000 / 1359113) ≤ (153416141 / 500000000) := by
  have h := checkLog_sound (w := (359113 / 2359113)) (n := 12)
    (lo := (306832281 / 1000000000)) (hi := (153416141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359113 / 1000000) = 1/(1000000 / 1359113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (306832281 / 1000000000) (153416141 / 500000000) (Real.log (1359113 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1359113 / 1000000) = -Real.log (1000000 / 1359113) := by
    rw [show ((1359113 / 1000000) : ℝ) = ((1000000 / 1359113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111225531 / 250000000) ≤ -Real.log (640887 / 1000000) ∧
    -Real.log (640887 / 1000000) ≤ (3559217 / 8000000) := by
  have h := checkLog_sound (w := (359113 / 1640887)) (n := 12)
    (lo := (111225531 / 250000000)) (hi := (3559217 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640887) = 1/(640887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3559217 / 8000000) (-111225531 / 250000000) (Real.log (640887 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4669591 / 20000000) ≤ -Real.log (1000000 / 1262987) ∧
    -Real.log (1000000 / 1262987) ≤ (233479551 / 1000000000) := by
  have h := checkLog_sound (w := (262987 / 2262987)) (n := 12)
    (lo := (4669591 / 20000000)) (hi := (233479551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262987 / 1000000) = 1/(1000000 / 1262987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4669591 / 20000000) (233479551 / 1000000000) (Real.log (1262987 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1262987 / 1000000) = -Real.log (1000000 / 1262987) := by
    rw [show ((1262987 / 1000000) : ℝ) = ((1000000 / 1262987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (305149747 / 1000000000) ≤ -Real.log (737013 / 1000000) ∧
    -Real.log (737013 / 1000000) ≤ (76287437 / 250000000) := by
  have h := checkLog_sound (w := (262987 / 1737013)) (n := 12)
    (lo := (305149747 / 1000000000)) (hi := (76287437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737013) = 1/(737013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-76287437 / 250000000) (-305149747 / 1000000000) (Real.log (737013 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9349917 / 40000000) ≤ -Real.log (500000 / 631663) ∧
    -Real.log (500000 / 631663) ≤ (116873963 / 500000000) := by
  have h := checkLog_sound (w := (131663 / 1131663)) (n := 12)
    (lo := (9349917 / 40000000)) (hi := (116873963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631663 / 500000) = 1/(500000 / 631663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9349917 / 40000000) (116873963 / 500000000) (Real.log (631663 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (631663 / 500000) = -Real.log (500000 / 631663) := by
    rw [show ((631663 / 500000) : ℝ) = ((500000 / 631663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (152804909 / 500000000) ≤ -Real.log (368337 / 500000) ∧
    -Real.log (368337 / 500000) ≤ (305609819 / 1000000000) := by
  have h := checkLog_sound (w := (131663 / 868337)) (n := 12)
    (lo := (152804909 / 500000000)) (hi := (305609819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368337) = 1/(368337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-305609819 / 1000000000) (-152804909 / 500000000) (Real.log (368337 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (187686239 / 250000000) ≤ -Real.log (250000000000 / 529644419773) ∧
    -Real.log (250000000000 / 529644419773) ≤ (375372479 / 500000000) := by
  have h := checkLog_sound (w := (29644419773 / 1029644419773)) (n := 12)
    (lo := (3599861 / 62500000)) (hi := (57597777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529644419773 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529644419773 / 500000000000) = 1/(250000000000 / 529644419773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (187686239 / 250000000) (375372479 / 500000000) (Real.log (529644419773 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (529644419773 / 250000000000) = -Real.log (250000000000 / 529644419773) := by
    rw [show ((529644419773 / 250000000000) : ℝ) = ((250000000000 / 529644419773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150346881 / 200000000) ≤ -Real.log (125000000000 / 265084367447) ∧
    -Real.log (125000000000 / 265084367447) ≤ (751734407 / 1000000000) := by
  have h := checkLog_sound (w := (15084367447 / 515084367447)) (n := 12)
    (lo := (2343489 / 40000000)) (hi := (29293613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265084367447 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265084367447 / 250000000000) = 1/(125000000000 / 265084367447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150346881 / 200000000) (751734407 / 1000000000) (Real.log (265084367447 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (265084367447 / 125000000000) = -Real.log (125000000000 / 265084367447) := by
    rw [show ((265084367447 / 125000000000) : ℝ) = ((125000000000 / 265084367447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (269314649 / 500000000) ≤ -Real.log (500000000000 / 856828169923) ∧
    -Real.log (500000000000 / 856828169923) ≤ (538629299 / 1000000000) := by
  have h := checkLog_sound (w := (356828169923 / 1356828169923)) (n := 12)
    (lo := (269314649 / 500000000)) (hi := (538629299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856828169923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856828169923 / 500000000000) = 1/(500000000000 / 856828169923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (269314649 / 500000000) (538629299 / 1000000000) (Real.log (856828169923 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (856828169923 / 500000000000) = -Real.log (500000000000 / 856828169923) := by
    rw [show ((856828169923 / 500000000000) : ℝ) = ((500000000000 / 856828169923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (33709859 / 62500000) ≤ -Real.log (500000000000 / 857452550247) ∧
    -Real.log (500000000000 / 857452550247) ≤ (107871549 / 200000000) := by
  have h := checkLog_sound (w := (357452550247 / 1357452550247)) (n := 12)
    (lo := (33709859 / 62500000)) (hi := (107871549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857452550247 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857452550247 / 500000000000) = 1/(500000000000 / 857452550247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (33709859 / 62500000) (107871549 / 200000000) (Real.log (857452550247 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (857452550247 / 500000000000) = -Real.log (500000000000 / 857452550247) := by
    rw [show ((857452550247 / 500000000000) : ℝ) = ((500000000000 / 857452550247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0300
