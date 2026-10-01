import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0078
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

theorem reflection_log_1_neg : (17585083 / 50000000) ≤ -Real.log (2560 / 3639) ∧
    -Real.log (2560 / 3639) ≤ (351701661 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 6199)) (n := 12)
    (lo := (17585083 / 50000000)) (hi := (351701661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3639 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3639 / 2560) = 1/(2560 / 3639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (17585083 / 50000000) (351701661 / 1000000000) (Real.log (3639 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3639 / 2560) = -Real.log (2560 / 3639) := by
    rw [show ((3639 / 2560) : ℝ) = ((2560 / 3639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (547289723 / 1000000000) ≤ -Real.log (1481 / 2560) ∧
    -Real.log (1481 / 2560) ≤ (136822431 / 250000000) := by
  have h := checkLog_sound (w := (1079 / 4041)) (n := 12)
    (lo := (547289723 / 1000000000)) (hi := (136822431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1481) = 1/(1481 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-136822431 / 250000000) (-547289723 / 1000000000) (Real.log (1481 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (350876917 / 1000000000) ≤ -Real.log (640 / 909) ∧
    -Real.log (640 / 909) ≤ (175438459 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1549)) (n := 12)
    (lo := (350876917 / 1000000000)) (hi := (175438459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909 / 640) = 1/(640 / 909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (350876917 / 1000000000) (175438459 / 500000000) (Real.log (909 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (909 / 640) = -Real.log (640 / 909) := by
    rw [show ((909 / 640) : ℝ) = ((640 / 909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (545266113 / 1000000000) ≤ -Real.log (371 / 640) ∧
    -Real.log (371 / 640) ≤ (272633057 / 500000000) := by
  have h := checkLog_sound (w := (269 / 1011)) (n := 12)
    (lo := (545266113 / 1000000000)) (hi := (272633057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 371) = 1/(371 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-272633057 / 500000000) (-545266113 / 1000000000) (Real.log (371 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (305688861 / 500000000) ≤ -Real.log (1280 / 2359) ∧
    -Real.log (1280 / 2359) ≤ (611377723 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 3639)) (n := 12)
    (lo := (305688861 / 500000000)) (hi := (611377723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 1280) = 1/(1280 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (305688861 / 500000000) (611377723 / 1000000000) (Real.log (2359 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2359 / 1280) = -Real.log (1280 / 2359) := by
    rw [show ((2359 / 1280) : ℝ) = ((1280 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1851310447 / 1000000000) ≤ -Real.log (201 / 1280) ∧
    -Real.log (201 / 1280) ≤ (37026209 / 20000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 201) = 1/(201 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-37026209 / 20000000) (-1851310447 / 1000000000) (Real.log (201 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (610105187 / 1000000000) ≤ -Real.log (320 / 589) ∧
    -Real.log (320 / 589) ≤ (152526297 / 250000000) := by
  have h := checkLog_sound (w := (269 / 909)) (n := 12)
    (lo := (610105187 / 1000000000)) (hi := (152526297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 320) = 1/(320 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (610105187 / 1000000000) (152526297 / 250000000) (Real.log (589 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (589 / 320) = -Real.log (320 / 589) := by
    rw [show ((589 / 320) : ℝ) = ((320 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1836495361 / 1000000000) ≤ -Real.log (51 / 320) ∧
    -Real.log (51 / 320) ≤ (459123841 / 250000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 51) = 1/(51 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-459123841 / 250000000) (-1836495361 / 1000000000) (Real.log (51 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (241487999 / 500000000) ≤ -Real.log (1000000 / 1620891) ∧
    -Real.log (1000000 / 1620891) ≤ (482975999 / 1000000000) := by
  have h := checkLog_sound (w := (620891 / 2620891)) (n := 12)
    (lo := (241487999 / 500000000)) (hi := (482975999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1620891 / 1000000) = 1/(1000000 / 1620891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (241487999 / 500000000) (482975999 / 1000000000) (Real.log (1620891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1620891 / 1000000) = -Real.log (1000000 / 1620891) := by
    rw [show ((1620891 / 1000000) : ℝ) = ((1000000 / 1620891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193986303 / 200000000) ≤ -Real.log (379109 / 1000000) ∧
    -Real.log (379109 / 1000000) ≤ (969931517 / 1000000000) := by
  have h := checkLog_sound (w := (120891 / 879109)) (n := 12)
    (lo := (55356867 / 200000000)) (hi := (17299021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 379109) = 1/(379109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-969931517 / 1000000000) (-193986303 / 200000000) (Real.log (379109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (242097169 / 500000000) ≤ -Real.log (1000000 / 1622867) ∧
    -Real.log (1000000 / 1622867) ≤ (484194339 / 1000000000) := by
  have h := checkLog_sound (w := (622867 / 2622867)) (n := 12)
    (lo := (242097169 / 500000000)) (hi := (484194339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1622867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1622867 / 1000000) = 1/(1000000 / 1622867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (242097169 / 500000000) (484194339 / 1000000000) (Real.log (1622867 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1622867 / 1000000) = -Real.log (1000000 / 1622867) := by
    rw [show ((1622867 / 1000000) : ℝ) = ((1000000 / 1622867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (121894671 / 125000000) ≤ -Real.log (377133 / 1000000) ∧
    -Real.log (377133 / 1000000) ≤ (97515737 / 100000000) := by
  have h := checkLog_sound (w := (122867 / 877133)) (n := 12)
    (lo := (70502547 / 250000000)) (hi := (282010189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 377133) = 1/(377133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-97515737 / 100000000) (-121894671 / 125000000) (Real.log (377133 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (399440999 / 1000000000) ≤ -Real.log (1000000 / 1490991) ∧
    -Real.log (1000000 / 1490991) ≤ (399441 / 1000000) := by
  have h := checkLog_sound (w := (490991 / 2490991)) (n := 12)
    (lo := (399440999 / 1000000000)) (hi := (399441 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1490991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1490991 / 1000000) = 1/(1000000 / 1490991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (399440999 / 1000000000) (399441 / 1000000) (Real.log (1490991 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1490991 / 1000000) = -Real.log (1000000 / 1490991) := by
    rw [show ((1490991 / 1000000) : ℝ) = ((1000000 / 1490991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (33764479 / 50000000) ≤ -Real.log (509009 / 1000000) ∧
    -Real.log (509009 / 1000000) ≤ (675289581 / 1000000000) := by
  have h := checkLog_sound (w := (490991 / 1509009)) (n := 12)
    (lo := (33764479 / 50000000)) (hi := (675289581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 509009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 509009) = 1/(509009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-675289581 / 1000000000) (-33764479 / 50000000) (Real.log (509009 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (400733933 / 1000000000) ≤ -Real.log (25000 / 37323) ∧
    -Real.log (25000 / 37323) ≤ (200366967 / 500000000) := by
  have h := checkLog_sound (w := (12323 / 62323)) (n := 12)
    (lo := (400733933 / 1000000000)) (hi := (200366967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37323 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37323 / 25000) = 1/(25000 / 37323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (400733933 / 1000000000) (200366967 / 500000000) (Real.log (37323 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37323 / 25000) = -Real.log (25000 / 37323) := by
    rw [show ((37323 / 25000) : ℝ) = ((25000 / 37323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (21221453 / 31250000) ≤ -Real.log (12677 / 25000) ∧
    -Real.log (12677 / 25000) ≤ (679086497 / 1000000000) := by
  have h := checkLog_sound (w := (12323 / 37677)) (n := 12)
    (lo := (21221453 / 31250000)) (hi := (679086497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 12677) = 1/(12677 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-679086497 / 1000000000) (-21221453 / 31250000) (Real.log (12677 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1452907513 / 1000000000) ≤ -Real.log (62500000000 / 267220476169) ∧
    -Real.log (62500000000 / 267220476169) ≤ (363226879 / 250000000) := by
  have h := checkLog_sound (w := (17220476169 / 517220476169)) (n := 12)
    (lo := (66613153 / 1000000000)) (hi := (33306577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267220476169 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(267220476169 / 250000000000) = 1/(62500000000 / 267220476169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1452907513 / 1000000000) (363226879 / 250000000) (Real.log (267220476169 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267220476169 / 62500000000) = -Real.log (62500000000 / 267220476169) := by
    rw [show ((267220476169 / 62500000000) : ℝ) = ((62500000000 / 267220476169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (291870341 / 200000000) ≤ -Real.log (500000000000 / 2151584454291) ∧
    -Real.log (500000000000 / 2151584454291) ≤ (364837927 / 250000000) := by
  have h := checkLog_sound (w := (151584454291 / 4151584454291)) (n := 12)
    (lo := (14611469 / 200000000)) (hi := (36528673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2151584454291 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2151584454291 / 2000000000000) = 1/(500000000000 / 2151584454291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (291870341 / 200000000) (364837927 / 250000000) (Real.log (2151584454291 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2151584454291 / 500000000000) = -Real.log (500000000000 / 2151584454291) := by
    rw [show ((2151584454291 / 500000000000) : ℝ) = ((500000000000 / 2151584454291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1074730579 / 1000000000) ≤ -Real.log (500000000000 / 1464601804683) ∧
    -Real.log (500000000000 / 1464601804683) ≤ (1074730581 / 1000000000) := by
  have h := checkLog_sound (w := (464601804683 / 2464601804683)) (n := 12)
    (lo := (381583399 / 1000000000)) (hi := (1907917 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1464601804683 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1464601804683 / 1000000000000) = 1/(500000000000 / 1464601804683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1074730579 / 1000000000) (1074730581 / 1000000000) (Real.log (1464601804683 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1464601804683 / 500000000000) = -Real.log (500000000000 / 1464601804683) := by
    rw [show ((1464601804683 / 500000000000) : ℝ) = ((500000000000 / 1464601804683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (107982043 / 100000000) ≤ -Real.log (125000000000 / 368018853041) ∧
    -Real.log (125000000000 / 368018853041) ≤ (67488777 / 62500000) := by
  have h := checkLog_sound (w := (118018853041 / 618018853041)) (n := 12)
    (lo := (1546693 / 4000000)) (hi := (386673251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368018853041 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(368018853041 / 250000000000) = 1/(125000000000 / 368018853041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (107982043 / 100000000) (67488777 / 62500000) (Real.log (368018853041 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (368018853041 / 125000000000) = -Real.log (125000000000 / 368018853041) := by
    rw [show ((368018853041 / 125000000000) : ℝ) = ((125000000000 / 368018853041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0078
