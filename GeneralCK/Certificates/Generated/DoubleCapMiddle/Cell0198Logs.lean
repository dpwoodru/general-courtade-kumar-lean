import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0198
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

theorem reflection_log_1_neg : (266562171 / 1000000000) ≤ -Real.log (1280 / 1671) ∧
    -Real.log (1280 / 1671) ≤ (66640543 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2951)) (n := 12)
    (lo := (266562171 / 1000000000)) (hi := (66640543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1280) = 1/(1280 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266562171 / 1000000000) (66640543 / 250000000) (Real.log (1671 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1671 / 1280) = -Real.log (1280 / 1671) := by
    rw [show ((1671 / 1280) : ℝ) = ((1280 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (364518121 / 1000000000) ≤ -Real.log (889 / 1280) ∧
    -Real.log (889 / 1280) ≤ (182259061 / 500000000) := by
  have h := checkLog_sound (w := (391 / 2169)) (n := 12)
    (lo := (364518121 / 1000000000)) (hi := (182259061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 889) = 1/(889 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-182259061 / 500000000) (-364518121 / 1000000000) (Real.log (889 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266113237 / 1000000000) ≤ -Real.log (5120 / 6681) ∧
    -Real.log (5120 / 6681) ≤ (133056619 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 11801)) (n := 12)
    (lo := (266113237 / 1000000000)) (hi := (133056619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6681 / 5120) = 1/(5120 / 6681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266113237 / 1000000000) (133056619 / 500000000) (Real.log (6681 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6681 / 5120) = -Real.log (5120 / 6681) := by
    rw [show ((6681 / 5120) : ℝ) = ((5120 / 6681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22729677 / 62500000) ≤ -Real.log (3559 / 5120) ∧
    -Real.log (3559 / 5120) ≤ (363674833 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 8679)) (n := 12)
    (lo := (22729677 / 62500000)) (hi := (363674833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3559) = 1/(3559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-363674833 / 1000000000) (-22729677 / 62500000) (Real.log (3559 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (476816307 / 1000000000) ≤ -Real.log (640 / 1031) ∧
    -Real.log (640 / 1031) ≤ (119204077 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1671)) (n := 12)
    (lo := (476816307 / 1000000000)) (hi := (119204077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1031 / 640) = 1/(640 / 1031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (476816307 / 1000000000) (119204077 / 250000000) (Real.log (1031 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1031 / 640) = -Real.log (640 / 1031) := by
    rw [show ((1031 / 640) : ℝ) = ((640 / 1031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (944015279 / 1000000000) ≤ -Real.log (249 / 640) ∧
    -Real.log (249 / 640) ≤ (944015281 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 249) = 1/(249 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-944015281 / 1000000000) (-944015279 / 1000000000) (Real.log (249 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (476088593 / 1000000000) ≤ -Real.log (2560 / 4121) ∧
    -Real.log (2560 / 4121) ≤ (238044297 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 6681)) (n := 12)
    (lo := (476088593 / 1000000000)) (hi := (238044297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4121 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4121 / 2560) = 1/(2560 / 4121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (476088593 / 1000000000) (238044297 / 500000000) (Real.log (4121 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4121 / 2560) = -Real.log (2560 / 4121) := by
    rw [show ((4121 / 2560) : ℝ) = ((2560 / 4121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (470503879 / 500000000) ≤ -Real.log (999 / 2560) ∧
    -Real.log (999 / 2560) ≤ (11762597 / 12500000) := by
  have h := checkLog_sound (w := (281 / 2279)) (n := 12)
    (lo := (123930289 / 500000000)) (hi := (247860579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 999) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 999) = 1/(999 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-11762597 / 12500000) (-470503879 / 500000000) (Real.log (999 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182027373 / 500000000) ≤ -Real.log (1000000 / 1439153) ∧
    -Real.log (1000000 / 1439153) ≤ (364054747 / 1000000000) := by
  have h := checkLog_sound (w := (439153 / 2439153)) (n := 12)
    (lo := (182027373 / 500000000)) (hi := (364054747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439153 / 1000000) = 1/(1000000 / 1439153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182027373 / 500000000) (364054747 / 1000000000) (Real.log (1439153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1439153 / 1000000) = -Real.log (1000000 / 1439153) := by
    rw [show ((1439153 / 1000000) : ℝ) = ((1000000 / 1439153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (578307137 / 1000000000) ≤ -Real.log (560847 / 1000000) ∧
    -Real.log (560847 / 1000000) ≤ (289153569 / 500000000) := by
  have h := checkLog_sound (w := (439153 / 1560847)) (n := 12)
    (lo := (578307137 / 1000000000)) (hi := (289153569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 560847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 560847) = 1/(560847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-289153569 / 500000000) (-578307137 / 1000000000) (Real.log (560847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182333709 / 500000000) ≤ -Real.log (200000 / 288007) ∧
    -Real.log (200000 / 288007) ≤ (364667419 / 1000000000) := by
  have h := checkLog_sound (w := (88007 / 488007)) (n := 12)
    (lo := (182333709 / 500000000)) (hi := (364667419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288007 / 200000) = 1/(200000 / 288007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182333709 / 500000000) (364667419 / 1000000000) (Real.log (288007 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288007 / 200000) = -Real.log (200000 / 288007) := by
    rw [show ((288007 / 200000) : ℝ) = ((200000 / 288007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (579880997 / 1000000000) ≤ -Real.log (111993 / 200000) ∧
    -Real.log (111993 / 200000) ≤ (289940499 / 500000000) := by
  have h := checkLog_sound (w := (88007 / 311993)) (n := 12)
    (lo := (579880997 / 1000000000)) (hi := (289940499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111993) = 1/(111993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-289940499 / 500000000) (-579880997 / 1000000000) (Real.log (111993 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (70918701 / 250000000) ≤ -Real.log (1000000 / 1328001) ∧
    -Real.log (1000000 / 1328001) ≤ (56734961 / 200000000) := by
  have h := checkLog_sound (w := (328001 / 2328001)) (n := 12)
    (lo := (70918701 / 250000000)) (hi := (56734961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328001 / 1000000) = 1/(1000000 / 1328001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (70918701 / 250000000) (56734961 / 200000000) (Real.log (1328001 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1328001 / 1000000) = -Real.log (1000000 / 1328001) := by
    rw [show ((1328001 / 1000000) : ℝ) = ((1000000 / 1328001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (198749213 / 500000000) ≤ -Real.log (671999 / 1000000) ∧
    -Real.log (671999 / 1000000) ≤ (397498427 / 1000000000) := by
  have h := checkLog_sound (w := (328001 / 1671999)) (n := 12)
    (lo := (198749213 / 500000000)) (hi := (397498427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671999) = 1/(671999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-397498427 / 1000000000) (-198749213 / 500000000) (Real.log (671999 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (284226609 / 1000000000) ≤ -Real.log (500000 / 664367) ∧
    -Real.log (500000 / 664367) ≤ (28422661 / 100000000) := by
  have h := checkLog_sound (w := (164367 / 1164367)) (n := 12)
    (lo := (284226609 / 1000000000)) (hi := (28422661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664367 / 500000) = 1/(500000 / 664367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (284226609 / 1000000000) (28422661 / 100000000) (Real.log (664367 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (664367 / 500000) = -Real.log (500000 / 664367) := by
    rw [show ((664367 / 500000) : ℝ) = ((500000 / 664367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (398589797 / 1000000000) ≤ -Real.log (335633 / 500000) ∧
    -Real.log (335633 / 500000) ≤ (199294899 / 500000000) := by
  have h := checkLog_sound (w := (164367 / 835633)) (n := 12)
    (lo := (398589797 / 1000000000)) (hi := (199294899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335633) = 1/(335633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-199294899 / 500000000) (-398589797 / 1000000000) (Real.log (335633 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (942361883 / 1000000000) ≤ -Real.log (125000000000 / 320754367947) ∧
    -Real.log (125000000000 / 320754367947) ≤ (188472377 / 200000000) := by
  have h := checkLog_sound (w := (70754367947 / 570754367947)) (n := 12)
    (lo := (249214703 / 1000000000)) (hi := (15575919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320754367947 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320754367947 / 250000000000) = 1/(125000000000 / 320754367947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (942361883 / 1000000000) (188472377 / 200000000) (Real.log (320754367947 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (320754367947 / 125000000000) = -Real.log (125000000000 / 320754367947) := by
    rw [show ((320754367947 / 125000000000) : ℝ) = ((125000000000 / 320754367947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188909683 / 200000000) ≤ -Real.log (250000000000 / 642912949917) ∧
    -Real.log (250000000000 / 642912949917) ≤ (944548417 / 1000000000) := by
  have h := checkLog_sound (w := (142912949917 / 1142912949917)) (n := 12)
    (lo := (50280247 / 200000000)) (hi := (62850309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642912949917 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642912949917 / 500000000000) = 1/(250000000000 / 642912949917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188909683 / 200000000) (944548417 / 1000000000) (Real.log (642912949917 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (642912949917 / 250000000000) = -Real.log (250000000000 / 642912949917) := by
    rw [show ((642912949917 / 250000000000) : ℝ) = ((250000000000 / 642912949917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (68117323 / 100000000) ≤ -Real.log (20000000000 / 39523898101) ∧
    -Real.log (20000000000 / 39523898101) ≤ (681173231 / 1000000000) := by
  have h := checkLog_sound (w := (19523898101 / 59523898101)) (n := 12)
    (lo := (68117323 / 100000000)) (hi := (681173231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39523898101 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39523898101 / 20000000000) = 1/(20000000000 / 39523898101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (68117323 / 100000000) (681173231 / 1000000000) (Real.log (39523898101 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (39523898101 / 20000000000) = -Real.log (20000000000 / 39523898101) := by
    rw [show ((39523898101 / 20000000000) : ℝ) = ((20000000000 / 39523898101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (341408203 / 500000000) ≤ -Real.log (62500000000 / 123715300641) ∧
    -Real.log (62500000000 / 123715300641) ≤ (682816407 / 1000000000) := by
  have h := checkLog_sound (w := (61215300641 / 186215300641)) (n := 12)
    (lo := (341408203 / 500000000)) (hi := (682816407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123715300641 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123715300641 / 62500000000) = 1/(62500000000 / 123715300641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (341408203 / 500000000) (682816407 / 1000000000) (Real.log (123715300641 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (123715300641 / 62500000000) = -Real.log (62500000000 / 123715300641) := by
    rw [show ((123715300641 / 62500000000) : ℝ) = ((62500000000 / 123715300641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0198
