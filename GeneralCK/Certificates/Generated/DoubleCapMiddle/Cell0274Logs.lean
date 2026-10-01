import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0274
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

theorem reflection_log_1_neg : (231855491 / 1000000000) ≤ -Real.log (640 / 807) ∧
    -Real.log (640 / 807) ≤ (57963873 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1447)) (n := 12)
    (lo := (231855491 / 1000000000)) (hi := (57963873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 640) = 1/(640 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (231855491 / 1000000000) (57963873 / 250000000) (Real.log (807 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (807 / 640) = -Real.log (640 / 807) := by
    rw [show ((807 / 640) : ℝ) = ((640 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302372787 / 1000000000) ≤ -Real.log (473 / 640) ∧
    -Real.log (473 / 640) ≤ (75593197 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1113)) (n := 12)
    (lo := (302372787 / 1000000000)) (hi := (75593197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 473) = 1/(473 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75593197 / 250000000) (-302372787 / 1000000000) (Real.log (473 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (231390699 / 1000000000) ≤ -Real.log (5120 / 6453) ∧
    -Real.log (5120 / 6453) ≤ (2313907 / 10000000) := by
  have h := checkLog_sound (w := (1333 / 11573)) (n := 12)
    (lo := (231390699 / 1000000000)) (hi := (2313907 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6453 / 5120) = 1/(5120 / 6453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (231390699 / 1000000000) (2313907 / 10000000) (Real.log (6453 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6453 / 5120) = -Real.log (5120 / 6453) := by
    rw [show ((6453 / 5120) : ℝ) = ((5120 / 6453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30158029 / 100000000) ≤ -Real.log (3787 / 5120) ∧
    -Real.log (3787 / 5120) ≤ (301580291 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 8907)) (n := 12)
    (lo := (30158029 / 100000000)) (hi := (301580291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3787) = 1/(3787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301580291 / 1000000000) (-30158029 / 100000000) (Real.log (3787 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (419943127 / 1000000000) ≤ -Real.log (320 / 487) ∧
    -Real.log (320 / 487) ≤ (52492891 / 125000000) := by
  have h := checkLog_sound (w := (167 / 807)) (n := 12)
    (lo := (419943127 / 1000000000)) (hi := (52492891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487 / 320) = 1/(320 / 487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (419943127 / 1000000000) (52492891 / 125000000) (Real.log (487 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (487 / 320) = -Real.log (320 / 487) := by
    rw [show ((487 / 320) : ℝ) = ((320 / 487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (737883073 / 1000000000) ≤ -Real.log (153 / 320) ∧
    -Real.log (153 / 320) ≤ (29515323 / 40000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 153) = 1/(153 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-29515323 / 40000000) (-737883073 / 1000000000) (Real.log (153 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41917281 / 100000000) ≤ -Real.log (2560 / 3893) ∧
    -Real.log (2560 / 3893) ≤ (419172811 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6453)) (n := 12)
    (lo := (41917281 / 100000000)) (hi := (419172811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3893 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3893 / 2560) = 1/(2560 / 3893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41917281 / 100000000) (419172811 / 1000000000) (Real.log (3893 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3893 / 2560) = -Real.log (2560 / 3893) := by
    rw [show ((3893 / 2560) : ℝ) = ((2560 / 3893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (183858773 / 250000000) ≤ -Real.log (1227 / 2560) ∧
    -Real.log (1227 / 2560) ≤ (367717547 / 500000000) := by
  have h := checkLog_sound (w := (53 / 2507)) (n := 12)
    (lo := (5285989 / 125000000)) (hi := (42287913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1227) = 1/(1227 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-367717547 / 500000000) (-183858773 / 250000000) (Real.log (1227 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (316926747 / 1000000000) ≤ -Real.log (500000 / 686451) ∧
    -Real.log (500000 / 686451) ≤ (79231687 / 250000000) := by
  have h := checkLog_sound (w := (186451 / 1186451)) (n := 12)
    (lo := (316926747 / 1000000000)) (hi := (79231687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686451 / 500000) = 1/(500000 / 686451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (316926747 / 1000000000) (79231687 / 250000000) (Real.log (686451 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (686451 / 500000) = -Real.log (500000 / 686451) := by
    rw [show ((686451 / 500000) : ℝ) = ((500000 / 686451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9333049 / 20000000) ≤ -Real.log (313549 / 500000) ∧
    -Real.log (313549 / 500000) ≤ (466652451 / 1000000000) := by
  have h := checkLog_sound (w := (186451 / 813549)) (n := 12)
    (lo := (9333049 / 20000000)) (hi := (466652451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 313549) = 1/(313549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-466652451 / 1000000000) (-9333049 / 20000000) (Real.log (313549 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (317555873 / 1000000000) ≤ -Real.log (500000 / 686883) ∧
    -Real.log (500000 / 686883) ≤ (158777937 / 500000000) := by
  have h := checkLog_sound (w := (186883 / 1186883)) (n := 12)
    (lo := (317555873 / 1000000000)) (hi := (158777937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686883 / 500000) = 1/(500000 / 686883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (317555873 / 1000000000) (158777937 / 500000000) (Real.log (686883 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (686883 / 500000) = -Real.log (500000 / 686883) := by
    rw [show ((686883 / 500000) : ℝ) = ((500000 / 686883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18721247 / 40000000) ≤ -Real.log (313117 / 500000) ∧
    -Real.log (313117 / 500000) ≤ (58503897 / 125000000) := by
  have h := checkLog_sound (w := (186883 / 813117)) (n := 12)
    (lo := (18721247 / 40000000)) (hi := (58503897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 313117) = 1/(313117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-58503897 / 125000000) (-18721247 / 40000000) (Real.log (313117 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (242341289 / 1000000000) ≤ -Real.log (1000000 / 1274229) ∧
    -Real.log (1000000 / 1274229) ≤ (24234129 / 100000000) := by
  have h := checkLog_sound (w := (274229 / 2274229)) (n := 12)
    (lo := (242341289 / 1000000000)) (hi := (24234129 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274229 / 1000000) = 1/(1000000 / 1274229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (242341289 / 1000000000) (24234129 / 100000000) (Real.log (1274229 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1274229 / 1000000) = -Real.log (1000000 / 1274229) := by
    rw [show ((1274229 / 1000000) : ℝ) = ((1000000 / 1274229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16026037 / 50000000) ≤ -Real.log (725771 / 1000000) ∧
    -Real.log (725771 / 1000000) ≤ (320520741 / 1000000000) := by
  have h := checkLog_sound (w := (274229 / 1725771)) (n := 12)
    (lo := (16026037 / 50000000)) (hi := (320520741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725771) = 1/(725771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-320520741 / 1000000000) (-16026037 / 50000000) (Real.log (725771 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (242879509 / 1000000000) ≤ -Real.log (200000 / 254983) ∧
    -Real.log (200000 / 254983) ≤ (24287951 / 100000000) := by
  have h := checkLog_sound (w := (54983 / 454983)) (n := 12)
    (lo := (242879509 / 1000000000)) (hi := (24287951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254983 / 200000) = 1/(200000 / 254983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (242879509 / 1000000000) (24287951 / 100000000) (Real.log (254983 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (254983 / 200000) = -Real.log (200000 / 254983) := by
    rw [show ((254983 / 200000) : ℝ) = ((200000 / 254983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (321466389 / 1000000000) ≤ -Real.log (145017 / 200000) ∧
    -Real.log (145017 / 200000) ≤ (32146639 / 100000000) := by
  have h := checkLog_sound (w := (54983 / 345017)) (n := 12)
    (lo := (321466389 / 1000000000)) (hi := (32146639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145017) = 1/(145017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-32146639 / 100000000) (-321466389 / 1000000000) (Real.log (145017 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (783579197 / 1000000000) ≤ -Real.log (125000000000 / 273661772163) ∧
    -Real.log (125000000000 / 273661772163) ≤ (783579199 / 1000000000) := by
  have h := checkLog_sound (w := (23661772163 / 523661772163)) (n := 12)
    (lo := (90432017 / 1000000000)) (hi := (45216009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273661772163 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273661772163 / 250000000000) = 1/(125000000000 / 273661772163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (783579197 / 1000000000) (783579199 / 1000000000) (Real.log (273661772163 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (273661772163 / 125000000000) = -Real.log (125000000000 / 273661772163) := by
    rw [show ((273661772163 / 125000000000) : ℝ) = ((125000000000 / 273661772163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (98198381 / 125000000) ≤ -Real.log (500000000000 / 1096847184919) ∧
    -Real.log (500000000000 / 1096847184919) ≤ (15711741 / 20000000) := by
  have h := checkLog_sound (w := (96847184919 / 2096847184919)) (n := 12)
    (lo := (23109967 / 250000000)) (hi := (92439869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096847184919 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096847184919 / 1000000000000) = 1/(500000000000 / 1096847184919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (98198381 / 125000000) (15711741 / 20000000) (Real.log (1096847184919 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1096847184919 / 500000000000) = -Real.log (500000000000 / 1096847184919) := by
    rw [show ((1096847184919 / 500000000000) : ℝ) = ((500000000000 / 1096847184919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56286203 / 100000000) ≤ -Real.log (100000000000 / 175569015571) ∧
    -Real.log (100000000000 / 175569015571) ≤ (562862031 / 1000000000) := by
  have h := checkLog_sound (w := (75569015571 / 275569015571)) (n := 12)
    (lo := (56286203 / 100000000)) (hi := (562862031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175569015571 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175569015571 / 100000000000) = 1/(100000000000 / 175569015571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (56286203 / 100000000) (562862031 / 1000000000) (Real.log (175569015571 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (175569015571 / 100000000000) = -Real.log (100000000000 / 175569015571) := by
    rw [show ((175569015571 / 100000000000) : ℝ) = ((100000000000 / 175569015571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (564345899 / 1000000000) ≤ -Real.log (250000000000 / 439574325769) ∧
    -Real.log (250000000000 / 439574325769) ≤ (5643459 / 10000000) := by
  have h := checkLog_sound (w := (189574325769 / 689574325769)) (n := 12)
    (lo := (564345899 / 1000000000)) (hi := (5643459 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439574325769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439574325769 / 250000000000) = 1/(250000000000 / 439574325769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (564345899 / 1000000000) (5643459 / 10000000) (Real.log (439574325769 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (439574325769 / 250000000000) = -Real.log (250000000000 / 439574325769) := by
    rw [show ((439574325769 / 250000000000) : ℝ) = ((250000000000 / 439574325769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0274
