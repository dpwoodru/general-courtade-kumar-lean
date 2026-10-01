import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0220
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

theorem reflection_log_1_neg : (25663877 / 100000000) ≤ -Real.log (2560 / 3309) ∧
    -Real.log (2560 / 3309) ≤ (256638771 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 5869)) (n := 12)
    (lo := (25663877 / 100000000)) (hi := (256638771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2560) = 1/(2560 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25663877 / 100000000) (256638771 / 1000000000) (Real.log (3309 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3309 / 2560) = -Real.log (2560 / 3309) := by
    rw [show ((3309 / 2560) : ℝ) = ((2560 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (346128079 / 1000000000) ≤ -Real.log (1811 / 2560) ∧
    -Real.log (1811 / 2560) ≤ (4326601 / 12500000) := by
  have h := checkLog_sound (w := (749 / 4371)) (n := 12)
    (lo := (346128079 / 1000000000)) (hi := (4326601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1811) = 1/(1811 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4326601 / 12500000) (-346128079 / 1000000000) (Real.log (1811 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128092679 / 500000000) ≤ -Real.log (1024 / 1323) ∧
    -Real.log (1024 / 1323) ≤ (256185359 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2347)) (n := 12)
    (lo := (128092679 / 500000000)) (hi := (256185359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1024) = 1/(1024 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128092679 / 500000000) (256185359 / 1000000000) (Real.log (1323 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1323 / 1024) = -Real.log (1024 / 1323) := by
    rw [show ((1323 / 1024) : ℝ) = ((1024 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6906003 / 20000000) ≤ -Real.log (725 / 1024) ∧
    -Real.log (725 / 1024) ≤ (345300151 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1749)) (n := 12)
    (lo := (6906003 / 20000000)) (hi := (345300151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 725) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 725) = 1/(725 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345300151 / 1000000000) (-6906003 / 20000000) (Real.log (725 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (230341491 / 500000000) ≤ -Real.log (1280 / 2029) ∧
    -Real.log (1280 / 2029) ≤ (460682983 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 3309)) (n := 12)
    (lo := (230341491 / 500000000)) (hi := (460682983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2029 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2029 / 1280) = 1/(1280 / 2029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (230341491 / 500000000) (460682983 / 1000000000) (Real.log (2029 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2029 / 1280) = -Real.log (1280 / 2029) := by
    rw [show ((2029 / 1280) : ℝ) = ((1280 / 2029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (175970667 / 200000000) ≤ -Real.log (531 / 1280) ∧
    -Real.log (531 / 1280) ≤ (879853337 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1171)) (n := 12)
    (lo := (37341231 / 200000000)) (hi := (46676539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 531) = 1/(531 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-879853337 / 1000000000) (-175970667 / 200000000) (Real.log (531 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (459943429 / 1000000000) ≤ -Real.log (512 / 811) ∧
    -Real.log (512 / 811) ≤ (45994343 / 100000000) := by
  have h := checkLog_sound (w := (299 / 1323)) (n := 12)
    (lo := (459943429 / 1000000000)) (hi := (45994343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811 / 512) = 1/(512 / 811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (459943429 / 1000000000) (45994343 / 100000000) (Real.log (811 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (811 / 512) = -Real.log (512 / 811) := by
    rw [show ((811 / 512) : ℝ) = ((512 / 811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (438516229 / 500000000) ≤ -Real.log (213 / 512) ∧
    -Real.log (213 / 512) ≤ (43851623 / 50000000) := by
  have h := checkLog_sound (w := (43 / 469)) (n := 12)
    (lo := (91942639 / 500000000)) (hi := (183885279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 213) = 1/(213 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43851623 / 50000000) (-438516229 / 500000000) (Real.log (213 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (350539259 / 1000000000) ≤ -Real.log (1000000 / 1419833) ∧
    -Real.log (1000000 / 1419833) ≤ (17526963 / 50000000) := by
  have h := checkLog_sound (w := (419833 / 2419833)) (n := 12)
    (lo := (350539259 / 1000000000)) (hi := (17526963 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419833 / 1000000) = 1/(1000000 / 1419833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (350539259 / 1000000000) (17526963 / 50000000) (Real.log (1419833 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1419833 / 1000000) = -Real.log (1000000 / 1419833) := by
    rw [show ((1419833 / 1000000) : ℝ) = ((1000000 / 1419833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (108887857 / 200000000) ≤ -Real.log (580167 / 1000000) ∧
    -Real.log (580167 / 1000000) ≤ (272219643 / 500000000) := by
  have h := checkLog_sound (w := (419833 / 1580167)) (n := 12)
    (lo := (108887857 / 200000000)) (hi := (272219643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 580167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 580167) = 1/(580167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-272219643 / 500000000) (-108887857 / 200000000) (Real.log (580167 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175578021 / 500000000) ≤ -Real.log (1000000 / 1420709) ∧
    -Real.log (1000000 / 1420709) ≤ (351156043 / 1000000000) := by
  have h := checkLog_sound (w := (420709 / 2420709)) (n := 12)
    (lo := (175578021 / 500000000)) (hi := (351156043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1420709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1420709 / 1000000) = 1/(1000000 / 1420709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175578021 / 500000000) (351156043 / 1000000000) (Real.log (1420709 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1420709 / 1000000) = -Real.log (1000000 / 1420709) := by
    rw [show ((1420709 / 1000000) : ℝ) = ((1000000 / 1420709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4265237 / 7812500) ≤ -Real.log (579291 / 1000000) ∧
    -Real.log (579291 / 1000000) ≤ (545950337 / 1000000000) := by
  have h := checkLog_sound (w := (420709 / 1579291)) (n := 12)
    (lo := (4265237 / 7812500)) (hi := (545950337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 579291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 579291) = 1/(579291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-545950337 / 1000000000) (-4265237 / 7812500) (Real.log (579291 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67900939 / 250000000) ≤ -Real.log (1000000 / 1312067) ∧
    -Real.log (1000000 / 1312067) ≤ (271603757 / 1000000000) := by
  have h := checkLog_sound (w := (312067 / 2312067)) (n := 12)
    (lo := (67900939 / 250000000)) (hi := (271603757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312067 / 1000000) = 1/(1000000 / 1312067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67900939 / 250000000) (271603757 / 1000000000) (Real.log (1312067 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1312067 / 1000000) = -Real.log (1000000 / 1312067) := by
    rw [show ((1312067 / 1000000) : ℝ) = ((1000000 / 1312067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (374063829 / 1000000000) ≤ -Real.log (687933 / 1000000) ∧
    -Real.log (687933 / 1000000) ≤ (37406383 / 100000000) := by
  have h := checkLog_sound (w := (312067 / 1687933)) (n := 12)
    (lo := (374063829 / 1000000000)) (hi := (37406383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687933) = 1/(687933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-37406383 / 100000000) (-374063829 / 1000000000) (Real.log (687933 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136075417 / 500000000) ≤ -Real.log (200000 / 262557) ∧
    -Real.log (200000 / 262557) ≤ (54430167 / 200000000) := by
  have h := checkLog_sound (w := (62557 / 462557)) (n := 12)
    (lo := (136075417 / 500000000)) (hi := (54430167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262557 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262557 / 200000) = 1/(200000 / 262557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136075417 / 500000000) (54430167 / 200000000) (Real.log (262557 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (262557 / 200000) = -Real.log (200000 / 262557) := by
    rw [show ((262557 / 200000) : ℝ) = ((200000 / 262557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4688851 / 12500000) ≤ -Real.log (137443 / 200000) ∧
    -Real.log (137443 / 200000) ≤ (375108081 / 1000000000) := by
  have h := checkLog_sound (w := (62557 / 337443)) (n := 12)
    (lo := (4688851 / 12500000)) (hi := (375108081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137443) = 1/(137443 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-375108081 / 1000000000) (-4688851 / 12500000) (Real.log (137443 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (55936159 / 62500000) ≤ -Real.log (500000000000 / 1223641641113) ∧
    -Real.log (500000000000 / 1223641641113) ≤ (447489273 / 500000000) := by
  have h := checkLog_sound (w := (223641641113 / 2223641641113)) (n := 12)
    (lo := (50457841 / 250000000)) (hi := (40366273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223641641113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1223641641113 / 1000000000000) = 1/(500000000000 / 1223641641113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (55936159 / 62500000) (447489273 / 500000000) (Real.log (1223641641113 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1223641641113 / 500000000000) = -Real.log (500000000000 / 1223641641113) := by
    rw [show ((1223641641113 / 500000000000) : ℝ) = ((500000000000 / 1223641641113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (897106379 / 1000000000) ≤ -Real.log (125000000000 / 306562030137) ∧
    -Real.log (125000000000 / 306562030137) ≤ (897106381 / 1000000000) := by
  have h := checkLog_sound (w := (56562030137 / 556562030137)) (n := 12)
    (lo := (203959199 / 1000000000)) (hi := (254949 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306562030137 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(306562030137 / 250000000000) = 1/(125000000000 / 306562030137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (897106379 / 1000000000) (897106381 / 1000000000) (Real.log (306562030137 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (306562030137 / 125000000000) = -Real.log (125000000000 / 306562030137) := by
    rw [show ((306562030137 / 125000000000) : ℝ) = ((125000000000 / 306562030137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (129133517 / 200000000) ≤ -Real.log (31250000000 / 59601870749) ∧
    -Real.log (31250000000 / 59601870749) ≤ (322833793 / 500000000) := by
  have h := checkLog_sound (w := (28351870749 / 90851870749)) (n := 12)
    (lo := (129133517 / 200000000)) (hi := (322833793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59601870749 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59601870749 / 31250000000) = 1/(31250000000 / 59601870749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (129133517 / 200000000) (322833793 / 500000000) (Real.log (59601870749 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (59601870749 / 31250000000) = -Real.log (31250000000 / 59601870749) := by
    rw [show ((59601870749 / 31250000000) : ℝ) = ((31250000000 / 59601870749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (129451783 / 200000000) ≤ -Real.log (500000000000 / 955148679817) ∧
    -Real.log (500000000000 / 955148679817) ≤ (161814729 / 250000000) := by
  have h := checkLog_sound (w := (455148679817 / 1455148679817)) (n := 12)
    (lo := (129451783 / 200000000)) (hi := (161814729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955148679817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955148679817 / 500000000000) = 1/(500000000000 / 955148679817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (129451783 / 200000000) (161814729 / 250000000) (Real.log (955148679817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (955148679817 / 500000000000) = -Real.log (500000000000 / 955148679817) := by
    rw [show ((955148679817 / 500000000000) : ℝ) = ((500000000000 / 955148679817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0220
