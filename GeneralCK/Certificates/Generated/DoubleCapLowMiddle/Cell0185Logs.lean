import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0185
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

theorem reflection_log_1_neg : (123610629 / 200000000) ≤ -Real.log (3200 / 5937) ∧
    -Real.log (3200 / 5937) ≤ (309026573 / 500000000) := by
  have h := checkLog_sound (w := (2737 / 9137)) (n := 12)
    (lo := (123610629 / 200000000)) (hi := (309026573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 3200) = 1/(3200 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (123610629 / 200000000) (309026573 / 500000000) (Real.log (5937 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5937 / 3200) = -Real.log (3200 / 5937) := by
    rw [show ((5937 / 3200) : ℝ) = ((3200 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1933179033 / 1000000000) ≤ -Real.log (463 / 3200) ∧
    -Real.log (463 / 3200) ≤ (483294759 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 463) = 1/(463 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-483294759 / 250000000) (-1933179033 / 1000000000) (Real.log (463 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1342147 / 2500000) ≤ -Real.log (1600 / 2737) ∧
    -Real.log (1600 / 2737) ≤ (536858801 / 1000000000) := by
  have h := checkLog_sound (w := (1137 / 4337)) (n := 12)
    (lo := (1342147 / 2500000)) (hi := (536858801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2737 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2737 / 1600) = 1/(1600 / 2737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1342147 / 2500000) (536858801 / 1000000000) (Real.log (2737 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2737 / 1600) = -Real.log (1600 / 2737) := by
    rw [show ((2737 / 1600) : ℝ) = ((1600 / 2737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1240031853 / 1000000000) ≤ -Real.log (463 / 1600) ∧
    -Real.log (463 / 1600) ≤ (248006371 / 200000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 463) = 1/(463 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248006371 / 200000000) (-1240031853 / 1000000000) (Real.log (463 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (637935693 / 1000000000) ≤ -Real.log (100000 / 189257) ∧
    -Real.log (100000 / 189257) ≤ (318967847 / 500000000) := by
  have h := checkLog_sound (w := (89257 / 289257)) (n := 12)
    (lo := (637935693 / 1000000000)) (hi := (318967847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189257 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189257 / 100000) = 1/(100000 / 189257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (637935693 / 1000000000) (318967847 / 500000000) (Real.log (189257 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (189257 / 100000) = -Real.log (100000 / 189257) := by
    rw [show ((189257 / 100000) : ℝ) = ((100000 / 189257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (557728951 / 250000000) ≤ -Real.log (10743 / 100000) ∧
    -Real.log (10743 / 100000) ≤ (69716119 / 31250000) := by
  have h := checkLog_sound (w := (1757 / 23243)) (n := 12)
    (lo := (18934283 / 125000000)) (hi := (30294853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10743) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 10743) = 1/(10743 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69716119 / 31250000) (-557728951 / 250000000) (Real.log (10743 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (319448971 / 500000000) ≤ -Real.log (125000 / 236799) ∧
    -Real.log (125000 / 236799) ≤ (638897943 / 1000000000) := by
  have h := checkLog_sound (w := (111799 / 361799)) (n := 12)
    (lo := (319448971 / 500000000)) (hi := (638897943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236799 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236799 / 125000) = 1/(125000 / 236799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (319448971 / 500000000) (638897943 / 1000000000) (Real.log (236799 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (236799 / 125000) = -Real.log (125000 / 236799) := by
    rw [show ((236799 / 125000) : ℝ) = ((125000 / 236799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2248021151 / 1000000000) ≤ -Real.log (13201 / 125000) ∧
    -Real.log (13201 / 125000) ≤ (449604231 / 200000000) := by
  have h := checkLog_sound (w := (1212 / 14413)) (n := 12)
    (lo := (168579611 / 1000000000)) (hi := (42144903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13201) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13201) = 1/(13201 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-449604231 / 200000000) (-2248021151 / 1000000000) (Real.log (13201 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (634796939 / 1000000000) ≤ -Real.log (1000000 / 1886639) ∧
    -Real.log (1000000 / 1886639) ≤ (31739847 / 50000000) := by
  have h := checkLog_sound (w := (886639 / 2886639)) (n := 12)
    (lo := (634796939 / 1000000000)) (hi := (31739847 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1886639 / 1000000) = 1/(1000000 / 1886639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (634796939 / 1000000000) (31739847 / 50000000) (Real.log (1886639 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1886639 / 1000000) = -Real.log (1000000 / 1886639) := by
    rw [show ((1886639 / 1000000) : ℝ) = ((1000000 / 1886639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (108858893 / 50000000) ≤ -Real.log (113361 / 1000000) ∧
    -Real.log (113361 / 1000000) ≤ (272147233 / 125000000) := by
  have h := checkLog_sound (w := (11639 / 238361)) (n := 12)
    (lo := (152713 / 1562500)) (hi := (97736321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113361) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 113361) = 1/(113361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-272147233 / 125000000) (-108858893 / 50000000) (Real.log (113361 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (635910469 / 1000000000) ≤ -Real.log (1000000 / 1888741) ∧
    -Real.log (1000000 / 1888741) ≤ (63591047 / 100000000) := by
  have h := checkLog_sound (w := (888741 / 2888741)) (n := 12)
    (lo := (635910469 / 1000000000)) (hi := (63591047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1888741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1888741 / 1000000) = 1/(1000000 / 1888741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (635910469 / 1000000000) (63591047 / 100000000) (Real.log (1888741 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1888741 / 1000000) = -Real.log (1000000 / 1888741) := by
    rw [show ((1888741 / 1000000) : ℝ) = ((1000000 / 1888741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (109794723 / 50000000) ≤ -Real.log (111259 / 1000000) ∧
    -Real.log (111259 / 1000000) ≤ (34310851 / 15625000) := by
  have h := checkLog_sound (w := (13741 / 236259)) (n := 12)
    (lo := (2911323 / 25000000)) (hi := (116452921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 111259) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 111259) = 1/(111259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-34310851 / 15625000) (-109794723 / 50000000) (Real.log (111259 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2868851497 / 1000000000) ≤ -Real.log (500000000000 / 8808386856557) ∧
    -Real.log (500000000000 / 8808386856557) ≤ (1434425751 / 500000000) := by
  have h := checkLog_sound (w := (808386856557 / 16808386856557)) (n := 12)
    (lo := (96262777 / 1000000000)) (hi := (48131389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8808386856557 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8808386856557 / 8000000000000) = 1/(500000000000 / 8808386856557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2868851497 / 1000000000) (1434425751 / 500000000) (Real.log (8808386856557 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8808386856557 / 500000000000) = -Real.log (500000000000 / 8808386856557) := by
    rw [show ((8808386856557 / 500000000000) : ℝ) = ((500000000000 / 8808386856557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2886919093 / 1000000000) ≤ -Real.log (125000000000 / 2242244905689) ∧
    -Real.log (125000000000 / 2242244905689) ≤ (1443459549 / 500000000) := by
  have h := checkLog_sound (w := (242244905689 / 4242244905689)) (n := 12)
    (lo := (114330373 / 1000000000)) (hi := (57165187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2242244905689 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2242244905689 / 2000000000000) = 1/(125000000000 / 2242244905689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2886919093 / 1000000000) (1443459549 / 500000000) (Real.log (2242244905689 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2242244905689 / 125000000000) = -Real.log (125000000000 / 2242244905689) := by
    rw [show ((2242244905689 / 125000000000) : ℝ) = ((125000000000 / 2242244905689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2811974799 / 1000000000) ≤ -Real.log (500000000000 / 8321375958221) ∧
    -Real.log (500000000000 / 8321375958221) ≤ (702993701 / 250000000) := by
  have h := checkLog_sound (w := (321375958221 / 16321375958221)) (n := 12)
    (lo := (39386079 / 1000000000)) (hi := (246163 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8321375958221 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8321375958221 / 8000000000000) = 1/(500000000000 / 8321375958221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2811974799 / 1000000000) (702993701 / 250000000) (Real.log (8321375958221 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8321375958221 / 500000000000) = -Real.log (500000000000 / 8321375958221) := by
    rw [show ((8321375958221 / 500000000000) : ℝ) = ((500000000000 / 8321375958221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2831804929 / 1000000000) ≤ -Real.log (62500000000 / 1061004615357) ∧
    -Real.log (62500000000 / 1061004615357) ≤ (1415902467 / 500000000) := by
  have h := checkLog_sound (w := (61004615357 / 2061004615357)) (n := 12)
    (lo := (59216209 / 1000000000)) (hi := (5921621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061004615357 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1061004615357 / 1000000000000) = 1/(62500000000 / 1061004615357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2831804929 / 1000000000) (1415902467 / 500000000) (Real.log (1061004615357 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1061004615357 / 62500000000) = -Real.log (62500000000 / 1061004615357) := by
    rw [show ((1061004615357 / 62500000000) : ℝ) = ((62500000000 / 1061004615357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0185
