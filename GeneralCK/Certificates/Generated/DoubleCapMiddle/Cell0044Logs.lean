import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0044
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

theorem reflection_log_1_neg : (11854553 / 31250000) ≤ -Real.log (2560 / 3741) ∧
    -Real.log (2560 / 3741) ≤ (379345697 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 6301)) (n := 12)
    (lo := (11854553 / 31250000)) (hi := (379345697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 2560) = 1/(2560 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11854553 / 31250000) (379345697 / 1000000000) (Real.log (3741 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3741 / 2560) = -Real.log (2560 / 3741) := by
    rw [show ((3741 / 2560) : ℝ) = ((2560 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (618648659 / 1000000000) ≤ -Real.log (1379 / 2560) ∧
    -Real.log (1379 / 2560) ≤ (30932433 / 50000000) := by
  have h := checkLog_sound (w := (1181 / 3939)) (n := 12)
    (lo := (618648659 / 1000000000)) (hi := (30932433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1379) = 1/(1379 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30932433 / 50000000) (-618648659 / 1000000000) (Real.log (1379 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7570869 / 20000000) ≤ -Real.log (1280 / 1869) ∧
    -Real.log (1280 / 1869) ≤ (378543451 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 3149)) (n := 12)
    (lo := (7570869 / 20000000)) (hi := (378543451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1280) = 1/(1280 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7570869 / 20000000) (378543451 / 1000000000) (Real.log (1869 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1869 / 1280) = -Real.log (1280 / 1869) := by
    rw [show ((1869 / 1280) : ℝ) = ((1280 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (616475533 / 1000000000) ≤ -Real.log (691 / 1280) ∧
    -Real.log (691 / 1280) ≤ (308237767 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1971)) (n := 12)
    (lo := (616475533 / 1000000000)) (hi := (308237767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 691) = 1/(691 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-308237767 / 500000000) (-616475533 / 1000000000) (Real.log (691 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653707693 / 1000000000) ≤ -Real.log (1280 / 2461) ∧
    -Real.log (1280 / 2461) ≤ (326853847 / 500000000) := by
  have h := checkLog_sound (w := (1181 / 3741)) (n := 12)
    (lo := (653707693 / 1000000000)) (hi := (326853847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1280) = 1/(1280 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653707693 / 1000000000) (326853847 / 500000000) (Real.log (2461 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2461 / 1280) = -Real.log (1280 / 2461) := by
    rw [show ((2461 / 1280) : ℝ) = ((1280 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (511899101 / 200000000) ≤ -Real.log (99 / 1280) ∧
    -Real.log (99 / 1280) ≤ (2559495509 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 99) = 1/(99 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2559495509 / 1000000000) (-511899101 / 200000000) (Real.log (99 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (652487933 / 1000000000) ≤ -Real.log (640 / 1229) ∧
    -Real.log (640 / 1229) ≤ (326243967 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1869)) (n := 12)
    (lo := (652487933 / 1000000000)) (hi := (326243967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 640) = 1/(640 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (652487933 / 1000000000) (326243967 / 500000000) (Real.log (1229 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1229 / 640) = -Real.log (640 / 1229) := by
    rw [show ((1229 / 640) : ℝ) = ((640 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2529642541 / 1000000000) ≤ -Real.log (51 / 640) ∧
    -Real.log (51 / 640) ≤ (505928509 / 200000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 51) = 1/(51 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-505928509 / 200000000) (-2529642541 / 1000000000) (Real.log (51 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (525416457 / 1000000000) ≤ -Real.log (1000000 / 1691163) ∧
    -Real.log (1000000 / 1691163) ≤ (262708229 / 500000000) := by
  have h := checkLog_sound (w := (691163 / 2691163)) (n := 12)
    (lo := (525416457 / 1000000000)) (hi := (262708229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1691163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1691163 / 1000000) = 1/(1000000 / 1691163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (525416457 / 1000000000) (262708229 / 500000000) (Real.log (1691163 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1691163 / 1000000) = -Real.log (1000000 / 1691163) := by
    rw [show ((1691163 / 1000000) : ℝ) = ((1000000 / 1691163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73433853 / 62500000) ≤ -Real.log (308837 / 1000000) ∧
    -Real.log (308837 / 1000000) ≤ (23498833 / 20000000) := by
  have h := checkLog_sound (w := (191163 / 808837)) (n := 12)
    (lo := (120448617 / 250000000)) (hi := (481794469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 308837) = 1/(308837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23498833 / 20000000) (-73433853 / 62500000) (Real.log (308837 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (526715901 / 1000000000) ≤ -Real.log (500000 / 846681) ∧
    -Real.log (500000 / 846681) ≤ (263357951 / 500000000) := by
  have h := checkLog_sound (w := (346681 / 1346681)) (n := 12)
    (lo := (526715901 / 1000000000)) (hi := (263357951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846681 / 500000) = 1/(500000 / 846681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (526715901 / 1000000000) (263357951 / 500000000) (Real.log (846681 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (846681 / 500000) = -Real.log (500000 / 846681) := by
    rw [show ((846681 / 500000) : ℝ) = ((500000 / 846681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1182087379 / 1000000000) ≤ -Real.log (153319 / 500000) ∧
    -Real.log (153319 / 500000) ≤ (1182087381 / 1000000000) := by
  have h := checkLog_sound (w := (96681 / 403319)) (n := 12)
    (lo := (488940199 / 1000000000)) (hi := (2444701 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 153319) = 1/(153319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1182087381 / 1000000000) (-1182087379 / 1000000000) (Real.log (153319 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55751323 / 125000000) ≤ -Real.log (250000 / 390517) ∧
    -Real.log (250000 / 390517) ≤ (89202117 / 200000000) := by
  have h := checkLog_sound (w := (140517 / 640517)) (n := 12)
    (lo := (55751323 / 125000000)) (hi := (89202117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390517 / 250000) = 1/(250000 / 390517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55751323 / 125000000) (89202117 / 200000000) (Real.log (390517 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (390517 / 250000) = -Real.log (250000 / 390517) := by
    rw [show ((390517 / 250000) : ℝ) = ((250000 / 390517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (825691631 / 1000000000) ≤ -Real.log (109483 / 250000) ∧
    -Real.log (109483 / 250000) ≤ (825691633 / 1000000000) := by
  have h := checkLog_sound (w := (15517 / 234483)) (n := 12)
    (lo := (132544451 / 1000000000)) (hi := (33136113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 109483) = 1/(109483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-825691633 / 1000000000) (-825691631 / 1000000000) (Real.log (109483 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22374447 / 50000000) ≤ -Real.log (1000000 / 1564379) ∧
    -Real.log (1000000 / 1564379) ≤ (447488941 / 1000000000) := by
  have h := checkLog_sound (w := (564379 / 2564379)) (n := 12)
    (lo := (22374447 / 50000000)) (hi := (447488941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1564379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1564379 / 1000000) = 1/(1000000 / 1564379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22374447 / 50000000) (447488941 / 1000000000) (Real.log (1564379 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1564379 / 1000000) = -Real.log (1000000 / 1564379) := by
    rw [show ((1564379 / 1000000) : ℝ) = ((1000000 / 1564379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (830982679 / 1000000000) ≤ -Real.log (435621 / 1000000) ∧
    -Real.log (435621 / 1000000) ≤ (830982681 / 1000000000) := by
  have h := checkLog_sound (w := (64379 / 935621)) (n := 12)
    (lo := (137835499 / 1000000000)) (hi := (275671 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 435621) = 1/(435621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-830982681 / 1000000000) (-830982679 / 1000000000) (Real.log (435621 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (850179053 / 500000000) ≤ -Real.log (4000000000 / 21903632013) ∧
    -Real.log (4000000000 / 21903632013) ≤ (1700358109 / 1000000000) := by
  have h := checkLog_sound (w := (5903632013 / 37903632013)) (n := 12)
    (lo := (157031873 / 500000000)) (hi := (314063747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21903632013 / 16000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21903632013 / 16000000000) = 1/(4000000000 / 21903632013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (850179053 / 500000000) (1700358109 / 1000000000) (Real.log (21903632013 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21903632013 / 4000000000) = -Real.log (4000000000 / 21903632013) := by
    rw [show ((21903632013 / 4000000000) : ℝ) = ((4000000000 / 21903632013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1708803281 / 1000000000) ≤ -Real.log (500000000000 / 2761174414131) ∧
    -Real.log (500000000000 / 2761174414131) ≤ (427200821 / 250000000) := by
  have h := checkLog_sound (w := (761174414131 / 4761174414131)) (n := 12)
    (lo := (322508921 / 1000000000)) (hi := (161254461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2761174414131 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2761174414131 / 2000000000000) = 1/(500000000000 / 2761174414131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1708803281 / 1000000000) (427200821 / 250000000) (Real.log (2761174414131 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2761174414131 / 500000000000) = -Real.log (500000000000 / 2761174414131) := by
    rw [show ((2761174414131 / 500000000000) : ℝ) = ((500000000000 / 2761174414131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254340443 / 200000000) ≤ -Real.log (50000000000 / 178345953253) ∧
    -Real.log (50000000000 / 178345953253) ≤ (1271702217 / 1000000000) := by
  have h := checkLog_sound (w := (78345953253 / 278345953253)) (n := 12)
    (lo := (115711007 / 200000000)) (hi := (144638759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178345953253 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(178345953253 / 100000000000) = 1/(50000000000 / 178345953253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254340443 / 200000000) (1271702217 / 1000000000) (Real.log (178345953253 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (178345953253 / 50000000000) = -Real.log (50000000000 / 178345953253) := by
    rw [show ((178345953253 / 50000000000) : ℝ) = ((50000000000 / 178345953253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1278471619 / 1000000000) ≤ -Real.log (20000000000 / 71822937829) ∧
    -Real.log (20000000000 / 71822937829) ≤ (1278471621 / 1000000000) := by
  have h := checkLog_sound (w := (31822937829 / 111822937829)) (n := 12)
    (lo := (585324439 / 1000000000)) (hi := (14633111 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71822937829 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71822937829 / 40000000000) = 1/(20000000000 / 71822937829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1278471619 / 1000000000) (1278471621 / 1000000000) (Real.log (71822937829 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (71822937829 / 20000000000) = -Real.log (20000000000 / 71822937829) := by
    rw [show ((71822937829 / 20000000000) : ℝ) = ((20000000000 / 71822937829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0044
