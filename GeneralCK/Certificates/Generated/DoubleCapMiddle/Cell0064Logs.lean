import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0064
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

theorem reflection_log_1_neg : (72635439 / 200000000) ≤ -Real.log (2560 / 3681) ∧
    -Real.log (2560 / 3681) ≤ (90794299 / 250000000) := by
  have h := checkLog_sound (w := (1121 / 6241)) (n := 12)
    (lo := (72635439 / 200000000)) (hi := (90794299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3681 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3681 / 2560) = 1/(2560 / 3681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72635439 / 200000000) (90794299 / 250000000) (Real.log (3681 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3681 / 2560) = -Real.log (2560 / 3681) := by
    rw [show ((3681 / 2560) : ℝ) = ((2560 / 3681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57605883 / 100000000) ≤ -Real.log (1439 / 2560) ∧
    -Real.log (1439 / 2560) ≤ (576058831 / 1000000000) := by
  have h := checkLog_sound (w := (1121 / 3999)) (n := 12)
    (lo := (57605883 / 100000000)) (hi := (576058831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1439) = 1/(1439 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-576058831 / 1000000000) (-57605883 / 100000000) (Real.log (1439 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (362361867 / 1000000000) ≤ -Real.log (1280 / 1839) ∧
    -Real.log (1280 / 1839) ≤ (90590467 / 250000000) := by
  have h := checkLog_sound (w := (559 / 3119)) (n := 12)
    (lo := (362361867 / 1000000000)) (hi := (90590467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1280) = 1/(1280 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (362361867 / 1000000000) (90590467 / 250000000) (Real.log (1839 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1839 / 1280) = -Real.log (1280 / 1839) := by
    rw [show ((1839 / 1280) : ℝ) = ((1280 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (573976219 / 1000000000) ≤ -Real.log (721 / 1280) ∧
    -Real.log (721 / 1280) ≤ (28698811 / 50000000) := by
  have h := checkLog_sound (w := (559 / 2001)) (n := 12)
    (lo := (573976219 / 1000000000)) (hi := (28698811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 721) = 1/(721 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28698811 / 50000000) (-573976219 / 1000000000) (Real.log (721 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (629025239 / 1000000000) ≤ -Real.log (1280 / 2401) ∧
    -Real.log (1280 / 2401) ≤ (15725631 / 25000000) := by
  have h := checkLog_sound (w := (1121 / 3681)) (n := 12)
    (lo := (629025239 / 1000000000)) (hi := (15725631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 1280) = 1/(1280 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (629025239 / 1000000000) (15725631 / 25000000) (Real.log (2401 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2401 / 1280) = -Real.log (1280 / 2401) := by
    rw [show ((2401 / 1280) : ℝ) = ((1280 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2085711153 / 1000000000) ≤ -Real.log (159 / 1280) ∧
    -Real.log (159 / 1280) ≤ (2085711157 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 159) = 1/(159 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2085711157 / 1000000000) (-2085711153 / 1000000000) (Real.log (159 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (313887489 / 500000000) ≤ -Real.log (640 / 1199) ∧
    -Real.log (640 / 1199) ≤ (627774979 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 1839)) (n := 12)
    (lo := (313887489 / 500000000)) (hi := (627774979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 640) = 1/(640 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (313887489 / 500000000) (627774979 / 1000000000) (Real.log (1199 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199 / 640) = -Real.log (640 / 1199) := by
    rw [show ((1199 / 640) : ℝ) = ((640 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103350951 / 50000000) ≤ -Real.log (81 / 640) ∧
    -Real.log (81 / 640) ≤ (2067019023 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 81) = 1/(81 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2067019023 / 1000000000) (-103350951 / 50000000) (Real.log (81 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125037561 / 250000000) ≤ -Real.log (1000000 / 1648969) ∧
    -Real.log (1000000 / 1648969) ≤ (100030049 / 200000000) := by
  have h := checkLog_sound (w := (648969 / 2648969)) (n := 12)
    (lo := (125037561 / 250000000)) (hi := (100030049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648969 / 1000000) = 1/(1000000 / 1648969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125037561 / 250000000) (100030049 / 200000000) (Real.log (1648969 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1648969 / 1000000) = -Real.log (1000000 / 1648969) := by
    rw [show ((1648969 / 1000000) : ℝ) = ((1000000 / 1648969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1046880739 / 1000000000) ≤ -Real.log (351031 / 1000000) ∧
    -Real.log (351031 / 1000000) ≤ (1046880741 / 1000000000) := by
  have h := checkLog_sound (w := (148969 / 851031)) (n := 12)
    (lo := (353733559 / 1000000000)) (hi := (8843339 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351031) = 1/(351031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1046880741 / 1000000000) (-1046880739 / 1000000000) (Real.log (351031 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125347411 / 250000000) ≤ -Real.log (500000 / 825507) ∧
    -Real.log (500000 / 825507) ≤ (100277929 / 200000000) := by
  have h := checkLog_sound (w := (325507 / 1325507)) (n := 12)
    (lo := (125347411 / 250000000)) (hi := (100277929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825507 / 500000) = 1/(500000 / 825507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125347411 / 250000000) (100277929 / 200000000) (Real.log (825507 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (825507 / 500000) = -Real.log (500000 / 825507) := by
    rw [show ((825507 / 500000) : ℝ) = ((500000 / 825507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1052723471 / 1000000000) ≤ -Real.log (174493 / 500000) ∧
    -Real.log (174493 / 500000) ≤ (1052723473 / 1000000000) := by
  have h := checkLog_sound (w := (75507 / 424493)) (n := 12)
    (lo := (359576291 / 1000000000)) (hi := (89894073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174493) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 174493) = 1/(174493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1052723473 / 1000000000) (-1052723471 / 1000000000) (Real.log (174493 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (417895529 / 1000000000) ≤ -Real.log (500000 / 759381) ∧
    -Real.log (500000 / 759381) ≤ (41789553 / 100000000) := by
  have h := checkLog_sound (w := (259381 / 1259381)) (n := 12)
    (lo := (417895529 / 1000000000)) (hi := (41789553 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759381 / 500000) = 1/(500000 / 759381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (417895529 / 1000000000) (41789553 / 100000000) (Real.log (759381 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (759381 / 500000) = -Real.log (500000 / 759381) := by
    rw [show ((759381 / 500000) : ℝ) = ((500000 / 759381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (45712083 / 62500000) ≤ -Real.log (240619 / 500000) ∧
    -Real.log (240619 / 500000) ≤ (73139333 / 100000000) := by
  have h := checkLog_sound (w := (9381 / 490619)) (n := 12)
    (lo := (9561537 / 250000000)) (hi := (38246149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 240619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 240619) = 1/(240619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-73139333 / 100000000) (-45712083 / 62500000) (Real.log (240619 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (41924769 / 100000000) ≤ -Real.log (1000000 / 1520817) ∧
    -Real.log (1000000 / 1520817) ≤ (419247691 / 1000000000) := by
  have h := checkLog_sound (w := (520817 / 2520817)) (n := 12)
    (lo := (41924769 / 100000000)) (hi := (419247691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1520817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1520817 / 1000000) = 1/(1000000 / 1520817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (41924769 / 100000000) (419247691 / 1000000000) (Real.log (1520817 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1520817 / 1000000) = -Real.log (1000000 / 1520817) := by
    rw [show ((1520817 / 1000000) : ℝ) = ((1000000 / 1520817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (183918177 / 250000000) ≤ -Real.log (479183 / 1000000) ∧
    -Real.log (479183 / 1000000) ≤ (73567271 / 100000000) := by
  have h := checkLog_sound (w := (20817 / 979183)) (n := 12)
    (lo := (5315691 / 125000000)) (hi := (42525529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 479183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 479183) = 1/(479183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-73567271 / 100000000) (-183918177 / 250000000) (Real.log (479183 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1547030983 / 1000000000) ≤ -Real.log (500000000000 / 2348751249889) ∧
    -Real.log (500000000000 / 2348751249889) ≤ (773515493 / 500000000) := by
  have h := checkLog_sound (w := (348751249889 / 4348751249889)) (n := 12)
    (lo := (160736623 / 1000000000)) (hi := (10046039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2348751249889 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2348751249889 / 2000000000000) = 1/(500000000000 / 2348751249889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1547030983 / 1000000000) (773515493 / 500000000) (Real.log (2348751249889 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2348751249889 / 500000000000) = -Real.log (500000000000 / 2348751249889) := by
    rw [show ((2348751249889 / 500000000000) : ℝ) = ((500000000000 / 2348751249889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310822623 / 200000000) ≤ -Real.log (500000000000 / 2365444459091) ∧
    -Real.log (500000000000 / 2365444459091) ≤ (777056559 / 500000000) := by
  have h := checkLog_sound (w := (365444459091 / 4365444459091)) (n := 12)
    (lo := (33563751 / 200000000)) (hi := (41954689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365444459091 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365444459091 / 2000000000000) = 1/(500000000000 / 2365444459091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310822623 / 200000000) (777056559 / 500000000) (Real.log (2365444459091 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2365444459091 / 500000000000) = -Real.log (500000000000 / 2365444459091) := by
    rw [show ((2365444459091 / 500000000000) : ℝ) = ((500000000000 / 2365444459091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1149288857 / 1000000000) ≤ -Real.log (31250000000 / 98623368271) ∧
    -Real.log (31250000000 / 98623368271) ≤ (1149288859 / 1000000000) := by
  have h := checkLog_sound (w := (36123368271 / 161123368271)) (n := 12)
    (lo := (456141677 / 1000000000)) (hi := (228070839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98623368271 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(98623368271 / 62500000000) = 1/(31250000000 / 98623368271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1149288857 / 1000000000) (1149288859 / 1000000000) (Real.log (98623368271 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (98623368271 / 31250000000) = -Real.log (31250000000 / 98623368271) := by
    rw [show ((98623368271 / 31250000000) : ℝ) = ((31250000000 / 98623368271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (577460199 / 500000000) ≤ -Real.log (62500000000 / 198360673271) ∧
    -Real.log (62500000000 / 198360673271) ≤ (2887301 / 2500000) := by
  have h := checkLog_sound (w := (73360673271 / 323360673271)) (n := 12)
    (lo := (230886609 / 500000000)) (hi := (461773219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198360673271 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(198360673271 / 125000000000) = 1/(62500000000 / 198360673271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (577460199 / 500000000) (2887301 / 2500000) (Real.log (198360673271 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (198360673271 / 62500000000) = -Real.log (62500000000 / 198360673271) := by
    rw [show ((198360673271 / 62500000000) : ℝ) = ((62500000000 / 198360673271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0064
