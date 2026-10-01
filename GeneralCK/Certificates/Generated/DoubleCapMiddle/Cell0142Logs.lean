import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0142
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

theorem reflection_log_1_neg : (297497029 / 1000000000) ≤ -Real.log (2560 / 3447) ∧
    -Real.log (2560 / 3447) ≤ (29749703 / 100000000) := by
  have h := checkLog_sound (w := (887 / 6007)) (n := 12)
    (lo := (297497029 / 1000000000)) (hi := (29749703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3447 / 2560) = 1/(2560 / 3447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (297497029 / 1000000000) (29749703 / 100000000) (Real.log (3447 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3447 / 2560) = -Real.log (2560 / 3447) := by
    rw [show ((3447 / 2560) : ℝ) = ((2560 / 3447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (106347209 / 250000000) ≤ -Real.log (1673 / 2560) ∧
    -Real.log (1673 / 2560) ≤ (425388837 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 4233)) (n := 12)
    (lo := (106347209 / 250000000)) (hi := (425388837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1673) = 1/(1673 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-425388837 / 1000000000) (-106347209 / 250000000) (Real.log (1673 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37078291 / 125000000) ≤ -Real.log (640 / 861) ∧
    -Real.log (640 / 861) ≤ (296626329 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1501)) (n := 12)
    (lo := (37078291 / 125000000)) (hi := (296626329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 640) = 1/(640 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37078291 / 125000000) (296626329 / 1000000000) (Real.log (861 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (861 / 640) = -Real.log (640 / 861) := by
    rw [show ((861 / 640) : ℝ) = ((640 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52949657 / 125000000) ≤ -Real.log (419 / 640) ∧
    -Real.log (419 / 640) ≤ (423597257 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1059)) (n := 12)
    (lo := (52949657 / 125000000)) (hi := (423597257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 419) = 1/(419 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-423597257 / 1000000000) (-52949657 / 125000000) (Real.log (419 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131620911 / 250000000) ≤ -Real.log (1280 / 2167) ∧
    -Real.log (1280 / 2167) ≤ (105296729 / 200000000) := by
  have h := checkLog_sound (w := (887 / 3447)) (n := 12)
    (lo := (131620911 / 250000000)) (hi := (105296729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2167 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2167 / 1280) = 1/(1280 / 2167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131620911 / 250000000) (105296729 / 200000000) (Real.log (2167 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2167 / 1280) = -Real.log (1280 / 2167) := by
    rw [show ((2167 / 1280) : ℝ) = ((1280 / 2167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (73800359 / 62500000) ≤ -Real.log (393 / 1280) ∧
    -Real.log (393 / 1280) ≤ (590402873 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 393) = 1/(393 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-590402873 / 500000000) (-73800359 / 62500000) (Real.log (393 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (525098283 / 1000000000) ≤ -Real.log (320 / 541) ∧
    -Real.log (320 / 541) ≤ (131274571 / 250000000) := by
  have h := checkLog_sound (w := (221 / 861)) (n := 12)
    (lo := (525098283 / 1000000000)) (hi := (131274571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541 / 320) = 1/(320 / 541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (525098283 / 1000000000) (131274571 / 250000000) (Real.log (541 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (541 / 320) = -Real.log (320 / 541) := by
    rw [show ((541 / 320) : ℝ) = ((320 / 541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (234640229 / 200000000) ≤ -Real.log (99 / 320) ∧
    -Real.log (99 / 320) ≤ (1173201147 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 99) = 1/(99 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1173201147 / 1000000000) (-234640229 / 200000000) (Real.log (99 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (405930333 / 1000000000) ≤ -Real.log (500000 / 750349) ∧
    -Real.log (500000 / 750349) ≤ (202965167 / 500000000) := by
  have h := checkLog_sound (w := (250349 / 1250349)) (n := 12)
    (lo := (405930333 / 1000000000)) (hi := (202965167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750349 / 500000) = 1/(500000 / 750349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (405930333 / 1000000000) (202965167 / 500000000) (Real.log (750349 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (750349 / 500000) = -Real.log (500000 / 750349) := by
    rw [show ((750349 / 500000) : ℝ) = ((500000 / 750349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (138908831 / 200000000) ≤ -Real.log (249651 / 500000) ∧
    -Real.log (249651 / 500000) ≤ (694544157 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 499651)) (n := 12)
    (lo := (55879 / 40000000)) (hi := (87311 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249651) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 249651) = 1/(249651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-694544157 / 1000000000) (-138908831 / 200000000) (Real.log (249651 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (407136377 / 1000000000) ≤ -Real.log (1000000 / 1502509) ∧
    -Real.log (1000000 / 1502509) ≤ (203568189 / 500000000) := by
  have h := checkLog_sound (w := (502509 / 2502509)) (n := 12)
    (lo := (407136377 / 1000000000)) (hi := (203568189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502509 / 1000000) = 1/(1000000 / 1502509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (407136377 / 1000000000) (203568189 / 500000000) (Real.log (1502509 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1502509 / 1000000) = -Real.log (1000000 / 1502509) := by
    rw [show ((1502509 / 1000000) : ℝ) = ((1000000 / 1502509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174544453 / 250000000) ≤ -Real.log (497491 / 1000000) ∧
    -Real.log (497491 / 1000000) ≤ (349088907 / 500000000) := by
  have h := checkLog_sound (w := (2509 / 997491)) (n := 12)
    (lo := (628829 / 125000000)) (hi := (5030633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497491) = 1/(497491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349088907 / 500000000) (-174544453 / 250000000) (Real.log (497491 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (322333467 / 1000000000) ≤ -Real.log (200000 / 276069) ∧
    -Real.log (200000 / 276069) ≤ (80583367 / 250000000) := by
  have h := checkLog_sound (w := (76069 / 476069)) (n := 12)
    (lo := (322333467 / 1000000000)) (hi := (80583367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276069 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276069 / 200000) = 1/(200000 / 276069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (322333467 / 1000000000) (80583367 / 250000000) (Real.log (276069 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (276069 / 200000) = -Real.log (200000 / 276069) := by
    rw [show ((276069 / 200000) : ℝ) = ((200000 / 276069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (478592407 / 1000000000) ≤ -Real.log (123931 / 200000) ∧
    -Real.log (123931 / 200000) ≤ (59824051 / 125000000) := by
  have h := checkLog_sound (w := (76069 / 323931)) (n := 12)
    (lo := (478592407 / 1000000000)) (hi := (59824051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123931) = 1/(123931 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59824051 / 125000000) (-478592407 / 1000000000) (Real.log (123931 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323476731 / 1000000000) ≤ -Real.log (250000 / 345481) ∧
    -Real.log (250000 / 345481) ≤ (80869183 / 250000000) := by
  have h := checkLog_sound (w := (95481 / 595481)) (n := 12)
    (lo := (323476731 / 1000000000)) (hi := (80869183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345481 / 250000) = 1/(250000 / 345481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323476731 / 1000000000) (80869183 / 250000000) (Real.log (345481 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (345481 / 250000) = -Real.log (250000 / 345481) := by
    rw [show ((345481 / 250000) : ℝ) = ((250000 / 345481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (481143851 / 1000000000) ≤ -Real.log (154519 / 250000) ∧
    -Real.log (154519 / 250000) ≤ (120285963 / 250000000) := by
  have h := checkLog_sound (w := (95481 / 404519)) (n := 12)
    (lo := (481143851 / 1000000000)) (hi := (120285963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154519) = 1/(154519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120285963 / 250000000) (-481143851 / 1000000000) (Real.log (154519 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (137559311 / 125000000) ≤ -Real.log (12500000000 / 37569897577) ∧
    -Real.log (12500000000 / 37569897577) ≤ (110047449 / 100000000) := by
  have h := checkLog_sound (w := (12569897577 / 62569897577)) (n := 12)
    (lo := (101831827 / 250000000)) (hi := (407327309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37569897577 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37569897577 / 25000000000) = 1/(12500000000 / 37569897577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (137559311 / 125000000) (110047449 / 100000000) (Real.log (37569897577 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (37569897577 / 12500000000) = -Real.log (12500000000 / 37569897577) := by
    rw [show ((37569897577 / 12500000000) : ℝ) = ((12500000000 / 37569897577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1105314189 / 1000000000) ≤ -Real.log (500000000000 / 1510086614633) ∧
    -Real.log (500000000000 / 1510086614633) ≤ (1105314191 / 1000000000) := by
  have h := checkLog_sound (w := (510086614633 / 2510086614633)) (n := 12)
    (lo := (412167009 / 1000000000)) (hi := (41216701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510086614633 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1510086614633 / 1000000000000) = 1/(500000000000 / 1510086614633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1105314189 / 1000000000) (1105314191 / 1000000000) (Real.log (1510086614633 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1510086614633 / 500000000000) = -Real.log (500000000000 / 1510086614633) := by
    rw [show ((1510086614633 / 500000000000) : ℝ) = ((500000000000 / 1510086614633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (400462937 / 500000000) ≤ -Real.log (250000000000 / 556900614051) ∧
    -Real.log (250000000000 / 556900614051) ≤ (200231469 / 250000000) := by
  have h := checkLog_sound (w := (56900614051 / 1056900614051)) (n := 12)
    (lo := (53889347 / 500000000)) (hi := (21555739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556900614051 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556900614051 / 500000000000) = 1/(250000000000 / 556900614051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (400462937 / 500000000) (200231469 / 250000000) (Real.log (556900614051 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (556900614051 / 250000000000) = -Real.log (250000000000 / 556900614051) := by
    rw [show ((556900614051 / 250000000000) : ℝ) = ((250000000000 / 556900614051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (402310291 / 500000000) ≤ -Real.log (250000000000 / 558962004673) ∧
    -Real.log (250000000000 / 558962004673) ≤ (100577573 / 125000000) := by
  have h := checkLog_sound (w := (58962004673 / 1058962004673)) (n := 12)
    (lo := (55736701 / 500000000)) (hi := (111473403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558962004673 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558962004673 / 500000000000) = 1/(250000000000 / 558962004673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (402310291 / 500000000) (100577573 / 125000000) (Real.log (558962004673 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (558962004673 / 250000000000) = -Real.log (250000000000 / 558962004673) := by
    rw [show ((558962004673 / 250000000000) : ℝ) = ((250000000000 / 558962004673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0142
