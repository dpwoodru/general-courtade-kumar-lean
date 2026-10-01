import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0140
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

theorem reflection_log_1_neg : (299236159 / 1000000000) ≤ -Real.log (2560 / 3453) ∧
    -Real.log (2560 / 3453) ≤ (935113 / 3125000) := by
  have h := checkLog_sound (w := (893 / 6013)) (n := 12)
    (lo := (299236159 / 1000000000)) (hi := (935113 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3453 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3453 / 2560) = 1/(2560 / 3453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (299236159 / 1000000000) (935113 / 3125000) (Real.log (3453 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3453 / 2560) = -Real.log (2560 / 3453) := by
    rw [show ((3453 / 2560) : ℝ) = ((2560 / 3453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (214490827 / 500000000) ≤ -Real.log (1667 / 2560) ∧
    -Real.log (1667 / 2560) ≤ (85796331 / 200000000) := by
  have h := checkLog_sound (w := (893 / 4227)) (n := 12)
    (lo := (214490827 / 500000000)) (hi := (85796331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1667) = 1/(1667 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-85796331 / 200000000) (-214490827 / 500000000) (Real.log (1667 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (74591743 / 250000000) ≤ -Real.log (256 / 345) ∧
    -Real.log (256 / 345) ≤ (298366973 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 601)) (n := 12)
    (lo := (74591743 / 250000000)) (hi := (298366973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345 / 256) = 1/(256 / 345) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (74591743 / 250000000) (298366973 / 1000000000) (Real.log (345 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (345 / 256) = -Real.log (256 / 345) := by
    rw [show ((345 / 256) : ℝ) = ((256 / 345) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26698977 / 62500000) ≤ -Real.log (167 / 256) ∧
    -Real.log (167 / 256) ≤ (427183633 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 423)) (n := 12)
    (lo := (26698977 / 62500000)) (hi := (427183633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 167) = 1/(167 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-427183633 / 1000000000) (-26698977 / 62500000) (Real.log (167 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (529248623 / 1000000000) ≤ -Real.log (1280 / 2173) ∧
    -Real.log (1280 / 2173) ≤ (33078039 / 62500000) := by
  have h := checkLog_sound (w := (893 / 3453)) (n := 12)
    (lo := (529248623 / 1000000000)) (hi := (33078039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2173 / 1280) = 1/(1280 / 2173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (529248623 / 1000000000) (33078039 / 62500000) (Real.log (2173 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2173 / 1280) = -Real.log (1280 / 2173) := by
    rw [show ((2173 / 1280) : ℝ) = ((1280 / 2173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1196190663 / 1000000000) ≤ -Real.log (387 / 1280) ∧
    -Real.log (387 / 1280) ≤ (239238133 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 387) = 1/(387 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239238133 / 200000000) (-1196190663 / 1000000000) (Real.log (387 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (527867089 / 1000000000) ≤ -Real.log (128 / 217) ∧
    -Real.log (128 / 217) ≤ (52786709 / 100000000) := by
  have h := checkLog_sound (w := (89 / 345)) (n := 12)
    (lo := (527867089 / 1000000000)) (hi := (52786709 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217 / 128) = 1/(128 / 217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (527867089 / 1000000000) (52786709 / 100000000) (Real.log (217 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (217 / 128) = -Real.log (128 / 217) := by
    rw [show ((217 / 128) : ℝ) = ((128 / 217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1188468617 / 1000000000) ≤ -Real.log (39 / 128) ∧
    -Real.log (39 / 128) ≤ (1188468619 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 39) = 1/(39 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1188468619 / 1000000000) (-1188468617 / 1000000000) (Real.log (39 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25521269 / 62500000) ≤ -Real.log (1000000 / 1504319) ∧
    -Real.log (1000000 / 1504319) ≤ (81668061 / 200000000) := by
  have h := checkLog_sound (w := (504319 / 2504319)) (n := 12)
    (lo := (25521269 / 62500000)) (hi := (81668061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504319 / 1000000) = 1/(1000000 / 1504319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25521269 / 62500000) (81668061 / 200000000) (Real.log (1504319 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1504319 / 1000000) = -Real.log (1000000 / 1504319) := by
    rw [show ((1504319 / 1000000) : ℝ) = ((1000000 / 1504319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (701822703 / 1000000000) ≤ -Real.log (495681 / 1000000) ∧
    -Real.log (495681 / 1000000) ≤ (140364541 / 200000000) := by
  have h := checkLog_sound (w := (4319 / 995681)) (n := 12)
    (lo := (8675523 / 1000000000)) (hi := (2168881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495681) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495681) = 1/(495681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-140364541 / 200000000) (-701822703 / 1000000000) (Real.log (495681 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (204772387 / 500000000) ≤ -Real.log (250000 / 376533) ∧
    -Real.log (250000 / 376533) ≤ (16381791 / 40000000) := by
  have h := checkLog_sound (w := (126533 / 626533)) (n := 12)
    (lo := (204772387 / 500000000)) (hi := (16381791 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376533 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376533 / 250000) = 1/(250000 / 376533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (204772387 / 500000000) (16381791 / 40000000) (Real.log (376533 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376533 / 250000) = -Real.log (250000 / 376533) := by
    rw [show ((376533 / 250000) : ℝ) = ((250000 / 376533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (705487003 / 1000000000) ≤ -Real.log (123467 / 250000) ∧
    -Real.log (123467 / 250000) ≤ (141097401 / 200000000) := by
  have h := checkLog_sound (w := (1533 / 248467)) (n := 12)
    (lo := (12339823 / 1000000000)) (hi := (771239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 123467) = 1/(123467 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-141097401 / 200000000) (-705487003 / 1000000000) (Real.log (123467 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (162310067 / 500000000) ≤ -Real.log (200000 / 276701) ∧
    -Real.log (200000 / 276701) ≤ (64924027 / 200000000) := by
  have h := checkLog_sound (w := (76701 / 476701)) (n := 12)
    (lo := (162310067 / 500000000)) (hi := (64924027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276701 / 200000) = 1/(200000 / 276701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (162310067 / 500000000) (64924027 / 200000000) (Real.log (276701 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (276701 / 200000) = -Real.log (200000 / 276701) := by
    rw [show ((276701 / 200000) : ℝ) = ((200000 / 276701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (241852533 / 500000000) ≤ -Real.log (123299 / 200000) ∧
    -Real.log (123299 / 200000) ≤ (483705067 / 1000000000) := by
  have h := checkLog_sound (w := (76701 / 323299)) (n := 12)
    (lo := (241852533 / 500000000)) (hi := (483705067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123299) = 1/(123299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-483705067 / 1000000000) (-241852533 / 500000000) (Real.log (123299 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (325766563 / 1000000000) ≤ -Real.log (250000 / 346273) ∧
    -Real.log (250000 / 346273) ≤ (81441641 / 250000000) := by
  have h := checkLog_sound (w := (96273 / 596273)) (n := 12)
    (lo := (325766563 / 1000000000)) (hi := (81441641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346273 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346273 / 250000) = 1/(250000 / 346273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (325766563 / 1000000000) (81441641 / 250000000) (Real.log (346273 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (346273 / 250000) = -Real.log (250000 / 346273) := by
    rw [show ((346273 / 250000) : ℝ) = ((250000 / 346273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (97256523 / 200000000) ≤ -Real.log (153727 / 250000) ∧
    -Real.log (153727 / 250000) ≤ (60785327 / 125000000) := by
  have h := checkLog_sound (w := (96273 / 403727)) (n := 12)
    (lo := (97256523 / 200000000)) (hi := (60785327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153727) = 1/(153727 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60785327 / 125000000) (-97256523 / 200000000) (Real.log (153727 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1110163007 / 1000000000) ≤ -Real.log (500000000000 / 1517426530369) ∧
    -Real.log (500000000000 / 1517426530369) ≤ (1110163009 / 1000000000) := by
  have h := checkLog_sound (w := (517426530369 / 2517426530369)) (n := 12)
    (lo := (417015827 / 1000000000)) (hi := (104253957 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517426530369 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1517426530369 / 1000000000000) = 1/(500000000000 / 1517426530369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1110163007 / 1000000000) (1110163009 / 1000000000) (Real.log (1517426530369 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1517426530369 / 500000000000) = -Real.log (500000000000 / 1517426530369) := by
    rw [show ((1517426530369 / 500000000000) : ℝ) = ((500000000000 / 1517426530369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (557515889 / 500000000) ≤ -Real.log (500000000000 / 1524832546349) ∧
    -Real.log (500000000000 / 1524832546349) ≤ (55751589 / 50000000) := by
  have h := checkLog_sound (w := (524832546349 / 2524832546349)) (n := 12)
    (lo := (210942299 / 500000000)) (hi := (421884599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524832546349 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1524832546349 / 1000000000000) = 1/(500000000000 / 1524832546349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (557515889 / 500000000) (55751589 / 50000000) (Real.log (1524832546349 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1524832546349 / 500000000000) = -Real.log (500000000000 / 1524832546349) := by
    rw [show ((1524832546349 / 500000000000) : ℝ) = ((500000000000 / 1524832546349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2020813 / 2500000) ≤ -Real.log (12500000000 / 28051829293) ∧
    -Real.log (12500000000 / 28051829293) ≤ (404162601 / 500000000) := by
  have h := checkLog_sound (w := (3051829293 / 53051829293)) (n := 12)
    (lo := (5758901 / 50000000)) (hi := (115178021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28051829293 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(28051829293 / 25000000000) = 1/(12500000000 / 28051829293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2020813 / 2500000) (404162601 / 500000000) (Real.log (28051829293 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28051829293 / 12500000000) = -Real.log (12500000000 / 28051829293) := by
    rw [show ((28051829293 / 12500000000) : ℝ) = ((12500000000 / 28051829293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (406024589 / 500000000) ≤ -Real.log (500000000000 / 1126259538013) ∧
    -Real.log (500000000000 / 1126259538013) ≤ (40602459 / 50000000) := by
  have h := checkLog_sound (w := (126259538013 / 2126259538013)) (n := 12)
    (lo := (59450999 / 500000000)) (hi := (118901999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126259538013 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126259538013 / 1000000000000) = 1/(500000000000 / 1126259538013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (406024589 / 500000000) (40602459 / 50000000) (Real.log (1126259538013 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1126259538013 / 500000000000) = -Real.log (500000000000 / 1126259538013) := by
    rw [show ((1126259538013 / 500000000000) : ℝ) = ((500000000000 / 1126259538013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0140
