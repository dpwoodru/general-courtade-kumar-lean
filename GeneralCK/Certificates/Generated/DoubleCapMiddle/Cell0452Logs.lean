import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0452
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

theorem reflection_log_1_neg : (187678277 / 1000000000) ≤ -Real.log (5120 / 6177) ∧
    -Real.log (5120 / 6177) ≤ (93839139 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 11297)) (n := 12)
    (lo := (187678277 / 1000000000)) (hi := (93839139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 5120) = 1/(5120 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187678277 / 1000000000) (93839139 / 500000000) (Real.log (6177 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6177 / 5120) = -Real.log (5120 / 6177) := by
    rw [show ((6177 / 5120) : ℝ) = ((5120 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (115616411 / 500000000) ≤ -Real.log (4063 / 5120) ∧
    -Real.log (4063 / 5120) ≤ (231232823 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 9183)) (n := 12)
    (lo := (115616411 / 500000000)) (hi := (231232823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4063) = 1/(4063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-231232823 / 1000000000) (-115616411 / 500000000) (Real.log (4063 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187435411 / 1000000000) ≤ -Real.log (10240 / 12351) ∧
    -Real.log (10240 / 12351) ≤ (46858853 / 250000000) := by
  have h := checkLog_sound (w := (2111 / 22591)) (n := 12)
    (lo := (187435411 / 1000000000)) (hi := (46858853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12351 / 10240) = 1/(10240 / 12351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187435411 / 1000000000) (46858853 / 250000000) (Real.log (12351 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12351 / 10240) = -Real.log (10240 / 12351) := by
    rw [show ((12351 / 10240) : ℝ) = ((10240 / 12351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28857963 / 125000000) ≤ -Real.log (8129 / 10240) ∧
    -Real.log (8129 / 10240) ≤ (46172741 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 18369)) (n := 12)
    (lo := (28857963 / 125000000)) (hi := (46172741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8129) = 1/(8129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46172741 / 200000000) (-28857963 / 125000000) (Real.log (8129 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172818847 / 500000000) ≤ -Real.log (2560 / 3617) ∧
    -Real.log (2560 / 3617) ≤ (69127539 / 200000000) := by
  have h := checkLog_sound (w := (1057 / 6177)) (n := 12)
    (lo := (172818847 / 500000000)) (hi := (69127539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3617 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3617 / 2560) = 1/(2560 / 3617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172818847 / 500000000) (69127539 / 200000000) (Real.log (3617 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3617 / 2560) = -Real.log (2560 / 3617) := by
    rw [show ((3617 / 2560) : ℝ) = ((2560 / 3617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (532544147 / 1000000000) ≤ -Real.log (1503 / 2560) ∧
    -Real.log (1503 / 2560) ≤ (133136037 / 250000000) := by
  have h := checkLog_sound (w := (1057 / 4063)) (n := 12)
    (lo := (532544147 / 1000000000)) (hi := (133136037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1503) = 1/(1503 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133136037 / 250000000) (-532544147 / 1000000000) (Real.log (1503 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3452229 / 10000000) ≤ -Real.log (5120 / 7231) ∧
    -Real.log (5120 / 7231) ≤ (345222901 / 1000000000) := by
  have h := checkLog_sound (w := (2111 / 12351)) (n := 12)
    (lo := (3452229 / 10000000)) (hi := (345222901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7231 / 5120) = 1/(5120 / 7231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3452229 / 10000000) (345222901 / 1000000000) (Real.log (7231 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7231 / 5120) = -Real.log (5120 / 7231) := by
    rw [show ((7231 / 5120) : ℝ) = ((5120 / 7231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (531546641 / 1000000000) ≤ -Real.log (3009 / 5120) ∧
    -Real.log (3009 / 5120) ≤ (265773321 / 500000000) := by
  have h := checkLog_sound (w := (2111 / 8129)) (n := 12)
    (lo := (531546641 / 1000000000)) (hi := (265773321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3009) = 1/(3009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-265773321 / 500000000) (-531546641 / 1000000000) (Real.log (3009 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25755889 / 100000000) ≤ -Real.log (125000 / 161721) ∧
    -Real.log (125000 / 161721) ≤ (257558891 / 1000000000) := by
  have h := checkLog_sound (w := (36721 / 286721)) (n := 12)
    (lo := (25755889 / 100000000)) (hi := (257558891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161721 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161721 / 125000) = 1/(125000 / 161721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25755889 / 100000000) (257558891 / 1000000000) (Real.log (161721 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (161721 / 125000) = -Real.log (125000 / 161721) := by
    rw [show ((161721 / 125000) : ℝ) = ((125000 / 161721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (347811483 / 1000000000) ≤ -Real.log (88279 / 125000) ∧
    -Real.log (88279 / 125000) ≤ (86952871 / 250000000) := by
  have h := checkLog_sound (w := (36721 / 213279)) (n := 12)
    (lo := (347811483 / 1000000000)) (hi := (86952871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88279) = 1/(88279 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86952871 / 250000000) (-347811483 / 1000000000) (Real.log (88279 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128943667 / 500000000) ≤ -Real.log (1000000 / 1294193) ∧
    -Real.log (1000000 / 1294193) ≤ (51577467 / 200000000) := by
  have h := checkLog_sound (w := (294193 / 2294193)) (n := 12)
    (lo := (128943667 / 500000000)) (hi := (51577467 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294193 / 1000000) = 1/(1000000 / 1294193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128943667 / 500000000) (51577467 / 200000000) (Real.log (1294193 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1294193 / 1000000) = -Real.log (1000000 / 1294193) := by
    rw [show ((1294193 / 1000000) : ℝ) = ((1000000 / 1294193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (348413449 / 1000000000) ≤ -Real.log (705807 / 1000000) ∧
    -Real.log (705807 / 1000000) ≤ (6968269 / 20000000) := by
  have h := checkLog_sound (w := (294193 / 1705807)) (n := 12)
    (lo := (348413449 / 1000000000)) (hi := (6968269 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705807) = 1/(705807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6968269 / 20000000) (-348413449 / 1000000000) (Real.log (705807 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38588161 / 200000000) ≤ -Real.log (1000000 / 1212811) ∧
    -Real.log (1000000 / 1212811) ≤ (96470403 / 500000000) := by
  have h := checkLog_sound (w := (212811 / 2212811)) (n := 12)
    (lo := (38588161 / 200000000)) (hi := (96470403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212811 / 1000000) = 1/(1000000 / 1212811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38588161 / 200000000) (96470403 / 500000000) (Real.log (1212811 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1212811 / 1000000) = -Real.log (1000000 / 1212811) := by
    rw [show ((1212811 / 1000000) : ℝ) = ((1000000 / 1212811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (119643453 / 500000000) ≤ -Real.log (787189 / 1000000) ∧
    -Real.log (787189 / 1000000) ≤ (239286907 / 1000000000) := by
  have h := checkLog_sound (w := (212811 / 1787189)) (n := 12)
    (lo := (119643453 / 500000000)) (hi := (239286907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787189) = 1/(787189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-239286907 / 1000000000) (-119643453 / 500000000) (Real.log (787189 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (193207093 / 1000000000) ≤ -Real.log (500000 / 606567) ∧
    -Real.log (500000 / 606567) ≤ (96603547 / 500000000) := by
  have h := checkLog_sound (w := (106567 / 1106567)) (n := 12)
    (lo := (193207093 / 1000000000)) (hi := (96603547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606567 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606567 / 500000) = 1/(500000 / 606567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (193207093 / 1000000000) (96603547 / 500000000) (Real.log (606567 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (606567 / 500000) = -Real.log (500000 / 606567) := by
    rw [show ((606567 / 500000) : ℝ) = ((500000 / 606567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (239697311 / 1000000000) ≤ -Real.log (393433 / 500000) ∧
    -Real.log (393433 / 500000) ≤ (7490541 / 31250000) := by
  have h := checkLog_sound (w := (106567 / 893433)) (n := 12)
    (lo := (239697311 / 1000000000)) (hi := (7490541 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393433) = 1/(393433 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-7490541 / 31250000) (-239697311 / 1000000000) (Real.log (393433 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (302685187 / 500000000) ≤ -Real.log (250000000000 / 457982645929) ∧
    -Real.log (250000000000 / 457982645929) ≤ (4842963 / 8000000) := by
  have h := checkLog_sound (w := (207982645929 / 707982645929)) (n := 12)
    (lo := (302685187 / 500000000)) (hi := (4842963 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457982645929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457982645929 / 250000000000) = 1/(250000000000 / 457982645929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302685187 / 500000000) (4842963 / 8000000) (Real.log (457982645929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (457982645929 / 250000000000) = -Real.log (250000000000 / 457982645929) := by
    rw [show ((457982645929 / 250000000000) : ℝ) = ((250000000000 / 457982645929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37893799 / 62500000) ≤ -Real.log (500000000000 / 916817911979) ∧
    -Real.log (500000000000 / 916817911979) ≤ (121260157 / 200000000) := by
  have h := checkLog_sound (w := (416817911979 / 1416817911979)) (n := 12)
    (lo := (37893799 / 62500000)) (hi := (121260157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916817911979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916817911979 / 500000000000) = 1/(500000000000 / 916817911979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37893799 / 62500000) (121260157 / 200000000) (Real.log (916817911979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (916817911979 / 500000000000) = -Real.log (500000000000 / 916817911979) := by
    rw [show ((916817911979 / 500000000000) : ℝ) = ((500000000000 / 916817911979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3376779 / 7812500) ≤ -Real.log (500000000000 / 770342954487) ∧
    -Real.log (500000000000 / 770342954487) ≤ (432227713 / 1000000000) := by
  have h := checkLog_sound (w := (270342954487 / 1270342954487)) (n := 12)
    (lo := (3376779 / 7812500)) (hi := (432227713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770342954487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770342954487 / 500000000000) = 1/(500000000000 / 770342954487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3376779 / 7812500) (432227713 / 1000000000) (Real.log (770342954487 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (770342954487 / 500000000000) = -Real.log (500000000000 / 770342954487) := by
    rw [show ((770342954487 / 500000000000) : ℝ) = ((500000000000 / 770342954487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (86580881 / 200000000) ≤ -Real.log (500000000000 / 770864416559) ∧
    -Real.log (500000000000 / 770864416559) ≤ (216452203 / 500000000) := by
  have h := checkLog_sound (w := (270864416559 / 1270864416559)) (n := 12)
    (lo := (86580881 / 200000000)) (hi := (216452203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770864416559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770864416559 / 500000000000) = 1/(500000000000 / 770864416559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (86580881 / 200000000) (216452203 / 500000000) (Real.log (770864416559 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (770864416559 / 500000000000) = -Real.log (500000000000 / 770864416559) := by
    rw [show ((770864416559 / 500000000000) : ℝ) = ((500000000000 / 770864416559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0452
