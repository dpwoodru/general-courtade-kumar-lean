import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0031
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

theorem reflection_log_1_neg : (389716751 / 1000000000) ≤ -Real.log (128 / 189) ∧
    -Real.log (128 / 189) ≤ (24357297 / 62500000) := by
  have h := checkLog_sound (w := (61 / 317)) (n := 12)
    (lo := (389716751 / 1000000000)) (hi := (24357297 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 128) = 1/(128 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (389716751 / 1000000000) (24357297 / 62500000) (Real.log (189 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (189 / 128) = -Real.log (128 / 189) := by
    rw [show ((189 / 128) : ℝ) = ((128 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (161834411 / 250000000) ≤ -Real.log (67 / 128) ∧
    -Real.log (67 / 128) ≤ (129467529 / 200000000) := by
  have h := checkLog_sound (w := (61 / 195)) (n := 12)
    (lo := (161834411 / 250000000)) (hi := (129467529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 67) = 1/(67 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129467529 / 200000000) (-161834411 / 250000000) (Real.log (67 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (77784557 / 200000000) ≤ -Real.log (2560 / 3777) ∧
    -Real.log (2560 / 3777) ≤ (194461393 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 6337)) (n := 12)
    (lo := (77784557 / 200000000)) (hi := (194461393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3777 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3777 / 2560) = 1/(2560 / 3777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (77784557 / 200000000) (194461393 / 500000000) (Real.log (3777 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3777 / 2560) = -Real.log (2560 / 3777) := by
    rw [show ((3777 / 2560) : ℝ) = ((2560 / 3777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32255067 / 50000000) ≤ -Real.log (1343 / 2560) ∧
    -Real.log (1343 / 2560) ≤ (645101341 / 1000000000) := by
  have h := checkLog_sound (w := (1217 / 3903)) (n := 12)
    (lo := (32255067 / 50000000)) (hi := (645101341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1343) = 1/(1343 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-645101341 / 1000000000) (-32255067 / 50000000) (Real.log (1343 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (669430653 / 1000000000) (334715327 / 500000000) (Real.log (125 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (125 / 64) = -Real.log (64 / 125) := by
    rw [show ((125 / 64) : ℝ) = ((64 / 125) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (382533849 / 125000000) ≤ -Real.log (3 / 64) ∧
    -Real.log (3 / 64) ≤ (3060270797 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4 / 3) = 1/(3 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3060270797 / 1000000000) (-382533849 / 125000000) (Real.log (3 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (668229933 / 1000000000) ≤ -Real.log (1280 / 2497) ∧
    -Real.log (1280 / 2497) ≤ (334114967 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 3777)) (n := 12)
    (lo := (668229933 / 1000000000)) (hi := (334114967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1280) = 1/(1280 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (668229933 / 1000000000) (334114967 / 500000000) (Real.log (2497 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2497 / 1280) = -Real.log (1280 / 2497) := by
    rw [show ((2497 / 1280) : ℝ) = ((1280 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (752870157 / 250000000) ≤ -Real.log (63 / 1280) ∧
    -Real.log (63 / 1280) ≤ (3011480633 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 63) = 1/(63 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3011480633 / 1000000000) (-752870157 / 250000000) (Real.log (63 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (271371113 / 500000000) ≤ -Real.log (1000000 / 1720719) ∧
    -Real.log (1000000 / 1720719) ≤ (542742227 / 1000000000) := by
  have h := checkLog_sound (w := (720719 / 2720719)) (n := 12)
    (lo := (271371113 / 500000000)) (hi := (542742227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1720719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1720719 / 1000000) = 1/(1000000 / 1720719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (271371113 / 500000000) (542742227 / 1000000000) (Real.log (1720719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1720719 / 1000000) = -Real.log (1000000 / 1720719) := by
    rw [show ((1720719 / 1000000) : ℝ) = ((1000000 / 1720719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (637768417 / 500000000) ≤ -Real.log (279281 / 1000000) ∧
    -Real.log (279281 / 1000000) ≤ (318884209 / 250000000) := by
  have h := checkLog_sound (w := (220719 / 779281)) (n := 12)
    (lo := (291194827 / 500000000)) (hi := (116477931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 279281) = 1/(279281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-318884209 / 250000000) (-637768417 / 500000000) (Real.log (279281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (272062787 / 500000000) ≤ -Real.log (1000000 / 1723101) ∧
    -Real.log (1000000 / 1723101) ≤ (21765023 / 40000000) := by
  have h := checkLog_sound (w := (723101 / 2723101)) (n := 12)
    (lo := (272062787 / 500000000)) (hi := (21765023 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723101 / 1000000) = 1/(1000000 / 1723101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (272062787 / 500000000) (21765023 / 40000000) (Real.log (1723101 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1723101 / 1000000) = -Real.log (1000000 / 1723101) := by
    rw [show ((1723101 / 1000000) : ℝ) = ((1000000 / 1723101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1284102459 / 1000000000) ≤ -Real.log (276899 / 1000000) ∧
    -Real.log (276899 / 1000000) ≤ (1284102461 / 1000000000) := by
  have h := checkLog_sound (w := (223101 / 776899)) (n := 12)
    (lo := (590955279 / 1000000000)) (hi := (7386941 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276899) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 276899) = 1/(276899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1284102461 / 1000000000) (-1284102459 / 1000000000) (Real.log (276899 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (465979919 / 1000000000) ≤ -Real.log (40000 / 63743) ∧
    -Real.log (40000 / 63743) ≤ (5824749 / 12500000) := by
  have h := checkLog_sound (w := (23743 / 103743)) (n := 12)
    (lo := (465979919 / 1000000000)) (hi := (5824749 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63743 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63743 / 40000) = 1/(40000 / 63743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (465979919 / 1000000000) (5824749 / 12500000) (Real.log (63743 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63743 / 40000) = -Real.log (40000 / 63743) := by
    rw [show ((63743 / 40000) : ℝ) = ((40000 / 63743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (225088967 / 250000000) ≤ -Real.log (16257 / 40000) ∧
    -Real.log (16257 / 40000) ≤ (90035587 / 100000000) := by
  have h := checkLog_sound (w := (3743 / 36257)) (n := 12)
    (lo := (12950543 / 62500000)) (hi := (207208689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 16257) = 1/(16257 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90035587 / 100000000) (-225088967 / 250000000) (Real.log (16257 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (233799119 / 500000000) ≤ -Real.log (250000 / 399039) ∧
    -Real.log (250000 / 399039) ≤ (467598239 / 1000000000) := by
  have h := checkLog_sound (w := (149039 / 649039)) (n := 12)
    (lo := (233799119 / 500000000)) (hi := (467598239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399039 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399039 / 250000) = 1/(250000 / 399039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (233799119 / 500000000) (467598239 / 1000000000) (Real.log (399039 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399039 / 250000) = -Real.log (250000 / 399039) := by
    rw [show ((399039 / 250000) : ℝ) = ((250000 / 399039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (906726613 / 1000000000) ≤ -Real.log (100961 / 250000) ∧
    -Real.log (100961 / 250000) ≤ (181345323 / 200000000) := by
  have h := checkLog_sound (w := (24039 / 225961)) (n := 12)
    (lo := (213579433 / 1000000000)) (hi := (106789717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100961) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 100961) = 1/(100961 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-181345323 / 200000000) (-906726613 / 1000000000) (Real.log (100961 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1818279061 / 1000000000) ≤ -Real.log (500000000000 / 3080623100031) ∧
    -Real.log (500000000000 / 3080623100031) ≤ (227284883 / 125000000) := by
  have h := checkLog_sound (w := (1080623100031 / 5080623100031)) (n := 12)
    (lo := (431984701 / 1000000000)) (hi := (215992351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3080623100031 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3080623100031 / 2000000000000) = 1/(500000000000 / 3080623100031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1818279061 / 1000000000) (227284883 / 125000000) (Real.log (3080623100031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3080623100031 / 500000000000) = -Real.log (500000000000 / 3080623100031) := by
    rw [show ((3080623100031 / 500000000000) : ℝ) = ((500000000000 / 3080623100031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1828228033 / 1000000000) ≤ -Real.log (500000000000 / 3111425104461) ∧
    -Real.log (500000000000 / 3111425104461) ≤ (457057009 / 250000000) := by
  have h := checkLog_sound (w := (1111425104461 / 5111425104461)) (n := 12)
    (lo := (441933673 / 1000000000)) (hi := (220966837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111425104461 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3111425104461 / 2000000000000) = 1/(500000000000 / 3111425104461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1828228033 / 1000000000) (457057009 / 250000000) (Real.log (3111425104461 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3111425104461 / 500000000000) = -Real.log (500000000000 / 3111425104461) := by
    rw [show ((3111425104461 / 500000000000) : ℝ) = ((500000000000 / 3111425104461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (341583947 / 250000000) ≤ -Real.log (12500000000 / 49011964077) ∧
    -Real.log (12500000000 / 49011964077) ≤ (136633579 / 100000000) := by
  have h := checkLog_sound (w := (24011964077 / 74011964077)) (n := 12)
    (lo := (2629643 / 3906250)) (hi := (673188609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49011964077 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(49011964077 / 25000000000) = 1/(12500000000 / 49011964077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (341583947 / 250000000) (136633579 / 100000000) (Real.log (49011964077 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49011964077 / 12500000000) = -Real.log (12500000000 / 49011964077) := by
    rw [show ((49011964077 / 12500000000) : ℝ) = ((12500000000 / 49011964077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (343581213 / 250000000) ≤ -Real.log (500000000000 / 1976203682611) ∧
    -Real.log (500000000000 / 1976203682611) ≤ (687162427 / 500000000) := by
  have h := checkLog_sound (w := (976203682611 / 2976203682611)) (n := 12)
    (lo := (85147209 / 125000000)) (hi := (681177673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976203682611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1976203682611 / 1000000000000) = 1/(500000000000 / 1976203682611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (343581213 / 250000000) (687162427 / 500000000) (Real.log (1976203682611 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1976203682611 / 500000000000) = -Real.log (500000000000 / 1976203682611) := by
    rw [show ((1976203682611 / 500000000000) : ℝ) = ((500000000000 / 1976203682611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0031
