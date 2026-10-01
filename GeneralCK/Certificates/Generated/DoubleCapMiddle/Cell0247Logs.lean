import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0247
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

theorem reflection_log_1_neg : (48864781 / 200000000) ≤ -Real.log (5120 / 6537) ∧
    -Real.log (5120 / 6537) ≤ (122161953 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 11657)) (n := 12)
    (lo := (48864781 / 200000000)) (hi := (122161953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6537 / 5120) = 1/(5120 / 6537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48864781 / 200000000) (122161953 / 500000000) (Real.log (6537 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6537 / 5120) = -Real.log (5120 / 6537) := by
    rw [show ((6537 / 5120) : ℝ) = ((5120 / 6537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (324011137 / 1000000000) ≤ -Real.log (3703 / 5120) ∧
    -Real.log (3703 / 5120) ≤ (162005569 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 8823)) (n := 12)
    (lo := (324011137 / 1000000000)) (hi := (162005569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3703) = 1/(3703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-162005569 / 500000000) (-324011137 / 1000000000) (Real.log (3703 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121932437 / 500000000) ≤ -Real.log (2560 / 3267) ∧
    -Real.log (2560 / 3267) ≤ (1950919 / 8000000) := by
  have h := checkLog_sound (w := (707 / 5827)) (n := 12)
    (lo := (121932437 / 500000000)) (hi := (1950919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3267 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3267 / 2560) = 1/(2560 / 3267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121932437 / 500000000) (1950919 / 8000000) (Real.log (3267 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3267 / 2560) = -Real.log (2560 / 3267) := by
    rw [show ((3267 / 2560) : ℝ) = ((2560 / 3267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (323201311 / 1000000000) ≤ -Real.log (1853 / 2560) ∧
    -Real.log (1853 / 2560) ≤ (10100041 / 31250000) := by
  have h := checkLog_sound (w := (707 / 4413)) (n := 12)
    (lo := (323201311 / 1000000000)) (hi := (10100041 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1853) = 1/(1853 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10100041 / 31250000) (-323201311 / 1000000000) (Real.log (1853 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (440520507 / 1000000000) ≤ -Real.log (2560 / 3977) ∧
    -Real.log (2560 / 3977) ≤ (110130127 / 250000000) := by
  have h := checkLog_sound (w := (1417 / 6537)) (n := 12)
    (lo := (440520507 / 1000000000)) (hi := (110130127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3977 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3977 / 2560) = 1/(2560 / 3977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (440520507 / 1000000000) (110130127 / 250000000) (Real.log (3977 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3977 / 2560) = -Real.log (2560 / 3977) := by
    rw [show ((3977 / 2560) : ℝ) = ((2560 / 3977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (806350873 / 1000000000) ≤ -Real.log (1143 / 2560) ∧
    -Real.log (1143 / 2560) ≤ (6450807 / 8000000) := by
  have h := checkLog_sound (w := (137 / 2423)) (n := 12)
    (lo := (113203693 / 1000000000)) (hi := (56601847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1143) = 1/(1143 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6450807 / 8000000) (-806350873 / 1000000000) (Real.log (1143 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87953177 / 200000000) ≤ -Real.log (1280 / 1987) ∧
    -Real.log (1280 / 1987) ≤ (219882943 / 500000000) := by
  have h := checkLog_sound (w := (707 / 3267)) (n := 12)
    (lo := (87953177 / 200000000)) (hi := (219882943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1280) = 1/(1280 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (87953177 / 200000000) (219882943 / 500000000) (Real.log (1987 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1987 / 1280) = -Real.log (1280 / 1987) := by
    rw [show ((1987 / 1280) : ℝ) = ((1280 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (803729639 / 1000000000) ≤ -Real.log (573 / 1280) ∧
    -Real.log (573 / 1280) ≤ (803729641 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 573) = 1/(573 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-803729641 / 1000000000) (-803729639 / 1000000000) (Real.log (573 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33381657 / 100000000) ≤ -Real.log (1000000 / 1396287) ∧
    -Real.log (1000000 / 1396287) ≤ (333816571 / 1000000000) := by
  have h := checkLog_sound (w := (396287 / 2396287)) (n := 12)
    (lo := (33381657 / 100000000)) (hi := (333816571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1396287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1396287 / 1000000) = 1/(1000000 / 1396287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33381657 / 100000000) (333816571 / 1000000000) (Real.log (1396287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1396287 / 1000000) = -Real.log (1000000 / 1396287) := by
    rw [show ((1396287 / 1000000) : ℝ) = ((1000000 / 1396287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (504656359 / 1000000000) ≤ -Real.log (603713 / 1000000) ∧
    -Real.log (603713 / 1000000) ≤ (12616409 / 25000000) := by
  have h := checkLog_sound (w := (396287 / 1603713)) (n := 12)
    (lo := (504656359 / 1000000000)) (hi := (12616409 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 603713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 603713) = 1/(603713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12616409 / 25000000) (-504656359 / 1000000000) (Real.log (603713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334439457 / 1000000000) ≤ -Real.log (1000000 / 1397157) ∧
    -Real.log (1000000 / 1397157) ≤ (167219729 / 500000000) := by
  have h := checkLog_sound (w := (397157 / 2397157)) (n := 12)
    (lo := (334439457 / 1000000000)) (hi := (167219729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397157 / 1000000) = 1/(1000000 / 1397157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334439457 / 1000000000) (167219729 / 500000000) (Real.log (1397157 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1397157 / 1000000) = -Real.log (1000000 / 1397157) := by
    rw [show ((1397157 / 1000000) : ℝ) = ((1000000 / 1397157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6326231 / 12500000) ≤ -Real.log (602843 / 1000000) ∧
    -Real.log (602843 / 1000000) ≤ (506098481 / 1000000000) := by
  have h := checkLog_sound (w := (397157 / 1602843)) (n := 12)
    (lo := (6326231 / 12500000)) (hi := (506098481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602843) = 1/(602843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-506098481 / 1000000000) (-6326231 / 12500000) (Real.log (602843 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256915601 / 1000000000) ≤ -Real.log (125000 / 161617) ∧
    -Real.log (125000 / 161617) ≤ (128457801 / 500000000) := by
  have h := checkLog_sound (w := (36617 / 286617)) (n := 12)
    (lo := (256915601 / 1000000000)) (hi := (128457801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161617 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161617 / 125000) = 1/(125000 / 161617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256915601 / 1000000000) (128457801 / 500000000) (Real.log (161617 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161617 / 125000) = -Real.log (125000 / 161617) := by
    rw [show ((161617 / 125000) : ℝ) = ((125000 / 161617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (346634093 / 1000000000) ≤ -Real.log (88383 / 125000) ∧
    -Real.log (88383 / 125000) ≤ (173317047 / 500000000) := by
  have h := checkLog_sound (w := (36617 / 213383)) (n := 12)
    (lo := (346634093 / 1000000000)) (hi := (173317047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88383) = 1/(88383 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-173317047 / 500000000) (-346634093 / 1000000000) (Real.log (88383 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (64364601 / 250000000) ≤ -Real.log (500000 / 646819) ∧
    -Real.log (500000 / 646819) ≤ (51491681 / 200000000) := by
  have h := checkLog_sound (w := (146819 / 1146819)) (n := 12)
    (lo := (64364601 / 250000000)) (hi := (51491681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646819 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646819 / 500000) = 1/(500000 / 646819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64364601 / 250000000) (51491681 / 200000000) (Real.log (646819 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (646819 / 500000) = -Real.log (500000 / 646819) := by
    rw [show ((646819 / 500000) : ℝ) = ((500000 / 646819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (13905097 / 40000000) ≤ -Real.log (353181 / 500000) ∧
    -Real.log (353181 / 500000) ≤ (173813713 / 500000000) := by
  have h := checkLog_sound (w := (146819 / 853181)) (n := 12)
    (lo := (13905097 / 40000000)) (hi := (173813713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 353181) = 1/(353181 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-173813713 / 500000000) (-13905097 / 40000000) (Real.log (353181 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (838472929 / 1000000000) ≤ -Real.log (250000000000 / 578208105507) ∧
    -Real.log (250000000000 / 578208105507) ≤ (838472931 / 1000000000) := by
  have h := checkLog_sound (w := (78208105507 / 1078208105507)) (n := 12)
    (lo := (145325749 / 1000000000)) (hi := (581303 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578208105507 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578208105507 / 500000000000) = 1/(250000000000 / 578208105507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (838472929 / 1000000000) (838472931 / 1000000000) (Real.log (578208105507 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (578208105507 / 250000000000) = -Real.log (250000000000 / 578208105507) := by
    rw [show ((578208105507 / 250000000000) : ℝ) = ((250000000000 / 578208105507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (420268969 / 500000000) ≤ -Real.log (250000000000 / 579403343823) ∧
    -Real.log (250000000000 / 579403343823) ≤ (42026897 / 50000000) := by
  have h := checkLog_sound (w := (79403343823 / 1079403343823)) (n := 12)
    (lo := (73695379 / 500000000)) (hi := (147390759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579403343823 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(579403343823 / 500000000000) = 1/(250000000000 / 579403343823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (420268969 / 500000000) (42026897 / 50000000) (Real.log (579403343823 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (579403343823 / 250000000000) = -Real.log (250000000000 / 579403343823) := by
    rw [show ((579403343823 / 250000000000) : ℝ) = ((250000000000 / 579403343823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (120709939 / 200000000) ≤ -Real.log (500000000000 / 914299129923) ∧
    -Real.log (500000000000 / 914299129923) ≤ (1178808 / 1953125) := by
  have h := checkLog_sound (w := (414299129923 / 1414299129923)) (n := 12)
    (lo := (120709939 / 200000000)) (hi := (1178808 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914299129923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914299129923 / 500000000000) = 1/(500000000000 / 914299129923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (120709939 / 200000000) (1178808 / 1953125) (Real.log (914299129923 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (914299129923 / 500000000000) = -Real.log (500000000000 / 914299129923) := by
    rw [show ((914299129923 / 500000000000) : ℝ) = ((500000000000 / 914299129923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (605085829 / 1000000000) ≤ -Real.log (500000000000 / 915704695327) ∧
    -Real.log (500000000000 / 915704695327) ≤ (60508583 / 100000000) := by
  have h := checkLog_sound (w := (415704695327 / 1415704695327)) (n := 12)
    (lo := (605085829 / 1000000000)) (hi := (60508583 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915704695327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915704695327 / 500000000000) = 1/(500000000000 / 915704695327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (605085829 / 1000000000) (60508583 / 100000000) (Real.log (915704695327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (915704695327 / 500000000000) = -Real.log (500000000000 / 915704695327) := by
    rw [show ((915704695327 / 500000000000) : ℝ) = ((500000000000 / 915704695327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0247
