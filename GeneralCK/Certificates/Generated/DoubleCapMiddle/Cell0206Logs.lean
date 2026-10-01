import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0206
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

theorem reflection_log_1_neg : (52593009 / 200000000) ≤ -Real.log (256 / 333) ∧
    -Real.log (256 / 333) ≤ (131482523 / 500000000) := by
  have h := checkLog_sound (w := (77 / 589)) (n := 12)
    (lo := (52593009 / 200000000)) (hi := (131482523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 256) = 1/(256 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52593009 / 200000000) (131482523 / 500000000) (Real.log (333 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (333 / 256) = -Real.log (256 / 333) := by
    rw [show ((333 / 256) : ℝ) = ((256 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (178895819 / 500000000) ≤ -Real.log (179 / 256) ∧
    -Real.log (179 / 256) ≤ (357791639 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 435)) (n := 12)
    (lo := (178895819 / 500000000)) (hi := (357791639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 179) = 1/(179 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-357791639 / 1000000000) (-178895819 / 500000000) (Real.log (179 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (262514493 / 1000000000) ≤ -Real.log (5120 / 6657) ∧
    -Real.log (5120 / 6657) ≤ (131257247 / 500000000) := by
  have h := checkLog_sound (w := (1537 / 11777)) (n := 12)
    (lo := (262514493 / 1000000000)) (hi := (131257247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6657 / 5120) = 1/(5120 / 6657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (262514493 / 1000000000) (131257247 / 500000000) (Real.log (6657 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6657 / 5120) = -Real.log (5120 / 6657) := by
    rw [show ((6657 / 5120) : ℝ) = ((5120 / 6657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (178477 / 500000) ≤ -Real.log (3583 / 5120) ∧
    -Real.log (3583 / 5120) ≤ (356954001 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 8703)) (n := 12)
    (lo := (178477 / 500000)) (hi := (356954001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3583) = 1/(3583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-356954001 / 1000000000) (-178477 / 500000) (Real.log (3583 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94195943 / 200000000) ≤ -Real.log (128 / 205) ∧
    -Real.log (128 / 205) ≤ (117744929 / 250000000) := by
  have h := checkLog_sound (w := (77 / 333)) (n := 12)
    (lo := (94195943 / 200000000)) (hi := (117744929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205 / 128) = 1/(128 / 205) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94195943 / 200000000) (117744929 / 250000000) (Real.log (205 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (205 / 128) = -Real.log (128 / 205) := by
    rw [show ((205 / 128) : ℝ) = ((128 / 205) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (92020463 / 100000000) ≤ -Real.log (51 / 128) ∧
    -Real.log (51 / 128) ≤ (115025579 / 125000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 51) = 1/(51 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115025579 / 125000000) (-92020463 / 100000000) (Real.log (51 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23512387 / 50000000) ≤ -Real.log (2560 / 4097) ∧
    -Real.log (2560 / 4097) ≤ (470247741 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 6657)) (n := 12)
    (lo := (23512387 / 50000000)) (hi := (470247741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4097 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4097 / 2560) = 1/(2560 / 4097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23512387 / 50000000) (470247741 / 1000000000) (Real.log (4097 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4097 / 2560) = -Real.log (2560 / 4097) := by
    rw [show ((4097 / 2560) : ℝ) = ((2560 / 4097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (91726777 / 100000000) ≤ -Real.log (1023 / 2560) ∧
    -Real.log (1023 / 2560) ≤ (229316943 / 250000000) := by
  have h := checkLog_sound (w := (257 / 2303)) (n := 12)
    (lo := (22412059 / 100000000)) (hi := (224120591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1023) = 1/(1023 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-229316943 / 250000000) (-91726777 / 100000000) (Real.log (1023 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (359150277 / 1000000000) ≤ -Real.log (62500 / 89507) ∧
    -Real.log (62500 / 89507) ≤ (179575139 / 500000000) := by
  have h := checkLog_sound (w := (27007 / 152007)) (n := 12)
    (lo := (359150277 / 1000000000)) (hi := (179575139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89507 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89507 / 62500) = 1/(62500 / 89507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (359150277 / 1000000000) (179575139 / 500000000) (Real.log (89507 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (89507 / 62500) = -Real.log (62500 / 89507) := by
    rw [show ((89507 / 62500) : ℝ) = ((62500 / 89507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (282915531 / 500000000) ≤ -Real.log (35493 / 62500) ∧
    -Real.log (35493 / 62500) ≤ (565831063 / 1000000000) := by
  have h := checkLog_sound (w := (27007 / 97993)) (n := 12)
    (lo := (282915531 / 500000000)) (hi := (565831063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35493) = 1/(35493 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-565831063 / 1000000000) (-282915531 / 500000000) (Real.log (35493 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (359765263 / 1000000000) ≤ -Real.log (1000000 / 1432993) ∧
    -Real.log (1000000 / 1432993) ≤ (22485329 / 62500000) := by
  have h := checkLog_sound (w := (432993 / 2432993)) (n := 12)
    (lo := (359765263 / 1000000000)) (hi := (22485329 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432993 / 1000000) = 1/(1000000 / 1432993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (359765263 / 1000000000) (22485329 / 62500000) (Real.log (1432993 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1432993 / 1000000) = -Real.log (1000000 / 1432993) := by
    rw [show ((1432993 / 1000000) : ℝ) = ((1000000 / 1432993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (567383629 / 1000000000) ≤ -Real.log (567007 / 1000000) ∧
    -Real.log (567007 / 1000000) ≤ (56738363 / 100000000) := by
  have h := checkLog_sound (w := (432993 / 1567007)) (n := 12)
    (lo := (567383629 / 1000000000)) (hi := (56738363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567007) = 1/(567007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-56738363 / 100000000) (-567383629 / 1000000000) (Real.log (567007 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (279273569 / 1000000000) ≤ -Real.log (1000000 / 1322169) ∧
    -Real.log (1000000 / 1322169) ≤ (27927357 / 100000000) := by
  have h := checkLog_sound (w := (322169 / 2322169)) (n := 12)
    (lo := (279273569 / 1000000000)) (hi := (27927357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322169 / 1000000) = 1/(1000000 / 1322169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (279273569 / 1000000000) (27927357 / 100000000) (Real.log (1322169 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1322169 / 1000000) = -Real.log (1000000 / 1322169) := by
    rw [show ((1322169 / 1000000) : ℝ) = ((1000000 / 1322169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97214321 / 250000000) ≤ -Real.log (677831 / 1000000) ∧
    -Real.log (677831 / 1000000) ≤ (77771457 / 200000000) := by
  have h := checkLog_sound (w := (322169 / 1677831)) (n := 12)
    (lo := (97214321 / 250000000)) (hi := (77771457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677831) = 1/(677831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77771457 / 200000000) (-97214321 / 250000000) (Real.log (677831 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (69956007 / 250000000) ≤ -Real.log (1000000 / 1322897) ∧
    -Real.log (1000000 / 1322897) ≤ (279824029 / 1000000000) := by
  have h := checkLog_sound (w := (322897 / 2322897)) (n := 12)
    (lo := (69956007 / 250000000)) (hi := (279824029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322897 / 1000000) = 1/(1000000 / 1322897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69956007 / 250000000) (279824029 / 1000000000) (Real.log (1322897 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1322897 / 1000000) = -Real.log (1000000 / 1322897) := by
    rw [show ((1322897 / 1000000) : ℝ) = ((1000000 / 1322897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (623891 / 1600000) ≤ -Real.log (677103 / 1000000) ∧
    -Real.log (677103 / 1000000) ≤ (97482969 / 250000000) := by
  have h := checkLog_sound (w := (322897 / 1677103)) (n := 12)
    (lo := (623891 / 1600000)) (hi := (97482969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677103) = 1/(677103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-97482969 / 250000000) (-623891 / 1600000) (Real.log (677103 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (46249067 / 50000000) ≤ -Real.log (50000000000 / 126091060209) ∧
    -Real.log (50000000000 / 126091060209) ≤ (462490671 / 500000000) := by
  have h := checkLog_sound (w := (26091060209 / 226091060209)) (n := 12)
    (lo := (2897927 / 12500000)) (hi := (231834161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126091060209 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126091060209 / 100000000000) = 1/(50000000000 / 126091060209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (46249067 / 50000000) (462490671 / 500000000) (Real.log (126091060209 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126091060209 / 50000000000) = -Real.log (50000000000 / 126091060209) := by
    rw [show ((126091060209 / 50000000000) : ℝ) = ((50000000000 / 126091060209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (927148893 / 1000000000) ≤ -Real.log (12500000000 / 31591166423) ∧
    -Real.log (12500000000 / 31591166423) ≤ (185429779 / 200000000) := by
  have h := checkLog_sound (w := (6591166423 / 56591166423)) (n := 12)
    (lo := (234001713 / 1000000000)) (hi := (117000857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31591166423 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31591166423 / 25000000000) = 1/(12500000000 / 31591166423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (927148893 / 1000000000) (185429779 / 200000000) (Real.log (31591166423 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (31591166423 / 12500000000) = -Real.log (12500000000 / 31591166423) := by
    rw [show ((31591166423 / 12500000000) : ℝ) = ((12500000000 / 31591166423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (334065427 / 500000000) ≤ -Real.log (500000000000 / 975293989209) ∧
    -Real.log (500000000000 / 975293989209) ≤ (133626171 / 200000000) := by
  have h := checkLog_sound (w := (475293989209 / 1475293989209)) (n := 12)
    (lo := (334065427 / 500000000)) (hi := (133626171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975293989209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975293989209 / 500000000000) = 1/(500000000000 / 975293989209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (334065427 / 500000000) (133626171 / 200000000) (Real.log (975293989209 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (975293989209 / 500000000000) = -Real.log (500000000000 / 975293989209) := by
    rw [show ((975293989209 / 500000000000) : ℝ) = ((500000000000 / 975293989209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1308117 / 1953125) ≤ -Real.log (100000000000 / 195376035847) ∧
    -Real.log (100000000000 / 195376035847) ≤ (133951181 / 200000000) := by
  have h := checkLog_sound (w := (95376035847 / 295376035847)) (n := 12)
    (lo := (1308117 / 1953125)) (hi := (133951181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195376035847 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195376035847 / 100000000000) = 1/(100000000000 / 195376035847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1308117 / 1953125) (133951181 / 200000000) (Real.log (195376035847 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (195376035847 / 100000000000) = -Real.log (100000000000 / 195376035847) := by
    rw [show ((195376035847 / 100000000000) : ℝ) = ((100000000000 / 195376035847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0206
