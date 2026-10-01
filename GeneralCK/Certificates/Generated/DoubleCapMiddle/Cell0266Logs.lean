import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0266
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

theorem reflection_log_1_neg : (235566071 / 1000000000) ≤ -Real.log (64 / 81) ∧
    -Real.log (64 / 81) ≤ (29445759 / 125000000) := by
  have h := checkLog_sound (w := (17 / 145)) (n := 12)
    (lo := (235566071 / 1000000000)) (hi := (29445759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 64) = 1/(64 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235566071 / 1000000000) (29445759 / 125000000) (Real.log (81 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (81 / 64) = -Real.log (64 / 81) := by
    rw [show ((81 / 64) : ℝ) = ((64 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (308735481 / 1000000000) ≤ -Real.log (47 / 64) ∧
    -Real.log (47 / 64) ≤ (154367741 / 500000000) := by
  have h := checkLog_sound (w := (17 / 111)) (n := 12)
    (lo := (308735481 / 1000000000)) (hi := (154367741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 47) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 47) = 1/(47 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-154367741 / 500000000) (-308735481 / 1000000000) (Real.log (47 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235103001 / 1000000000) ≤ -Real.log (5120 / 6477) ∧
    -Real.log (5120 / 6477) ≤ (117551501 / 500000000) := by
  have h := checkLog_sound (w := (1357 / 11597)) (n := 12)
    (lo := (235103001 / 1000000000)) (hi := (117551501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6477 / 5120) = 1/(5120 / 6477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235103001 / 1000000000) (117551501 / 500000000) (Real.log (6477 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6477 / 5120) = -Real.log (5120 / 6477) := by
    rw [show ((6477 / 5120) : ℝ) = ((5120 / 6477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307937927 / 1000000000) ≤ -Real.log (3763 / 5120) ∧
    -Real.log (3763 / 5120) ≤ (38492241 / 125000000) := by
  have h := checkLog_sound (w := (1357 / 8883)) (n := 12)
    (lo := (307937927 / 1000000000)) (hi := (38492241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3763) = 1/(3763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-38492241 / 125000000) (-307937927 / 1000000000) (Real.log (3763 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85216879 / 200000000) ≤ -Real.log (32 / 49) ∧
    -Real.log (32 / 49) ≤ (106521099 / 250000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 32) = 1/(32 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85216879 / 200000000) (106521099 / 250000000) (Real.log (49 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49 / 32) = -Real.log (32 / 49) := by
    rw [show ((49 / 32) : ℝ) = ((32 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (757685701 / 1000000000) ≤ -Real.log (15 / 32) ∧
    -Real.log (15 / 32) ≤ (757685703 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 15) = 1/(15 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-757685703 / 1000000000) (-757685701 / 1000000000) (Real.log (15 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106329699 / 250000000) ≤ -Real.log (2560 / 3917) ∧
    -Real.log (2560 / 3917) ≤ (425318797 / 1000000000) := by
  have h := checkLog_sound (w := (1357 / 6477)) (n := 12)
    (lo := (106329699 / 250000000)) (hi := (425318797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3917 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3917 / 2560) = 1/(2560 / 3917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106329699 / 250000000) (425318797 / 1000000000) (Real.log (3917 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3917 / 2560) = -Real.log (2560 / 3917) := by
    rw [show ((3917 / 2560) : ℝ) = ((2560 / 3917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (37759441 / 50000000) ≤ -Real.log (1203 / 2560) ∧
    -Real.log (1203 / 2560) ≤ (377594411 / 500000000) := by
  have h := checkLog_sound (w := (77 / 2483)) (n := 12)
    (lo := (1551041 / 25000000)) (hi := (62041641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1203) = 1/(1203 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-377594411 / 500000000) (-37759441 / 50000000) (Real.log (1203 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40243679 / 125000000) ≤ -Real.log (200000 / 275963) ∧
    -Real.log (200000 / 275963) ≤ (321949433 / 1000000000) := by
  have h := checkLog_sound (w := (75963 / 475963)) (n := 12)
    (lo := (40243679 / 125000000)) (hi := (321949433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275963 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275963 / 200000) = 1/(200000 / 275963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40243679 / 125000000) (321949433 / 1000000000) (Real.log (275963 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (275963 / 200000) = -Real.log (200000 / 275963) := by
    rw [show ((275963 / 200000) : ℝ) = ((200000 / 275963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (238868729 / 500000000) ≤ -Real.log (124037 / 200000) ∧
    -Real.log (124037 / 200000) ≤ (477737459 / 1000000000) := by
  have h := checkLog_sound (w := (75963 / 324037)) (n := 12)
    (lo := (238868729 / 500000000)) (hi := (477737459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 124037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 124037) = 1/(124037 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-477737459 / 1000000000) (-238868729 / 500000000) (Real.log (124037 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64515371 / 200000000) ≤ -Real.log (1000000 / 1380681) ∧
    -Real.log (1000000 / 1380681) ≤ (40322107 / 125000000) := by
  have h := checkLog_sound (w := (380681 / 2380681)) (n := 12)
    (lo := (64515371 / 200000000)) (hi := (40322107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1380681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1380681 / 1000000) = 1/(1000000 / 1380681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64515371 / 200000000) (40322107 / 125000000) (Real.log (1380681 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1380681 / 1000000) = -Real.log (1000000 / 1380681) := by
    rw [show ((1380681 / 1000000) : ℝ) = ((1000000 / 1380681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (479134791 / 1000000000) ≤ -Real.log (619319 / 1000000) ∧
    -Real.log (619319 / 1000000) ≤ (59891849 / 125000000) := by
  have h := checkLog_sound (w := (380681 / 1619319)) (n := 12)
    (lo := (479134791 / 1000000000)) (hi := (59891849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 619319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 619319) = 1/(619319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59891849 / 125000000) (-479134791 / 1000000000) (Real.log (619319 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123324559 / 500000000) ≤ -Real.log (100000 / 127973) ∧
    -Real.log (100000 / 127973) ≤ (246649119 / 1000000000) := by
  have h := checkLog_sound (w := (27973 / 227973)) (n := 12)
    (lo := (123324559 / 500000000)) (hi := (246649119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127973 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127973 / 100000) = 1/(100000 / 127973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123324559 / 500000000) (246649119 / 1000000000) (Real.log (127973 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (127973 / 100000) = -Real.log (100000 / 127973) := by
    rw [show ((127973 / 100000) : ℝ) = ((100000 / 127973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (328129137 / 1000000000) ≤ -Real.log (72027 / 100000) ∧
    -Real.log (72027 / 100000) ≤ (164064569 / 500000000) := by
  have h := checkLog_sound (w := (27973 / 172027)) (n := 12)
    (lo := (328129137 / 1000000000)) (hi := (164064569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72027) = 1/(72027 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-164064569 / 500000000) (-328129137 / 1000000000) (Real.log (72027 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24718893 / 100000000) ≤ -Real.log (1000000 / 1280421) ∧
    -Real.log (1000000 / 1280421) ≤ (247188931 / 1000000000) := by
  have h := checkLog_sound (w := (280421 / 2280421)) (n := 12)
    (lo := (24718893 / 100000000)) (hi := (247188931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280421 / 1000000) = 1/(1000000 / 1280421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24718893 / 100000000) (247188931 / 1000000000) (Real.log (1280421 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1280421 / 1000000) = -Real.log (1000000 / 1280421) := by
    rw [show ((1280421 / 1000000) : ℝ) = ((1000000 / 1280421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1028403 / 3125000) ≤ -Real.log (719579 / 1000000) ∧
    -Real.log (719579 / 1000000) ≤ (329088961 / 1000000000) := by
  have h := checkLog_sound (w := (280421 / 1719579)) (n := 12)
    (lo := (1028403 / 3125000)) (hi := (329088961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719579) = 1/(719579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-329088961 / 1000000000) (-1028403 / 3125000) (Real.log (719579 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (79968689 / 100000000) ≤ -Real.log (500000000000 / 1112422099857) ∧
    -Real.log (500000000000 / 1112422099857) ≤ (199921723 / 250000000) := by
  have h := checkLog_sound (w := (112422099857 / 2112422099857)) (n := 12)
    (lo := (10653971 / 100000000)) (hi := (106539711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112422099857 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112422099857 / 1000000000000) = 1/(500000000000 / 1112422099857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79968689 / 100000000) (199921723 / 250000000) (Real.log (1112422099857 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1112422099857 / 500000000000) = -Real.log (500000000000 / 1112422099857) := by
    rw [show ((1112422099857 / 500000000000) : ℝ) = ((500000000000 / 1112422099857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (400855823 / 500000000) ≤ -Real.log (125000000000 / 278669191483) ∧
    -Real.log (125000000000 / 278669191483) ≤ (25053489 / 31250000) := by
  have h := checkLog_sound (w := (28669191483 / 528669191483)) (n := 12)
    (lo := (54282233 / 500000000)) (hi := (108564467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278669191483 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(278669191483 / 250000000000) = 1/(125000000000 / 278669191483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (400855823 / 500000000) (25053489 / 31250000) (Real.log (278669191483 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (278669191483 / 125000000000) = -Real.log (125000000000 / 278669191483) := by
    rw [show ((278669191483 / 125000000000) : ℝ) = ((125000000000 / 278669191483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (114955651 / 200000000) ≤ -Real.log (250000000000 / 444184125397) ∧
    -Real.log (250000000000 / 444184125397) ≤ (35923641 / 62500000) := by
  have h := checkLog_sound (w := (194184125397 / 694184125397)) (n := 12)
    (lo := (114955651 / 200000000)) (hi := (35923641 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444184125397 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444184125397 / 250000000000) = 1/(250000000000 / 444184125397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (114955651 / 200000000) (35923641 / 62500000) (Real.log (444184125397 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (444184125397 / 250000000000) = -Real.log (250000000000 / 444184125397) := by
    rw [show ((444184125397 / 250000000000) : ℝ) = ((250000000000 / 444184125397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (57627789 / 100000000) ≤ -Real.log (250000000000 / 444850739113) ∧
    -Real.log (250000000000 / 444850739113) ≤ (576277891 / 1000000000) := by
  have h := checkLog_sound (w := (194850739113 / 694850739113)) (n := 12)
    (lo := (57627789 / 100000000)) (hi := (576277891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444850739113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444850739113 / 250000000000) = 1/(250000000000 / 444850739113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (57627789 / 100000000) (576277891 / 1000000000) (Real.log (444850739113 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (444850739113 / 250000000000) = -Real.log (250000000000 / 444850739113) := by
    rw [show ((444850739113 / 250000000000) : ℝ) = ((250000000000 / 444850739113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0266
