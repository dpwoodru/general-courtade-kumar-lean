import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0295
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

theorem reflection_log_1_neg : (225094771 / 1000000000) ≤ -Real.log (2048 / 2565) ∧
    -Real.log (2048 / 2565) ≤ (56273693 / 250000000) := by
  have h := checkLog_sound (w := (517 / 4613)) (n := 12)
    (lo := (225094771 / 1000000000)) (hi := (56273693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2565 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2565 / 2048) = 1/(2048 / 2565) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225094771 / 1000000000) (56273693 / 250000000) (Real.log (2565 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2565 / 2048) = -Real.log (2048 / 2565) := by
    rw [show ((2565 / 2048) : ℝ) = ((2048 / 2565) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29094259 / 100000000) ≤ -Real.log (1531 / 2048) ∧
    -Real.log (1531 / 2048) ≤ (290942591 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 3579)) (n := 12)
    (lo := (29094259 / 100000000)) (hi := (290942591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1531) = 1/(1531 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290942591 / 1000000000) (-29094259 / 100000000) (Real.log (1531 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8994433 / 40000000) ≤ -Real.log (5120 / 6411) ∧
    -Real.log (5120 / 6411) ≤ (112430413 / 500000000) := by
  have h := checkLog_sound (w := (1291 / 11531)) (n := 12)
    (lo := (8994433 / 40000000)) (hi := (112430413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6411 / 5120) = 1/(5120 / 6411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8994433 / 40000000) (112430413 / 500000000) (Real.log (6411 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6411 / 5120) = -Real.log (5120 / 6411) := by
    rw [show ((6411 / 5120) : ℝ) = ((5120 / 6411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (145275383 / 500000000) ≤ -Real.log (3829 / 5120) ∧
    -Real.log (3829 / 5120) ≤ (290550767 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 8949)) (n := 12)
    (lo := (145275383 / 500000000)) (hi := (290550767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3829) = 1/(3829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-290550767 / 1000000000) (-145275383 / 500000000) (Real.log (3829 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (408715029 / 1000000000) ≤ -Real.log (1024 / 1541) ∧
    -Real.log (1024 / 1541) ≤ (40871503 / 100000000) := by
  have h := checkLog_sound (w := (517 / 2565)) (n := 12)
    (lo := (408715029 / 1000000000)) (hi := (40871503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1541 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1541 / 1024) = 1/(1024 / 1541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (408715029 / 1000000000) (40871503 / 100000000) (Real.log (1541 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1541 / 1024) = -Real.log (1024 / 1541) := by
    rw [show ((1541 / 1024) : ℝ) = ((1024 / 1541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (702960801 / 1000000000) ≤ -Real.log (507 / 1024) ∧
    -Real.log (507 / 1024) ≤ (702960803 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 1019)) (n := 12)
    (lo := (9813621 / 1000000000)) (hi := (4906811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 507) = 1/(507 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-702960803 / 1000000000) (-702960801 / 1000000000) (Real.log (507 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (102081399 / 250000000) ≤ -Real.log (2560 / 3851) ∧
    -Real.log (2560 / 3851) ≤ (408325597 / 1000000000) := by
  have h := checkLog_sound (w := (1291 / 6411)) (n := 12)
    (lo := (102081399 / 250000000)) (hi := (408325597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3851 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3851 / 2560) = 1/(2560 / 3851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (102081399 / 250000000) (408325597 / 1000000000) (Real.log (3851 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3851 / 2560) = -Real.log (2560 / 3851) := by
    rw [show ((3851 / 2560) : ℝ) = ((2560 / 3851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (701778069 / 1000000000) ≤ -Real.log (1269 / 2560) ∧
    -Real.log (1269 / 2560) ≤ (701778071 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 2549)) (n := 12)
    (lo := (8630889 / 1000000000)) (hi := (863089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1269) = 1/(1269 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-701778071 / 1000000000) (-701778069 / 1000000000) (Real.log (1269 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (77024253 / 250000000) ≤ -Real.log (1000000 / 1360833) ∧
    -Real.log (1000000 / 1360833) ≤ (308097013 / 1000000000) := by
  have h := checkLog_sound (w := (360833 / 2360833)) (n := 12)
    (lo := (77024253 / 250000000)) (hi := (308097013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360833 / 1000000) = 1/(1000000 / 1360833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (77024253 / 250000000) (308097013 / 1000000000) (Real.log (1360833 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1360833 / 1000000) = -Real.log (1000000 / 1360833) := by
    rw [show ((1360833 / 1000000) : ℝ) = ((1000000 / 1360833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (55948689 / 125000000) ≤ -Real.log (639167 / 1000000) ∧
    -Real.log (639167 / 1000000) ≤ (447589513 / 1000000000) := by
  have h := checkLog_sound (w := (360833 / 1639167)) (n := 12)
    (lo := (55948689 / 125000000)) (hi := (447589513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639167) = 1/(639167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-447589513 / 1000000000) (-55948689 / 125000000) (Real.log (639167 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154207207 / 500000000) ≤ -Real.log (200000 / 272253) ∧
    -Real.log (200000 / 272253) ≤ (61682883 / 200000000) := by
  have h := checkLog_sound (w := (72253 / 472253)) (n := 12)
    (lo := (154207207 / 500000000)) (hi := (61682883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272253 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272253 / 200000) = 1/(200000 / 272253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154207207 / 500000000) (61682883 / 200000000) (Real.log (272253 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (272253 / 200000) = -Real.log (200000 / 272253) := by
    rw [show ((272253 / 200000) : ℝ) = ((200000 / 272253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (448265621 / 1000000000) ≤ -Real.log (127747 / 200000) ∧
    -Real.log (127747 / 200000) ≤ (224132811 / 500000000) := by
  have h := checkLog_sound (w := (72253 / 327747)) (n := 12)
    (lo := (448265621 / 1000000000)) (hi := (224132811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127747) = 1/(127747 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224132811 / 500000000) (-448265621 / 1000000000) (Real.log (127747 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58704979 / 250000000) ≤ -Real.log (1000000 / 1264681) ∧
    -Real.log (1000000 / 1264681) ≤ (234819917 / 1000000000) := by
  have h := checkLog_sound (w := (264681 / 2264681)) (n := 12)
    (lo := (58704979 / 250000000)) (hi := (234819917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264681 / 1000000) = 1/(1000000 / 1264681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58704979 / 250000000) (234819917 / 1000000000) (Real.log (1264681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1264681 / 1000000) = -Real.log (1000000 / 1264681) := by
    rw [show ((1264681 / 1000000) : ℝ) = ((1000000 / 1264681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15372543 / 50000000) ≤ -Real.log (735319 / 1000000) ∧
    -Real.log (735319 / 1000000) ≤ (307450861 / 1000000000) := by
  have h := checkLog_sound (w := (264681 / 1735319)) (n := 12)
    (lo := (15372543 / 50000000)) (hi := (307450861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735319) = 1/(735319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-307450861 / 1000000000) (-15372543 / 50000000) (Real.log (735319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (117544361 / 500000000) ≤ -Real.log (1000000 / 1265021) ∧
    -Real.log (1000000 / 1265021) ≤ (235088723 / 1000000000) := by
  have h := checkLog_sound (w := (265021 / 2265021)) (n := 12)
    (lo := (117544361 / 500000000)) (hi := (235088723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265021 / 1000000) = 1/(1000000 / 1265021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (117544361 / 500000000) (235088723 / 1000000000) (Real.log (1265021 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1265021 / 1000000) = -Real.log (1000000 / 1265021) := by
    rw [show ((1265021 / 1000000) : ℝ) = ((1000000 / 1265021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (307913351 / 1000000000) ≤ -Real.log (734979 / 1000000) ∧
    -Real.log (734979 / 1000000) ≤ (38489169 / 125000000) := by
  have h := checkLog_sound (w := (265021 / 1734979)) (n := 12)
    (lo := (307913351 / 1000000000)) (hi := (38489169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734979) = 1/(734979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-38489169 / 125000000) (-307913351 / 1000000000) (Real.log (734979 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (188921631 / 250000000) ≤ -Real.log (62500000000 / 133067042729) ∧
    -Real.log (62500000000 / 133067042729) ≤ (377843263 / 500000000) := by
  have h := checkLog_sound (w := (8067042729 / 258067042729)) (n := 12)
    (lo := (3908709 / 62500000)) (hi := (12507869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133067042729 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(133067042729 / 125000000000) = 1/(62500000000 / 133067042729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188921631 / 250000000) (377843263 / 500000000) (Real.log (133067042729 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (133067042729 / 62500000000) = -Real.log (62500000000 / 133067042729) := by
    rw [show ((133067042729 / 62500000000) : ℝ) = ((62500000000 / 133067042729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (151336007 / 200000000) ≤ -Real.log (50000000000 / 106559449537) ∧
    -Real.log (50000000000 / 106559449537) ≤ (756680037 / 1000000000) := by
  have h := checkLog_sound (w := (6559449537 / 206559449537)) (n := 12)
    (lo := (12706571 / 200000000)) (hi := (7941607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106559449537 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(106559449537 / 100000000000) = 1/(50000000000 / 106559449537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (151336007 / 200000000) (756680037 / 1000000000) (Real.log (106559449537 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (106559449537 / 50000000000) = -Real.log (50000000000 / 106559449537) := by
    rw [show ((106559449537 / 50000000000) : ℝ) = ((50000000000 / 106559449537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (67783847 / 125000000) ≤ -Real.log (500000000000 / 859953979157) ∧
    -Real.log (500000000000 / 859953979157) ≤ (542270777 / 1000000000) := by
  have h := checkLog_sound (w := (359953979157 / 1359953979157)) (n := 12)
    (lo := (67783847 / 125000000)) (hi := (542270777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859953979157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859953979157 / 500000000000) = 1/(500000000000 / 859953979157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (67783847 / 125000000) (542270777 / 1000000000) (Real.log (859953979157 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (859953979157 / 500000000000) = -Real.log (500000000000 / 859953979157) := by
    rw [show ((859953979157 / 500000000000) : ℝ) = ((500000000000 / 859953979157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (271501037 / 500000000) ≤ -Real.log (50000000000 / 86058309149) ∧
    -Real.log (50000000000 / 86058309149) ≤ (21720083 / 40000000) := by
  have h := checkLog_sound (w := (36058309149 / 136058309149)) (n := 12)
    (lo := (271501037 / 500000000)) (hi := (21720083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86058309149 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86058309149 / 50000000000) = 1/(50000000000 / 86058309149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (271501037 / 500000000) (21720083 / 40000000) (Real.log (86058309149 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (86058309149 / 50000000000) = -Real.log (50000000000 / 86058309149) := by
    rw [show ((86058309149 / 50000000000) : ℝ) = ((50000000000 / 86058309149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0295
