import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0165
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

theorem reflection_log_1_neg : (140632521 / 500000000) ≤ -Real.log (5120 / 6783) ∧
    -Real.log (5120 / 6783) ≤ (281265043 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 11903)) (n := 12)
    (lo := (140632521 / 500000000)) (hi := (281265043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6783 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6783 / 5120) = 1/(5120 / 6783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140632521 / 500000000) (281265043 / 1000000000) (Real.log (6783 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6783 / 5120) = -Real.log (5120 / 6783) := by
    rw [show ((6783 / 5120) : ℝ) = ((5120 / 6783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (196376639 / 500000000) ≤ -Real.log (3457 / 5120) ∧
    -Real.log (3457 / 5120) ≤ (392753279 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 8577)) (n := 12)
    (lo := (196376639 / 500000000)) (hi := (392753279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3457) = 1/(3457 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-392753279 / 1000000000) (-196376639 / 500000000) (Real.log (3457 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140411331 / 500000000) ≤ -Real.log (256 / 339) ∧
    -Real.log (256 / 339) ≤ (280822663 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 595)) (n := 12)
    (lo := (140411331 / 500000000)) (hi := (280822663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 256) = 1/(256 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140411331 / 500000000) (280822663 / 1000000000) (Real.log (339 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (339 / 256) = -Real.log (256 / 339) := by
    rw [show ((339 / 256) : ℝ) = ((256 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (391885849 / 1000000000) ≤ -Real.log (173 / 256) ∧
    -Real.log (173 / 256) ≤ (7837717 / 20000000) := by
  have h := checkLog_sound (w := (83 / 429)) (n := 12)
    (lo := (391885849 / 1000000000)) (hi := (7837717 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 173) = 1/(173 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7837717 / 20000000) (-391885849 / 1000000000) (Real.log (173 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (500538517 / 1000000000) ≤ -Real.log (2560 / 4223) ∧
    -Real.log (2560 / 4223) ≤ (250269259 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 6783)) (n := 12)
    (lo := (500538517 / 1000000000)) (hi := (250269259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4223 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4223 / 2560) = 1/(2560 / 4223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (500538517 / 1000000000) (250269259 / 500000000) (Real.log (4223 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4223 / 2560) = -Real.log (2560 / 4223) := by
    rw [show ((4223 / 2560) : ℝ) = ((2560 / 4223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (524353337 / 500000000) ≤ -Real.log (897 / 2560) ∧
    -Real.log (897 / 2560) ≤ (262176669 / 250000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 897) = 1/(897 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-262176669 / 250000000) (-524353337 / 500000000) (Real.log (897 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (499827869 / 1000000000) ≤ -Real.log (128 / 211) ∧
    -Real.log (128 / 211) ≤ (49982787 / 100000000) := by
  have h := checkLog_sound (w := (83 / 339)) (n := 12)
    (lo := (499827869 / 1000000000)) (hi := (49982787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 128) = 1/(128 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (499827869 / 1000000000) (49982787 / 100000000) (Real.log (211 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (211 / 128) = -Real.log (128 / 211) := by
    rw [show ((211 / 128) : ℝ) = ((128 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1045367773 / 1000000000) ≤ -Real.log (45 / 128) ∧
    -Real.log (45 / 128) ≤ (41814711 / 40000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 45) = 1/(45 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-41814711 / 40000000) (-1045367773 / 1000000000) (Real.log (45 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (192083281 / 500000000) ≤ -Real.log (100000 / 146839) ∧
    -Real.log (100000 / 146839) ≤ (384166563 / 1000000000) := by
  have h := checkLog_sound (w := (46839 / 246839)) (n := 12)
    (lo := (192083281 / 500000000)) (hi := (384166563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146839 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146839 / 100000) = 1/(100000 / 146839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (192083281 / 500000000) (384166563 / 1000000000) (Real.log (146839 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (146839 / 100000) = -Real.log (100000 / 146839) := by
    rw [show ((146839 / 100000) : ℝ) = ((100000 / 146839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (631845141 / 1000000000) ≤ -Real.log (53161 / 100000) ∧
    -Real.log (53161 / 100000) ≤ (315922571 / 500000000) := by
  have h := checkLog_sound (w := (46839 / 153161)) (n := 12)
    (lo := (631845141 / 1000000000)) (hi := (315922571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 53161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 53161) = 1/(53161 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-315922571 / 500000000) (-631845141 / 1000000000) (Real.log (53161 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (192386923 / 500000000) ≤ -Real.log (500000 / 734641) ∧
    -Real.log (500000 / 734641) ≤ (384773847 / 1000000000) := by
  have h := checkLog_sound (w := (234641 / 1234641)) (n := 12)
    (lo := (192386923 / 500000000)) (hi := (384773847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734641 / 500000) = 1/(500000 / 734641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (192386923 / 500000000) (384773847 / 1000000000) (Real.log (734641 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (734641 / 500000) = -Real.log (500000 / 734641) := by
    rw [show ((734641 / 500000) : ℝ) = ((500000 / 734641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79190559 / 125000000) ≤ -Real.log (265359 / 500000) ∧
    -Real.log (265359 / 500000) ≤ (633524473 / 1000000000) := by
  have h := checkLog_sound (w := (234641 / 765359)) (n := 12)
    (lo := (79190559 / 125000000)) (hi := (633524473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 265359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 265359) = 1/(265359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-633524473 / 1000000000) (-79190559 / 125000000) (Real.log (265359 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150996589 / 500000000) ≤ -Real.log (125000 / 169069) ∧
    -Real.log (125000 / 169069) ≤ (301993179 / 1000000000) := by
  have h := checkLog_sound (w := (44069 / 294069)) (n := 12)
    (lo := (150996589 / 500000000)) (hi := (301993179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169069 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169069 / 125000) = 1/(125000 / 169069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150996589 / 500000000) (301993179 / 1000000000) (Real.log (169069 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169069 / 125000) = -Real.log (125000 / 169069) := by
    rw [show ((169069 / 125000) : ℝ) = ((125000 / 169069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (434716797 / 1000000000) ≤ -Real.log (80931 / 125000) ∧
    -Real.log (80931 / 125000) ≤ (217358399 / 500000000) := by
  have h := checkLog_sound (w := (44069 / 205931)) (n := 12)
    (lo := (434716797 / 1000000000)) (hi := (217358399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80931) = 1/(80931 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-217358399 / 500000000) (-434716797 / 1000000000) (Real.log (80931 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (302553443 / 1000000000) ≤ -Real.log (100000 / 135331) ∧
    -Real.log (100000 / 135331) ≤ (75638361 / 250000000) := by
  have h := checkLog_sound (w := (35331 / 235331)) (n := 12)
    (lo := (302553443 / 1000000000)) (hi := (75638361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135331 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135331 / 100000) = 1/(100000 / 135331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (302553443 / 1000000000) (75638361 / 250000000) (Real.log (135331 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (135331 / 100000) = -Real.log (100000 / 135331) := by
    rw [show ((135331 / 100000) : ℝ) = ((100000 / 135331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (435888233 / 1000000000) ≤ -Real.log (64669 / 100000) ∧
    -Real.log (64669 / 100000) ≤ (217944117 / 500000000) := by
  have h := checkLog_sound (w := (35331 / 164669)) (n := 12)
    (lo := (435888233 / 1000000000)) (hi := (217944117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64669) = 1/(64669 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-217944117 / 500000000) (-435888233 / 1000000000) (Real.log (64669 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1016011703 / 1000000000) ≤ -Real.log (500000000000 / 1381078234043) ∧
    -Real.log (500000000000 / 1381078234043) ≤ (203202341 / 200000000) := by
  have h := checkLog_sound (w := (381078234043 / 2381078234043)) (n := 12)
    (lo := (322864523 / 1000000000)) (hi := (80716131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381078234043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1381078234043 / 1000000000000) = 1/(500000000000 / 1381078234043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1016011703 / 1000000000) (203202341 / 200000000) (Real.log (1381078234043 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1381078234043 / 500000000000) = -Real.log (500000000000 / 1381078234043) := by
    rw [show ((1381078234043 / 500000000000) : ℝ) = ((500000000000 / 1381078234043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1018298317 / 1000000000) ≤ -Real.log (500000000000 / 1384239841121) ∧
    -Real.log (500000000000 / 1384239841121) ≤ (1018298319 / 1000000000) := by
  have h := checkLog_sound (w := (384239841121 / 2384239841121)) (n := 12)
    (lo := (325151137 / 1000000000)) (hi := (162575569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384239841121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1384239841121 / 1000000000000) = 1/(500000000000 / 1384239841121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1018298317 / 1000000000) (1018298319 / 1000000000) (Real.log (1384239841121 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1384239841121 / 500000000000) = -Real.log (500000000000 / 1384239841121) := by
    rw [show ((1384239841121 / 500000000000) : ℝ) = ((500000000000 / 1384239841121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29468399 / 40000000) ≤ -Real.log (500000000000 / 1044525583521) ∧
    -Real.log (500000000000 / 1044525583521) ≤ (736709977 / 1000000000) := by
  have h := checkLog_sound (w := (44525583521 / 2044525583521)) (n := 12)
    (lo := (8712559 / 200000000)) (hi := (10890699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1044525583521 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1044525583521 / 1000000000000) = 1/(500000000000 / 1044525583521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (29468399 / 40000000) (736709977 / 1000000000) (Real.log (1044525583521 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1044525583521 / 500000000000) = -Real.log (500000000000 / 1044525583521) := by
    rw [show ((1044525583521 / 500000000000) : ℝ) = ((500000000000 / 1044525583521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (184610419 / 250000000) ≤ -Real.log (500000000000 / 1046335956951) ∧
    -Real.log (500000000000 / 1046335956951) ≤ (369220839 / 500000000) := by
  have h := checkLog_sound (w := (46335956951 / 2046335956951)) (n := 12)
    (lo := (1415453 / 31250000)) (hi := (45294497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1046335956951 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1046335956951 / 1000000000000) = 1/(500000000000 / 1046335956951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (184610419 / 250000000) (369220839 / 500000000) (Real.log (1046335956951 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1046335956951 / 500000000000) = -Real.log (500000000000 / 1046335956951) := by
    rw [show ((1046335956951 / 500000000000) : ℝ) = ((500000000000 / 1046335956951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0165
