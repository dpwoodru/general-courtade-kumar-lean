import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0339
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

theorem reflection_log_1_neg : (2684363 / 12500000) ≤ -Real.log (10240 / 12693) ∧
    -Real.log (10240 / 12693) ≤ (214749041 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 22933)) (n := 12)
    (lo := (2684363 / 12500000)) (hi := (214749041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12693 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12693 / 10240) = 1/(10240 / 12693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2684363 / 12500000) (214749041 / 1000000000) (Real.log (12693 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12693 / 10240) = -Real.log (10240 / 12693) := by
    rw [show ((12693 / 10240) : ℝ) = ((10240 / 12693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (273845943 / 1000000000) ≤ -Real.log (7787 / 10240) ∧
    -Real.log (7787 / 10240) ≤ (34230743 / 125000000) := by
  have h := checkLog_sound (w := (2453 / 18027)) (n := 12)
    (lo := (273845943 / 1000000000)) (hi := (34230743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7787) = 1/(7787 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34230743 / 125000000) (-273845943 / 1000000000) (Real.log (7787 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (107256331 / 500000000) ≤ -Real.log (1024 / 1269) ∧
    -Real.log (1024 / 1269) ≤ (214512663 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 2293)) (n := 12)
    (lo := (107256331 / 500000000)) (hi := (214512663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1024) = 1/(1024 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (107256331 / 500000000) (214512663 / 1000000000) (Real.log (1269 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1269 / 1024) = -Real.log (1024 / 1269) := by
    rw [show ((1269 / 1024) : ℝ) = ((1024 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (273460759 / 1000000000) ≤ -Real.log (779 / 1024) ∧
    -Real.log (779 / 1024) ≤ (6836519 / 25000000) := by
  have h := checkLog_sound (w := (245 / 1803)) (n := 12)
    (lo := (273460759 / 1000000000)) (hi := (6836519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 779) = 1/(779 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6836519 / 25000000) (-273460759 / 1000000000) (Real.log (779 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (391434851 / 1000000000) ≤ -Real.log (5120 / 7573) ∧
    -Real.log (5120 / 7573) ≤ (97858713 / 250000000) := by
  have h := checkLog_sound (w := (2453 / 12693)) (n := 12)
    (lo := (391434851 / 1000000000)) (hi := (97858713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7573 / 5120) = 1/(5120 / 7573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (391434851 / 1000000000) (97858713 / 250000000) (Real.log (7573 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7573 / 5120) = -Real.log (5120 / 7573) := by
    rw [show ((7573 / 5120) : ℝ) = ((5120 / 7573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (652200193 / 1000000000) ≤ -Real.log (2667 / 5120) ∧
    -Real.log (2667 / 5120) ≤ (326100097 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 7787)) (n := 12)
    (lo := (652200193 / 1000000000)) (hi := (326100097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2667) = 1/(2667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-326100097 / 500000000) (-652200193 / 1000000000) (Real.log (2667 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97759657 / 250000000) ≤ -Real.log (512 / 757) ∧
    -Real.log (512 / 757) ≤ (391038629 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 1269)) (n := 12)
    (lo := (97759657 / 250000000)) (hi := (391038629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 512) = 1/(512 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97759657 / 250000000) (391038629 / 1000000000) (Real.log (757 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (757 / 512) = -Real.log (512 / 757) := by
    rw [show ((757 / 512) : ℝ) = ((512 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325537983 / 500000000) ≤ -Real.log (267 / 512) ∧
    -Real.log (267 / 512) ≤ (651075967 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 779)) (n := 12)
    (lo := (325537983 / 500000000)) (hi := (651075967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 267) = 1/(267 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-651075967 / 1000000000) (-325537983 / 500000000) (Real.log (267 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36764541 / 125000000) ≤ -Real.log (50000 / 67097) ∧
    -Real.log (50000 / 67097) ≤ (294116329 / 1000000000) := by
  have h := checkLog_sound (w := (17097 / 117097)) (n := 12)
    (lo := (36764541 / 125000000)) (hi := (294116329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67097 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67097 / 50000) = 1/(50000 / 67097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36764541 / 125000000) (294116329 / 1000000000) (Real.log (67097 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67097 / 50000) = -Real.log (50000 / 67097) := by
    rw [show ((67097 / 50000) : ℝ) = ((50000 / 67097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209229583 / 500000000) ≤ -Real.log (32903 / 50000) ∧
    -Real.log (32903 / 50000) ≤ (418459167 / 1000000000) := by
  have h := checkLog_sound (w := (17097 / 82903)) (n := 12)
    (lo := (209229583 / 500000000)) (hi := (418459167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32903) = 1/(32903 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-418459167 / 1000000000) (-209229583 / 500000000) (Real.log (32903 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (294435963 / 1000000000) ≤ -Real.log (1000000 / 1342369) ∧
    -Real.log (1000000 / 1342369) ≤ (73608991 / 250000000) := by
  have h := checkLog_sound (w := (342369 / 2342369)) (n := 12)
    (lo := (294435963 / 1000000000)) (hi := (73608991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342369 / 1000000) = 1/(1000000 / 1342369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (294435963 / 1000000000) (73608991 / 250000000) (Real.log (1342369 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1342369 / 1000000) = -Real.log (1000000 / 1342369) := by
    rw [show ((1342369 / 1000000) : ℝ) = ((1000000 / 1342369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83822259 / 200000000) ≤ -Real.log (657631 / 1000000) ∧
    -Real.log (657631 / 1000000) ≤ (3274307 / 7812500) := by
  have h := checkLog_sound (w := (342369 / 1657631)) (n := 12)
    (lo := (83822259 / 200000000)) (hi := (3274307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657631) = 1/(657631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3274307 / 7812500) (-83822259 / 200000000) (Real.log (657631 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (111520973 / 500000000) ≤ -Real.log (1000000 / 1249873) ∧
    -Real.log (1000000 / 1249873) ≤ (223041947 / 1000000000) := by
  have h := checkLog_sound (w := (249873 / 2249873)) (n := 12)
    (lo := (111520973 / 500000000)) (hi := (223041947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249873 / 1000000) = 1/(1000000 / 1249873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (111520973 / 500000000) (223041947 / 1000000000) (Real.log (1249873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1249873 / 1000000) = -Real.log (1000000 / 1249873) := by
    rw [show ((1249873 / 1000000) : ℝ) = ((1000000 / 1249873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (287512753 / 1000000000) ≤ -Real.log (750127 / 1000000) ∧
    -Real.log (750127 / 1000000) ≤ (143756377 / 500000000) := by
  have h := checkLog_sound (w := (249873 / 1750127)) (n := 12)
    (lo := (287512753 / 1000000000)) (hi := (143756377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750127) = 1/(750127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-143756377 / 500000000) (-287512753 / 1000000000) (Real.log (750127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (223309937 / 1000000000) ≤ -Real.log (31250 / 39069) ∧
    -Real.log (31250 / 39069) ≤ (111654969 / 500000000) := by
  have h := checkLog_sound (w := (7819 / 70319)) (n := 12)
    (lo := (223309937 / 1000000000)) (hi := (111654969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39069 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39069 / 31250) = 1/(31250 / 39069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (223309937 / 1000000000) (111654969 / 500000000) (Real.log (39069 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39069 / 31250) = -Real.log (31250 / 39069) := by
    rw [show ((39069 / 31250) : ℝ) = ((31250 / 39069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (71989861 / 250000000) ≤ -Real.log (23431 / 31250) ∧
    -Real.log (23431 / 31250) ≤ (57591889 / 200000000) := by
  have h := checkLog_sound (w := (7819 / 54681)) (n := 12)
    (lo := (71989861 / 250000000)) (hi := (57591889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23431) = 1/(23431 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-57591889 / 200000000) (-71989861 / 250000000) (Real.log (23431 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (356287747 / 500000000) ≤ -Real.log (50000000000 / 101961827189) ∧
    -Real.log (50000000000 / 101961827189) ≤ (89071937 / 125000000) := by
  have h := checkLog_sound (w := (1961827189 / 201961827189)) (n := 12)
    (lo := (9714157 / 500000000)) (hi := (3885663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101961827189 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101961827189 / 100000000000) = 1/(50000000000 / 101961827189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (356287747 / 500000000) (89071937 / 125000000) (Real.log (101961827189 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (101961827189 / 50000000000) = -Real.log (50000000000 / 101961827189) := by
    rw [show ((101961827189 / 50000000000) : ℝ) = ((50000000000 / 101961827189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356773629 / 500000000) ≤ -Real.log (50000000000 / 102060958197) ∧
    -Real.log (50000000000 / 102060958197) ≤ (35677363 / 50000000) := by
  have h := checkLog_sound (w := (2060958197 / 202060958197)) (n := 12)
    (lo := (10200039 / 500000000)) (hi := (20400079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102060958197 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102060958197 / 100000000000) = 1/(50000000000 / 102060958197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356773629 / 500000000) (35677363 / 50000000) (Real.log (102060958197 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (102060958197 / 50000000000) = -Real.log (50000000000 / 102060958197) := by
    rw [show ((102060958197 / 50000000000) : ℝ) = ((50000000000 / 102060958197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (510554699 / 1000000000) ≤ -Real.log (25000000000 / 41655379689) ∧
    -Real.log (25000000000 / 41655379689) ≤ (5105547 / 10000000) := by
  have h := checkLog_sound (w := (16655379689 / 66655379689)) (n := 12)
    (lo := (510554699 / 1000000000)) (hi := (5105547 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41655379689 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41655379689 / 25000000000) = 1/(25000000000 / 41655379689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (510554699 / 1000000000) (5105547 / 10000000) (Real.log (41655379689 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41655379689 / 25000000000) = -Real.log (25000000000 / 41655379689) := by
    rw [show ((41655379689 / 25000000000) : ℝ) = ((25000000000 / 41655379689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (511269381 / 1000000000) ≤ -Real.log (125000000000 / 208425803423) ∧
    -Real.log (125000000000 / 208425803423) ≤ (255634691 / 500000000) := by
  have h := checkLog_sound (w := (83425803423 / 333425803423)) (n := 12)
    (lo := (511269381 / 1000000000)) (hi := (255634691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208425803423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208425803423 / 125000000000) = 1/(125000000000 / 208425803423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (511269381 / 1000000000) (255634691 / 500000000) (Real.log (208425803423 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (208425803423 / 125000000000) = -Real.log (125000000000 / 208425803423) := by
    rw [show ((208425803423 / 125000000000) : ℝ) = ((125000000000 / 208425803423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0339
