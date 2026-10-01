import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221
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

theorem reflection_log_1_neg : (65081523 / 125000000) ≤ -Real.log (1600 / 2693) ∧
    -Real.log (1600 / 2693) ≤ (104130437 / 200000000) := by
  have h := checkLog_sound (w := (1093 / 4293)) (n := 12)
    (lo := (65081523 / 125000000)) (hi := (104130437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2693 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2693 / 1600) = 1/(1600 / 2693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65081523 / 125000000) (104130437 / 200000000) (Real.log (2693 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2693 / 1600) = -Real.log (1600 / 2693) := by
    rw [show ((2693 / 1600) : ℝ) = ((1600 / 2693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (35913997 / 31250000) ≤ -Real.log (507 / 1600) ∧
    -Real.log (507 / 1600) ≤ (574623953 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 507) = 1/(507 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-574623953 / 500000000) (-35913997 / 31250000) (Real.log (507 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (513571849 / 1000000000) ≤ -Real.log (800 / 1337) ∧
    -Real.log (800 / 1337) ≤ (10271437 / 20000000) := by
  have h := checkLog_sound (w := (537 / 2137)) (n := 12)
    (lo := (513571849 / 1000000000)) (hi := (10271437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 800) = 1/(800 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (513571849 / 1000000000) (10271437 / 20000000) (Real.log (1337 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1337 / 800) = -Real.log (800 / 1337) := by
    rw [show ((1337 / 800) : ℝ) = ((800 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (556228847 / 500000000) ≤ -Real.log (263 / 800) ∧
    -Real.log (263 / 800) ≤ (34764303 / 31250000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 263) = 1/(263 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34764303 / 31250000) (-556228847 / 500000000) (Real.log (263 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (487609 / 1562500) ≤ -Real.log (800 / 1093) ∧
    -Real.log (800 / 1093) ≤ (312069761 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1893)) (n := 12)
    (lo := (487609 / 1562500)) (hi := (312069761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093 / 800) = 1/(800 / 1093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (487609 / 1562500) (312069761 / 1000000000) (Real.log (1093 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1093 / 800) = -Real.log (800 / 1093) := by
    rw [show ((1093 / 800) : ℝ) = ((800 / 1093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114025181 / 250000000) ≤ -Real.log (507 / 800) ∧
    -Real.log (507 / 800) ≤ (18244029 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1307)) (n := 12)
    (lo := (114025181 / 250000000)) (hi := (18244029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 507) = 1/(507 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-18244029 / 40000000) (-114025181 / 250000000) (Real.log (507 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (294533547 / 1000000000) ≤ -Real.log (400 / 537) ∧
    -Real.log (400 / 537) ≤ (73633387 / 250000000) := by
  have h := checkLog_sound (w := (137 / 937)) (n := 12)
    (lo := (294533547 / 1000000000)) (hi := (73633387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537 / 400) = 1/(400 / 537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (294533547 / 1000000000) (73633387 / 250000000) (Real.log (537 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (537 / 400) = -Real.log (400 / 537) := by
    rw [show ((537 / 400) : ℝ) = ((400 / 537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209655257 / 500000000) ≤ -Real.log (263 / 400) ∧
    -Real.log (263 / 400) ≤ (83862103 / 200000000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 263) = 1/(263 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83862103 / 200000000) (-209655257 / 500000000) (Real.log (263 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (592003317 / 1000000000) ≤ -Real.log (500000 / 903803) ∧
    -Real.log (500000 / 903803) ≤ (296001659 / 500000000) := by
  have h := checkLog_sound (w := (403803 / 1403803)) (n := 12)
    (lo := (592003317 / 1000000000)) (hi := (296001659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903803 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903803 / 500000) = 1/(500000 / 903803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (592003317 / 1000000000) (296001659 / 500000000) (Real.log (903803 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (903803 / 500000) = -Real.log (500000 / 903803) := by
    rw [show ((903803 / 500000) : ℝ) = ((500000 / 903803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (65928397 / 40000000) ≤ -Real.log (96197 / 500000) ∧
    -Real.log (96197 / 500000) ≤ (206026241 / 125000000) := by
  have h := checkLog_sound (w := (28803 / 221197)) (n := 12)
    (lo := (52383113 / 200000000)) (hi := (130957783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96197) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 96197) = 1/(96197 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-206026241 / 125000000) (-65928397 / 40000000) (Real.log (96197 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (594163511 / 1000000000) ≤ -Real.log (200000 / 362303) ∧
    -Real.log (200000 / 362303) ≤ (74270439 / 125000000) := by
  have h := checkLog_sound (w := (162303 / 562303)) (n := 12)
    (lo := (594163511 / 1000000000)) (hi := (74270439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362303 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362303 / 200000) = 1/(200000 / 362303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (594163511 / 1000000000) (74270439 / 125000000) (Real.log (362303 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (362303 / 200000) = -Real.log (200000 / 362303) := by
    rw [show ((362303 / 200000) : ℝ) = ((200000 / 362303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1668736849 / 1000000000) ≤ -Real.log (37697 / 200000) ∧
    -Real.log (37697 / 200000) ≤ (417184213 / 250000000) := by
  have h := checkLog_sound (w := (12303 / 87697)) (n := 12)
    (lo := (282442489 / 1000000000)) (hi := (28244249 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37697) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 37697) = 1/(37697 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-417184213 / 250000000) (-1668736849 / 1000000000) (Real.log (37697 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (142137511 / 250000000) ≤ -Real.log (200000 / 353141) ∧
    -Real.log (200000 / 353141) ≤ (113710009 / 200000000) := by
  have h := checkLog_sound (w := (153141 / 553141)) (n := 12)
    (lo := (142137511 / 250000000)) (hi := (113710009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353141 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353141 / 200000) = 1/(200000 / 353141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (142137511 / 250000000) (113710009 / 200000000) (Real.log (353141 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (353141 / 200000) = -Real.log (200000 / 353141) := by
    rw [show ((353141 / 200000) : ℝ) = ((200000 / 353141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11337299 / 7812500) ≤ -Real.log (46859 / 200000) ∧
    -Real.log (46859 / 200000) ≤ (58046971 / 40000000) := by
  have h := checkLog_sound (w := (3141 / 96859)) (n := 12)
    (lo := (8109989 / 125000000)) (hi := (64879913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46859) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 46859) = 1/(46859 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58046971 / 40000000) (-11337299 / 7812500) (Real.log (46859 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (572842217 / 1000000000) ≤ -Real.log (10000 / 17733) ∧
    -Real.log (10000 / 17733) ≤ (286421109 / 500000000) := by
  have h := checkLog_sound (w := (7733 / 27733)) (n := 12)
    (lo := (572842217 / 1000000000)) (hi := (286421109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17733 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17733 / 10000) = 1/(10000 / 17733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (572842217 / 1000000000) (286421109 / 500000000) (Real.log (17733 / 10000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (17733 / 10000) = -Real.log (10000 / 17733) := by
    rw [show ((17733 / 10000) : ℝ) = ((10000 / 17733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37103193 / 25000000) ≤ -Real.log (2267 / 10000) ∧
    -Real.log (2267 / 10000) ≤ (1484127723 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 4767)) (n := 12)
    (lo := (1222917 / 12500000)) (hi := (97833361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2500 / 2267) = 1/(2267 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1484127723 / 1000000000) (-37103193 / 25000000) (Real.log (2267 / 10000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1120106621 / 500000000) ≤ -Real.log (500000000000 / 4697667286921) ∧
    -Real.log (500000000000 / 4697667286921) ≤ (1120106623 / 500000000) := by
  have h := checkLog_sound (w := (697667286921 / 8697667286921)) (n := 12)
    (lo := (80385851 / 500000000)) (hi := (160771703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4697667286921 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4697667286921 / 4000000000000) = 1/(500000000000 / 4697667286921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1120106621 / 500000000) (1120106623 / 500000000) (Real.log (4697667286921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4697667286921 / 500000000000) = -Real.log (500000000000 / 4697667286921) := by
    rw [show ((4697667286921 / 500000000000) : ℝ) = ((500000000000 / 4697667286921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56572509 / 25000000) ≤ -Real.log (250000000000 / 2402730986551) ∧
    -Real.log (250000000000 / 2402730986551) ≤ (565725091 / 250000000) := by
  have h := checkLog_sound (w := (402730986551 / 4402730986551)) (n := 12)
    (lo := (9172941 / 50000000)) (hi := (183458821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2402730986551 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2402730986551 / 2000000000000) = 1/(250000000000 / 2402730986551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56572509 / 25000000) (565725091 / 250000000) (Real.log (2402730986551 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2402730986551 / 250000000000) = -Real.log (250000000000 / 2402730986551) := by
    rw [show ((2402730986551 / 250000000000) : ℝ) = ((250000000000 / 2402730986551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (504931079 / 250000000) ≤ -Real.log (250000000000 / 1884061759747) ∧
    -Real.log (250000000000 / 1884061759747) ≤ (2019724319 / 1000000000) := by
  have h := checkLog_sound (w := (884061759747 / 2884061759747)) (n := 12)
    (lo := (158357489 / 250000000)) (hi := (633429957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1884061759747 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1884061759747 / 1000000000000) = 1/(250000000000 / 1884061759747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (504931079 / 250000000) (2019724319 / 1000000000) (Real.log (1884061759747 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1884061759747 / 250000000000) = -Real.log (250000000000 / 1884061759747) := by
    rw [show ((1884061759747 / 250000000000) : ℝ) = ((250000000000 / 1884061759747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2056969937 / 1000000000) ≤ -Real.log (7812500000 / 61111187693) ∧
    -Real.log (7812500000 / 61111187693) ≤ (102848497 / 50000000) := by
  have h := checkLog_sound (w := (29861187693 / 92361187693)) (n := 12)
    (lo := (670675577 / 1000000000)) (hi := (335337789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61111187693 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(61111187693 / 31250000000) = 1/(7812500000 / 61111187693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2056969937 / 1000000000) (102848497 / 50000000) (Real.log (61111187693 / 7812500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (61111187693 / 7812500000) = -Real.log (7812500000 / 61111187693) := by
    rw [show ((61111187693 / 7812500000) : ℝ) = ((7812500000 / 61111187693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221
