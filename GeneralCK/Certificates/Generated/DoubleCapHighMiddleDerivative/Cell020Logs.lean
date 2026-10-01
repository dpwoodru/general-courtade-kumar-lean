import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (232939167 / 1000000000) ≤ -Real.log (5120 / 6463) ∧
    -Real.log (5120 / 6463) ≤ (7279349 / 31250000) := by
  have h := checkLog_sound (w := (1343 / 11583)) (n := 12)
    (lo := (232939167 / 1000000000)) (hi := (7279349 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6463 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6463 / 5120) = 1/(5120 / 6463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (232939167 / 1000000000) (7279349 / 31250000) (Real.log (6463 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6463 / 5120) = -Real.log (5120 / 6463) := by
    rw [show ((6463 / 5120) : ℝ) = ((5120 / 6463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (60844879 / 200000000) ≤ -Real.log (3777 / 5120) ∧
    -Real.log (3777 / 5120) ≤ (76056099 / 250000000) := by
  have h := checkLog_sound (w := (1343 / 8897)) (n := 12)
    (lo := (60844879 / 200000000)) (hi := (76056099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3777) = 1/(3777 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) (Real.log (3777 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116237439 / 500000000) ≤ -Real.log (256 / 323) ∧
    -Real.log (256 / 323) ≤ (232474879 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 579)) (n := 12)
    (lo := (116237439 / 500000000)) (hi := (232474879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 256) = 1/(256 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116237439 / 500000000) (232474879 / 1000000000) (Real.log (323 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (323 / 256) = -Real.log (256 / 323) := by
    rw [show ((323 / 256) : ℝ) = ((256 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303430429 / 1000000000) ≤ -Real.log (189 / 256) ∧
    -Real.log (189 / 256) ≤ (30343043 / 100000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 189) = 1/(189 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) (Real.log (189 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42563509 / 250000000) ≤ -Real.log (500000 / 592803) ∧
    -Real.log (500000 / 592803) ≤ (170254037 / 1000000000) := by
  have h := checkLog_sound (w := (92803 / 1092803)) (n := 12)
    (lo := (42563509 / 250000000)) (hi := (170254037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592803 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592803 / 500000) = 1/(500000 / 592803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42563509 / 250000000) (170254037 / 1000000000) (Real.log (592803 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (592803 / 500000) = -Real.log (500000 / 592803) := by
    rw [show ((592803 / 500000) : ℝ) = ((500000 / 592803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (205311 / 1000000) ≤ -Real.log (407197 / 500000) ∧
    -Real.log (407197 / 500000) ≤ (205311001 / 1000000000) := by
  have h := checkLog_sound (w := (92803 / 907197)) (n := 12)
    (lo := (205311 / 1000000)) (hi := (205311001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407197) = 1/(407197 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-205311001 / 1000000000) (-205311 / 1000000) (Real.log (407197 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170607379 / 1000000000) ≤ -Real.log (40000 / 47441) ∧
    -Real.log (40000 / 47441) ≤ (8530369 / 50000000) := by
  have h := checkLog_sound (w := (7441 / 87441)) (n := 12)
    (lo := (170607379 / 1000000000)) (hi := (8530369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47441 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47441 / 40000) = 1/(40000 / 47441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170607379 / 1000000000) (8530369 / 50000000) (Real.log (47441 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47441 / 40000) = -Real.log (40000 / 47441) := by
    rw [show ((47441 / 40000) : ℝ) = ((40000 / 47441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (329321 / 1600000) ≤ -Real.log (32559 / 40000) ∧
    -Real.log (32559 / 40000) ≤ (102912813 / 500000000) := by
  have h := checkLog_sound (w := (7441 / 72559)) (n := 12)
    (lo := (329321 / 1600000)) (hi := (102912813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32559) = 1/(32559 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-102912813 / 500000000) (-329321 / 1600000) (Real.log (32559 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4977421 / 40000000) ≤ -Real.log (1000000 / 1132509) ∧
    -Real.log (1000000 / 1132509) ≤ (62217763 / 500000000) := by
  have h := checkLog_sound (w := (132509 / 2132509)) (n := 12)
    (lo := (4977421 / 40000000)) (hi := (62217763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132509 / 1000000) = 1/(1000000 / 1132509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4977421 / 40000000) (62217763 / 500000000) (Real.log (1132509 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1132509 / 1000000) = -Real.log (1000000 / 1132509) := by
    rw [show ((1132509 / 1000000) : ℝ) = ((1000000 / 1132509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142150141 / 1000000000) ≤ -Real.log (867491 / 1000000) ∧
    -Real.log (867491 / 1000000) ≤ (71075071 / 500000000) := by
  have h := checkLog_sound (w := (132509 / 1867491)) (n := 12)
    (lo := (142150141 / 1000000000)) (hi := (71075071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867491) = 1/(867491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71075071 / 500000000) (-142150141 / 1000000000) (Real.log (867491 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62352401 / 500000000) ≤ -Real.log (500000 / 566407) ∧
    -Real.log (500000 / 566407) ≤ (124704803 / 1000000000) := by
  have h := checkLog_sound (w := (66407 / 1066407)) (n := 12)
    (lo := (62352401 / 500000000)) (hi := (124704803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566407 / 500000) = 1/(500000 / 566407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62352401 / 500000000) (124704803 / 1000000000) (Real.log (566407 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566407 / 500000) = -Real.log (500000 / 566407) := by
    rw [show ((566407 / 500000) : ℝ) = ((500000 / 566407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4453181 / 31250000) ≤ -Real.log (433593 / 500000) ∧
    -Real.log (433593 / 500000) ≤ (142501793 / 1000000000) := by
  have h := checkLog_sound (w := (66407 / 933593)) (n := 12)
    (lo := (4453181 / 31250000)) (hi := (142501793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433593) = 1/(433593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-142501793 / 1000000000) (-4453181 / 31250000) (Real.log (433593 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133976327 / 250000000) ≤ -Real.log (500000000000 / 854497354497) ∧
    -Real.log (500000000000 / 854497354497) ≤ (535905309 / 1000000000) := by
  have h := checkLog_sound (w := (354497354497 / 1354497354497)) (n := 12)
    (lo := (133976327 / 250000000)) (hi := (535905309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854497354497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854497354497 / 500000000000) = 1/(500000000000 / 854497354497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133976327 / 250000000) (535905309 / 1000000000) (Real.log (854497354497 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (854497354497 / 500000000000) = -Real.log (500000000000 / 854497354497) := by
    rw [show ((854497354497 / 500000000000) : ℝ) = ((500000000000 / 854497354497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268581781 / 500000000) ≤ -Real.log (500000000000 / 855573206249) ∧
    -Real.log (500000000000 / 855573206249) ≤ (537163563 / 1000000000) := by
  have h := checkLog_sound (w := (355573206249 / 1355573206249)) (n := 12)
    (lo := (268581781 / 500000000)) (hi := (537163563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855573206249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855573206249 / 500000000000) = 1/(500000000000 / 855573206249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (268581781 / 500000000) (537163563 / 1000000000) (Real.log (855573206249 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (855573206249 / 500000000000) = -Real.log (500000000000 / 855573206249) := by
    rw [show ((855573206249 / 500000000000) : ℝ) = ((500000000000 / 855573206249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (93891259 / 250000000) ≤ -Real.log (100000000000 / 145581377073) ∧
    -Real.log (100000000000 / 145581377073) ≤ (375565037 / 1000000000) := by
  have h := checkLog_sound (w := (45581377073 / 245581377073)) (n := 12)
    (lo := (93891259 / 250000000)) (hi := (375565037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145581377073 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145581377073 / 100000000000) = 1/(100000000000 / 145581377073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93891259 / 250000000) (375565037 / 1000000000) (Real.log (145581377073 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145581377073 / 100000000000) = -Real.log (100000000000 / 145581377073) := by
    rw [show ((145581377073 / 100000000000) : ℝ) = ((100000000000 / 145581377073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (75286601 / 200000000) ≤ -Real.log (250000000000 / 364269480021) ∧
    -Real.log (250000000000 / 364269480021) ≤ (188216503 / 500000000) := by
  have h := checkLog_sound (w := (114269480021 / 614269480021)) (n := 12)
    (lo := (75286601 / 200000000)) (hi := (188216503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364269480021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364269480021 / 250000000000) = 1/(250000000000 / 364269480021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (75286601 / 200000000) (188216503 / 500000000) (Real.log (364269480021 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (364269480021 / 250000000000) = -Real.log (250000000000 / 364269480021) := by
    rw [show ((364269480021 / 250000000000) : ℝ) = ((250000000000 / 364269480021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (266585667 / 1000000000) ≤ -Real.log (125000000000 / 163187427881) ∧
    -Real.log (125000000000 / 163187427881) ≤ (66646417 / 250000000) := by
  have h := checkLog_sound (w := (38187427881 / 288187427881)) (n := 12)
    (lo := (266585667 / 1000000000)) (hi := (66646417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163187427881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163187427881 / 125000000000) = 1/(125000000000 / 163187427881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (266585667 / 1000000000) (66646417 / 250000000) (Real.log (163187427881 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (163187427881 / 125000000000) = -Real.log (125000000000 / 163187427881) := by
    rw [show ((163187427881 / 125000000000) : ℝ) = ((125000000000 / 163187427881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133603297 / 500000000) ≤ -Real.log (2500000000 / 3265775739) ∧
    -Real.log (2500000000 / 3265775739) ≤ (53441319 / 200000000) := by
  have h := checkLog_sound (w := (765775739 / 5765775739)) (n := 12)
    (lo := (133603297 / 500000000)) (hi := (53441319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3265775739 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3265775739 / 2500000000) = 1/(2500000000 / 3265775739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133603297 / 500000000) (53441319 / 200000000) (Real.log (3265775739 / 2500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3265775739 / 2500000000) = -Real.log (2500000000 / 3265775739) := by
    rw [show ((3265775739 / 2500000000) : ℝ) = ((2500000000 / 3265775739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17796989 / 1000000000) ≤ -Real.log (245590110351 / 250000000000) ∧
    -Real.log (245590110351 / 250000000000) ≤ (1779699 / 100000000) := by
  have h := checkLog_sound (w := (4409889649 / 495590110351)) (n := 12)
    (lo := (17796989 / 1000000000)) (hi := (1779699 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245590110351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245590110351) = 1/(245590110351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1779699 / 100000000) (-17796989 / 1000000000) (Real.log (245590110351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2214327 / 125000000) ≤ -Real.log (982441364919 / 1000000000000) ∧
    -Real.log (982441364919 / 1000000000000) ≤ (17714617 / 1000000000) := by
  have h := checkLog_sound (w := (17558635081 / 1982441364919)) (n := 12)
    (lo := (2214327 / 125000000)) (hi := (17714617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982441364919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982441364919) = 1/(982441364919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17714617 / 1000000000) (-2214327 / 125000000) (Real.log (982441364919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020
