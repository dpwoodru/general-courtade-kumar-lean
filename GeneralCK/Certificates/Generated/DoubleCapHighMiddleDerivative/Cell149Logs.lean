import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell149
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

theorem reflection_log_1_neg : (291094213 / 1000000000) ≤ -Real.log (512 / 685) ∧
    -Real.log (512 / 685) ≤ (145547107 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1197)) (n := 12)
    (lo := (291094213 / 1000000000)) (hi := (145547107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685 / 512) = 1/(512 / 685) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291094213 / 1000000000) (145547107 / 500000000) (Real.log (685 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (685 / 512) = -Real.log (512 / 685) := by
    rw [show ((685 / 512) : ℝ) = ((512 / 685) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (412324517 / 1000000000) ≤ -Real.log (339 / 512) ∧
    -Real.log (339 / 512) ≤ (206162259 / 500000000) := by
  have h := checkLog_sound (w := (173 / 851)) (n := 12)
    (lo := (412324517 / 1000000000)) (hi := (206162259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 339) = 1/(339 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-206162259 / 500000000) (-412324517 / 1000000000) (Real.log (339 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (290656161 / 1000000000) ≤ -Real.log (5120 / 6847) ∧
    -Real.log (5120 / 6847) ≤ (145328081 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 11967)) (n := 12)
    (lo := (290656161 / 1000000000)) (hi := (145328081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6847 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6847 / 5120) = 1/(5120 / 6847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (290656161 / 1000000000) (145328081 / 500000000) (Real.log (6847 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6847 / 5120) = -Real.log (5120 / 6847) := by
    rw [show ((6847 / 5120) : ℝ) = ((5120 / 6847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (411439953 / 1000000000) ≤ -Real.log (3393 / 5120) ∧
    -Real.log (3393 / 5120) ≤ (205719977 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 8513)) (n := 12)
    (lo := (411439953 / 1000000000)) (hi := (205719977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3393) = 1/(3393 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-205719977 / 500000000) (-411439953 / 1000000000) (Real.log (3393 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (107433497 / 500000000) ≤ -Real.log (1000000 / 1239697) ∧
    -Real.log (1000000 / 1239697) ≤ (42973399 / 200000000) := by
  have h := checkLog_sound (w := (239697 / 2239697)) (n := 12)
    (lo := (107433497 / 500000000)) (hi := (42973399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239697 / 1000000) = 1/(1000000 / 1239697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (107433497 / 500000000) (42973399 / 200000000) (Real.log (1239697 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1239697 / 1000000) = -Real.log (1000000 / 1239697) := by
    rw [show ((1239697 / 1000000) : ℝ) = ((1000000 / 1239697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1712739 / 6250000) ≤ -Real.log (760303 / 1000000) ∧
    -Real.log (760303 / 1000000) ≤ (274038241 / 1000000000) := by
  have h := checkLog_sound (w := (239697 / 1760303)) (n := 12)
    (lo := (1712739 / 6250000)) (hi := (274038241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760303) = 1/(760303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-274038241 / 1000000000) (-1712739 / 6250000) (Real.log (760303 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (107603671 / 500000000) ≤ -Real.log (1000000 / 1240119) ∧
    -Real.log (1000000 / 1240119) ≤ (215207343 / 1000000000) := by
  have h := checkLog_sound (w := (240119 / 2240119)) (n := 12)
    (lo := (107603671 / 500000000)) (hi := (215207343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240119 / 1000000) = 1/(1000000 / 1240119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (107603671 / 500000000) (215207343 / 1000000000) (Real.log (1240119 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1240119 / 1000000) = -Real.log (1000000 / 1240119) := by
    rw [show ((1240119 / 1000000) : ℝ) = ((1000000 / 1240119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68648359 / 250000000) ≤ -Real.log (759881 / 1000000) ∧
    -Real.log (759881 / 1000000) ≤ (274593437 / 1000000000) := by
  have h := checkLog_sound (w := (240119 / 1759881)) (n := 12)
    (lo := (68648359 / 250000000)) (hi := (274593437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759881) = 1/(759881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-274593437 / 1000000000) (-68648359 / 250000000) (Real.log (759881 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39727619 / 250000000) ≤ -Real.log (1000000 / 1172233) ∧
    -Real.log (1000000 / 1172233) ≤ (158910477 / 1000000000) := by
  have h := checkLog_sound (w := (172233 / 2172233)) (n := 12)
    (lo := (39727619 / 250000000)) (hi := (158910477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172233 / 1000000) = 1/(1000000 / 1172233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39727619 / 250000000) (158910477 / 1000000000) (Real.log (1172233 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1172233 / 1000000) = -Real.log (1000000 / 1172233) := by
    rw [show ((1172233 / 1000000) : ℝ) = ((1000000 / 1172233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (37804713 / 200000000) ≤ -Real.log (827767 / 1000000) ∧
    -Real.log (827767 / 1000000) ≤ (94511783 / 500000000) := by
  have h := checkLog_sound (w := (172233 / 1827767)) (n := 12)
    (lo := (37804713 / 200000000)) (hi := (94511783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827767) = 1/(827767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94511783 / 500000000) (-37804713 / 200000000) (Real.log (827767 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39794363 / 250000000) ≤ -Real.log (500000 / 586273) ∧
    -Real.log (500000 / 586273) ≤ (159177453 / 1000000000) := by
  have h := checkLog_sound (w := (86273 / 1086273)) (n := 12)
    (lo := (39794363 / 250000000)) (hi := (159177453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586273 / 500000) = 1/(500000 / 586273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39794363 / 250000000) (159177453 / 1000000000) (Real.log (586273 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586273 / 500000) = -Real.log (500000 / 586273) := by
    rw [show ((586273 / 500000) : ℝ) = ((500000 / 586273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94700881 / 500000000) ≤ -Real.log (413727 / 500000) ∧
    -Real.log (413727 / 500000) ≤ (189401763 / 1000000000) := by
  have h := checkLog_sound (w := (86273 / 913727)) (n := 12)
    (lo := (94700881 / 500000000)) (hi := (189401763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413727) = 1/(413727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189401763 / 1000000000) (-94700881 / 500000000) (Real.log (413727 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (702096113 / 1000000000) ≤ -Real.log (100000000000 / 201797819039) ∧
    -Real.log (100000000000 / 201797819039) ≤ (140419223 / 200000000) := by
  have h := checkLog_sound (w := (1797819039 / 401797819039)) (n := 12)
    (lo := (8948933 / 1000000000)) (hi := (4474467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201797819039 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201797819039 / 200000000000) = 1/(100000000000 / 201797819039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (702096113 / 1000000000) (140419223 / 200000000) (Real.log (201797819039 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (201797819039 / 100000000000) = -Real.log (100000000000 / 201797819039) := by
    rw [show ((201797819039 / 100000000000) : ℝ) = ((100000000000 / 201797819039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70341873 / 100000000) ≤ -Real.log (7812500000 / 15786320059) ∧
    -Real.log (7812500000 / 15786320059) ≤ (175854683 / 250000000) := by
  have h := checkLog_sound (w := (161320059 / 31411320059)) (n := 12)
    (lo := (205431 / 20000000)) (hi := (10271551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15786320059 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15786320059 / 15625000000) = 1/(7812500000 / 15786320059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (70341873 / 100000000) (175854683 / 250000000) (Real.log (15786320059 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (15786320059 / 7812500000) = -Real.log (7812500000 / 15786320059) := by
    rw [show ((15786320059 / 7812500000) : ℝ) = ((7812500000 / 15786320059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (97781047 / 200000000) ≤ -Real.log (31250000000 / 50954068641) ∧
    -Real.log (31250000000 / 50954068641) ≤ (122226309 / 250000000) := by
  have h := checkLog_sound (w := (19704068641 / 82204068641)) (n := 12)
    (lo := (97781047 / 200000000)) (hi := (122226309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50954068641 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50954068641 / 31250000000) = 1/(31250000000 / 50954068641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97781047 / 200000000) (122226309 / 250000000) (Real.log (50954068641 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50954068641 / 31250000000) = -Real.log (31250000000 / 50954068641) := by
    rw [show ((50954068641 / 31250000000) : ℝ) = ((31250000000 / 50954068641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (489800779 / 1000000000) ≤ -Real.log (781250000 / 1274993017) ∧
    -Real.log (781250000 / 1274993017) ≤ (24490039 / 50000000) := by
  have h := checkLog_sound (w := (493743017 / 2056243017)) (n := 12)
    (lo := (489800779 / 1000000000)) (hi := (24490039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274993017 / 781250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274993017 / 781250000) = 1/(781250000 / 1274993017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (489800779 / 1000000000) (24490039 / 50000000) (Real.log (1274993017 / 781250000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (1274993017 / 781250000) = -Real.log (781250000 / 1274993017) := by
    rw [show ((1274993017 / 781250000) : ℝ) = ((781250000 / 1274993017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (173967021 / 500000000) ≤ -Real.log (500000000000 / 708069420501) ∧
    -Real.log (500000000000 / 708069420501) ≤ (347934043 / 1000000000) := by
  have h := checkLog_sound (w := (208069420501 / 1208069420501)) (n := 12)
    (lo := (173967021 / 500000000)) (hi := (347934043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708069420501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708069420501 / 500000000000) = 1/(500000000000 / 708069420501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173967021 / 500000000) (347934043 / 1000000000) (Real.log (708069420501 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (708069420501 / 500000000000) = -Real.log (500000000000 / 708069420501) := by
    rw [show ((708069420501 / 500000000000) : ℝ) = ((500000000000 / 708069420501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69715843 / 200000000) ≤ -Real.log (250000000000 / 354263197713) ∧
    -Real.log (250000000000 / 354263197713) ≤ (21786201 / 62500000) := by
  have h := checkLog_sound (w := (104263197713 / 604263197713)) (n := 12)
    (lo := (69715843 / 200000000)) (hi := (21786201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354263197713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354263197713 / 250000000000) = 1/(250000000000 / 354263197713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69715843 / 200000000) (21786201 / 62500000) (Real.log (354263197713 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (354263197713 / 250000000000) = -Real.log (250000000000 / 354263197713) := by
    rw [show ((354263197713 / 250000000000) : ℝ) = ((250000000000 / 354263197713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30224309 / 1000000000) ≤ -Real.log (242556969471 / 250000000000) ∧
    -Real.log (242556969471 / 250000000000) ≤ (3022431 / 100000000) := by
  have h := checkLog_sound (w := (7443030529 / 492556969471)) (n := 12)
    (lo := (30224309 / 1000000000)) (hi := (3022431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242556969471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242556969471) = 1/(242556969471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3022431 / 100000000) (-30224309 / 1000000000) (Real.log (242556969471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (470517 / 15625000) ≤ -Real.log (970335793711 / 1000000000000) ∧
    -Real.log (970335793711 / 1000000000000) ≤ (30113089 / 1000000000) := by
  have h := checkLog_sound (w := (29664206289 / 1970335793711)) (n := 12)
    (lo := (470517 / 15625000)) (hi := (30113089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970335793711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970335793711) = 1/(970335793711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30113089 / 1000000000) (-470517 / 15625000) (Real.log (970335793711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell149
