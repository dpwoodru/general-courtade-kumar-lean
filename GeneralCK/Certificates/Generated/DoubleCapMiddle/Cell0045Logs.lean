import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0045
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

theorem reflection_log_1_neg : (7570869 / 20000000) ≤ -Real.log (1280 / 1869) ∧
    -Real.log (1280 / 1869) ≤ (378543451 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 3149)) (n := 12)
    (lo := (7570869 / 20000000)) (hi := (378543451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1280) = 1/(1280 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7570869 / 20000000) (378543451 / 1000000000) (Real.log (1869 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1869 / 1280) = -Real.log (1280 / 1869) := by
    rw [show ((1869 / 1280) : ℝ) = ((1280 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (616475533 / 1000000000) ≤ -Real.log (691 / 1280) ∧
    -Real.log (691 / 1280) ≤ (308237767 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1971)) (n := 12)
    (lo := (616475533 / 1000000000)) (hi := (308237767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 691) = 1/(691 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-308237767 / 500000000) (-616475533 / 1000000000) (Real.log (691 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4721757 / 12500000) ≤ -Real.log (512 / 747) ∧
    -Real.log (512 / 747) ≤ (377740561 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 1259)) (n := 12)
    (lo := (4721757 / 12500000)) (hi := (377740561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 512) = 1/(512 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4721757 / 12500000) (377740561 / 1000000000) (Real.log (747 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (747 / 512) = -Real.log (512 / 747) := by
    rw [show ((747 / 512) : ℝ) = ((512 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307153559 / 500000000) ≤ -Real.log (277 / 512) ∧
    -Real.log (277 / 512) ≤ (614307119 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 789)) (n := 12)
    (lo := (307153559 / 500000000)) (hi := (614307119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 277) = 1/(277 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-614307119 / 1000000000) (-307153559 / 500000000) (Real.log (277 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (652487933 / 1000000000) ≤ -Real.log (640 / 1229) ∧
    -Real.log (640 / 1229) ≤ (326243967 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1869)) (n := 12)
    (lo := (652487933 / 1000000000)) (hi := (326243967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 640) = 1/(640 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (652487933 / 1000000000) (326243967 / 500000000) (Real.log (1229 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229 / 640) = -Real.log (640 / 1229) := by
    rw [show ((1229 / 640) : ℝ) = ((640 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2529642541 / 1000000000) ≤ -Real.log (51 / 640) ∧
    -Real.log (51 / 640) ≤ (505928509 / 200000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 51) = 1/(51 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-505928509 / 200000000) (-2529642541 / 1000000000) (Real.log (51 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (651266683 / 1000000000) ≤ -Real.log (256 / 491) ∧
    -Real.log (256 / 491) ≤ (162816671 / 250000000) := by
  have h := checkLog_sound (w := (235 / 747)) (n := 12)
    (lo := (651266683 / 1000000000)) (hi := (162816671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 256) = 1/(256 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (651266683 / 1000000000) (162816671 / 250000000) (Real.log (491 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (491 / 256) = -Real.log (256 / 491) := by
    rw [show ((491 / 256) : ℝ) = ((256 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (500131001 / 200000000) ≤ -Real.log (21 / 256) ∧
    -Real.log (21 / 256) ≤ (2500655009 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 21) = 1/(21 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2500655009 / 1000000000) (-500131001 / 200000000) (Real.log (21 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131030459 / 250000000) ≤ -Real.log (40000 / 67559) ∧
    -Real.log (40000 / 67559) ≤ (524121837 / 1000000000) := by
  have h := checkLog_sound (w := (27559 / 107559)) (n := 12)
    (lo := (131030459 / 250000000)) (hi := (524121837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67559 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67559 / 40000) = 1/(40000 / 67559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131030459 / 250000000) (524121837 / 1000000000) (Real.log (67559 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67559 / 40000) = -Real.log (40000 / 67559) := by
    rw [show ((67559 / 40000) : ℝ) = ((40000 / 67559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1167881983 / 1000000000) ≤ -Real.log (12441 / 40000) ∧
    -Real.log (12441 / 40000) ≤ (233576397 / 200000000) := by
  have h := checkLog_sound (w := (7559 / 32441)) (n := 12)
    (lo := (474734803 / 1000000000)) (hi := (118683701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 12441) = 1/(12441 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-233576397 / 200000000) (-1167881983 / 1000000000) (Real.log (12441 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (525417049 / 1000000000) ≤ -Real.log (250000 / 422791) ∧
    -Real.log (250000 / 422791) ≤ (10508341 / 20000000) := by
  have h := checkLog_sound (w := (172791 / 672791)) (n := 12)
    (lo := (525417049 / 1000000000)) (hi := (10508341 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422791 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422791 / 250000) = 1/(250000 / 422791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (525417049 / 1000000000) (10508341 / 20000000) (Real.log (422791 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (422791 / 250000) = -Real.log (250000 / 422791) := by
    rw [show ((422791 / 250000) : ℝ) = ((250000 / 422791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (587472443 / 500000000) ≤ -Real.log (77209 / 250000) ∧
    -Real.log (77209 / 250000) ≤ (146868111 / 125000000) := by
  have h := checkLog_sound (w := (47791 / 202209)) (n := 12)
    (lo := (240898853 / 500000000)) (hi := (481797707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 77209) = 1/(77209 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-146868111 / 125000000) (-587472443 / 500000000) (Real.log (77209 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222270469 / 500000000) ≤ -Real.log (500000 / 779887) ∧
    -Real.log (500000 / 779887) ≤ (444540939 / 1000000000) := by
  have h := checkLog_sound (w := (279887 / 1279887)) (n := 12)
    (lo := (222270469 / 500000000)) (hi := (444540939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779887 / 500000) = 1/(500000 / 779887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222270469 / 500000000) (444540939 / 1000000000) (Real.log (779887 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (779887 / 500000) = -Real.log (500000 / 779887) := by
    rw [show ((779887 / 500000) : ℝ) = ((500000 / 779887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (820467047 / 1000000000) ≤ -Real.log (220113 / 500000) ∧
    -Real.log (220113 / 500000) ≤ (820467049 / 1000000000) := by
  have h := checkLog_sound (w := (29887 / 470113)) (n := 12)
    (lo := (127319867 / 1000000000)) (hi := (31829967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220113) = 1/(220113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-820467049 / 1000000000) (-820467047 / 1000000000) (Real.log (220113 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (55751403 / 125000000) ≤ -Real.log (1000000 / 1562069) ∧
    -Real.log (1000000 / 1562069) ≤ (17840449 / 40000000) := by
  have h := checkLog_sound (w := (562069 / 2562069)) (n := 12)
    (lo := (55751403 / 125000000)) (hi := (17840449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562069 / 1000000) = 1/(1000000 / 1562069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (55751403 / 125000000) (17840449 / 40000000) (Real.log (1562069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1562069 / 1000000) = -Real.log (1000000 / 1562069) := by
    rw [show ((1562069 / 1000000) : ℝ) = ((1000000 / 1562069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (412846957 / 500000000) ≤ -Real.log (437931 / 1000000) ∧
    -Real.log (437931 / 1000000) ≤ (206423479 / 250000000) := by
  have h := checkLog_sound (w := (62069 / 937931)) (n := 12)
    (lo := (66273367 / 500000000)) (hi := (26509347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437931) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 437931) = 1/(437931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-206423479 / 250000000) (-412846957 / 500000000) (Real.log (437931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1692003819 / 1000000000) ≤ -Real.log (62500000000 / 339396953621) ∧
    -Real.log (62500000000 / 339396953621) ≤ (846001911 / 500000000) := by
  have h := checkLog_sound (w := (89396953621 / 589396953621)) (n := 12)
    (lo := (305709459 / 1000000000)) (hi := (15285473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339396953621 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(339396953621 / 250000000000) = 1/(62500000000 / 339396953621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1692003819 / 1000000000) (846001911 / 500000000) (Real.log (339396953621 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339396953621 / 62500000000) = -Real.log (62500000000 / 339396953621) := by
    rw [show ((339396953621 / 62500000000) : ℝ) = ((62500000000 / 339396953621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (340072387 / 200000000) ≤ -Real.log (250000000000 / 1368982243003) ∧
    -Real.log (250000000000 / 1368982243003) ≤ (850180969 / 500000000) := by
  have h := checkLog_sound (w := (368982243003 / 2368982243003)) (n := 12)
    (lo := (12562703 / 40000000)) (hi := (39258447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1368982243003 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1368982243003 / 1000000000000) = 1/(250000000000 / 1368982243003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (340072387 / 200000000) (850180969 / 500000000) (Real.log (1368982243003 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1368982243003 / 250000000000) = -Real.log (250000000000 / 1368982243003) := by
    rw [show ((1368982243003 / 250000000000) : ℝ) = ((250000000000 / 1368982243003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253001597 / 200000000) ≤ -Real.log (500000000000 / 1771560516643) ∧
    -Real.log (500000000000 / 1771560516643) ≤ (1265007987 / 1000000000) := by
  have h := checkLog_sound (w := (771560516643 / 2771560516643)) (n := 12)
    (lo := (114372161 / 200000000)) (hi := (285930403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771560516643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1771560516643 / 1000000000000) = 1/(500000000000 / 1771560516643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253001597 / 200000000) (1265007987 / 1000000000) (Real.log (1771560516643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1771560516643 / 500000000000) = -Real.log (500000000000 / 1771560516643) := by
    rw [show ((1771560516643 / 500000000000) : ℝ) = ((500000000000 / 1771560516643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1271705139 / 1000000000) ≤ -Real.log (50000000000 / 178346474673) ∧
    -Real.log (50000000000 / 178346474673) ≤ (1271705141 / 1000000000) := by
  have h := checkLog_sound (w := (78346474673 / 278346474673)) (n := 12)
    (lo := (578557959 / 1000000000)) (hi := (14463949 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178346474673 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(178346474673 / 100000000000) = 1/(50000000000 / 178346474673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1271705139 / 1000000000) (1271705141 / 1000000000) (Real.log (178346474673 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (178346474673 / 50000000000) = -Real.log (50000000000 / 178346474673) := by
    rw [show ((178346474673 / 50000000000) : ℝ) = ((50000000000 / 178346474673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0045
