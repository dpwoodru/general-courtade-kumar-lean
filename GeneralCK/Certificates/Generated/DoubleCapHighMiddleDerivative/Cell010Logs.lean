import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell010
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

theorem reflection_log_1_neg : (228286553 / 1000000000) ≤ -Real.log (5120 / 6433) ∧
    -Real.log (5120 / 6433) ≤ (114143277 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 11553)) (n := 12)
    (lo := (228286553 / 1000000000)) (hi := (114143277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6433 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6433 / 5120) = 1/(5120 / 6433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (228286553 / 1000000000) (114143277 / 500000000) (Real.log (6433 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6433 / 5120) = -Real.log (5120 / 6433) := by
    rw [show ((6433 / 5120) : ℝ) = ((5120 / 6433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (296312961 / 1000000000) ≤ -Real.log (3807 / 5120) ∧
    -Real.log (3807 / 5120) ≤ (148156481 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 8927)) (n := 12)
    (lo := (296312961 / 1000000000)) (hi := (148156481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3807) = 1/(3807 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-148156481 / 500000000) (-296312961 / 1000000000) (Real.log (3807 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227820099 / 1000000000) ≤ -Real.log (512 / 643) ∧
    -Real.log (512 / 643) ≤ (2278201 / 10000000) := by
  have h := checkLog_sound (w := (131 / 1155)) (n := 12)
    (lo := (227820099 / 1000000000)) (hi := (2278201 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643 / 512) = 1/(512 / 643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227820099 / 1000000000) (2278201 / 10000000) (Real.log (643 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (643 / 512) = -Real.log (512 / 643) := by
    rw [show ((643 / 512) : ℝ) = ((512 / 643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295525249 / 1000000000) ≤ -Real.log (381 / 512) ∧
    -Real.log (381 / 512) ≤ (1182101 / 4000000) := by
  have h := checkLog_sound (w := (131 / 893)) (n := 12)
    (lo := (295525249 / 1000000000)) (hi := (1182101 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 381) = 1/(381 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1182101 / 4000000) (-295525249 / 1000000000) (Real.log (381 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166723029 / 1000000000) ≤ -Real.log (1000000 / 1181427) ∧
    -Real.log (1000000 / 1181427) ≤ (16672303 / 100000000) := by
  have h := checkLog_sound (w := (181427 / 2181427)) (n := 12)
    (lo := (166723029 / 1000000000)) (hi := (16672303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181427 / 1000000) = 1/(1000000 / 1181427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166723029 / 1000000000) (16672303 / 100000000) (Real.log (1181427 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181427 / 1000000) = -Real.log (1000000 / 1181427) := by
    rw [show ((1181427 / 1000000) : ℝ) = ((1000000 / 1181427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (100096349 / 500000000) ≤ -Real.log (818573 / 1000000) ∧
    -Real.log (818573 / 1000000) ≤ (200192699 / 1000000000) := by
  have h := checkLog_sound (w := (181427 / 1818573)) (n := 12)
    (lo := (100096349 / 500000000)) (hi := (200192699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818573) = 1/(818573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-200192699 / 1000000000) (-100096349 / 500000000) (Real.log (818573 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83538811 / 500000000) ≤ -Real.log (500000 / 590923) ∧
    -Real.log (500000 / 590923) ≤ (167077623 / 1000000000) := by
  have h := checkLog_sound (w := (90923 / 1090923)) (n := 12)
    (lo := (83538811 / 500000000)) (hi := (167077623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590923 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590923 / 500000) = 1/(500000 / 590923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83538811 / 500000000) (167077623 / 1000000000) (Real.log (590923 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (590923 / 500000) = -Real.log (500000 / 590923) := by
    rw [show ((590923 / 500000) : ℝ) = ((500000 / 590923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25088087 / 125000000) ≤ -Real.log (409077 / 500000) ∧
    -Real.log (409077 / 500000) ≤ (200704697 / 1000000000) := by
  have h := checkLog_sound (w := (90923 / 909077)) (n := 12)
    (lo := (25088087 / 125000000)) (hi := (200704697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409077) = 1/(409077 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-200704697 / 1000000000) (-25088087 / 125000000) (Real.log (409077 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12174761 / 100000000) ≤ -Real.log (1000000 / 1129469) ∧
    -Real.log (1000000 / 1129469) ≤ (121747611 / 1000000000) := by
  have h := checkLog_sound (w := (129469 / 2129469)) (n := 12)
    (lo := (12174761 / 100000000)) (hi := (121747611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129469 / 1000000) = 1/(1000000 / 1129469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12174761 / 100000000) (121747611 / 1000000000) (Real.log (1129469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1129469 / 1000000) = -Real.log (1000000 / 1129469) := by
    rw [show ((1129469 / 1000000) : ℝ) = ((1000000 / 1129469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34662977 / 250000000) ≤ -Real.log (870531 / 1000000) ∧
    -Real.log (870531 / 1000000) ≤ (138651909 / 1000000000) := by
  have h := checkLog_sound (w := (129469 / 1870531)) (n := 12)
    (lo := (34662977 / 250000000)) (hi := (138651909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870531) = 1/(870531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-138651909 / 1000000000) (-34662977 / 250000000) (Real.log (870531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30504403 / 250000000) ≤ -Real.log (500000 / 564887) ∧
    -Real.log (500000 / 564887) ≤ (122017613 / 1000000000) := by
  have h := checkLog_sound (w := (64887 / 1064887)) (n := 12)
    (lo := (30504403 / 250000000)) (hi := (122017613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564887 / 500000) = 1/(500000 / 564887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30504403 / 250000000) (122017613 / 1000000000) (Real.log (564887 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (564887 / 500000) = -Real.log (500000 / 564887) := by
    rw [show ((564887 / 500000) : ℝ) = ((500000 / 564887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13900233 / 100000000) ≤ -Real.log (435113 / 500000) ∧
    -Real.log (435113 / 500000) ≤ (139002331 / 1000000000) := by
  have h := checkLog_sound (w := (64887 / 935113)) (n := 12)
    (lo := (13900233 / 100000000)) (hi := (139002331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435113) = 1/(435113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139002331 / 1000000000) (-13900233 / 100000000) (Real.log (435113 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (523345349 / 1000000000) ≤ -Real.log (500000000000 / 843832020997) ∧
    -Real.log (500000000000 / 843832020997) ≤ (10466907 / 20000000) := by
  have h := checkLog_sound (w := (343832020997 / 1343832020997)) (n := 12)
    (lo := (523345349 / 1000000000)) (hi := (10466907 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843832020997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843832020997 / 500000000000) = 1/(500000000000 / 843832020997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (523345349 / 1000000000) (10466907 / 20000000) (Real.log (843832020997 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (843832020997 / 500000000000) = -Real.log (500000000000 / 843832020997) := by
    rw [show ((843832020997 / 500000000000) : ℝ) = ((500000000000 / 843832020997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (104919903 / 200000000) ≤ -Real.log (250000000000 / 422445495141) ∧
    -Real.log (250000000000 / 422445495141) ≤ (131149879 / 250000000) := by
  have h := checkLog_sound (w := (172445495141 / 672445495141)) (n := 12)
    (lo := (104919903 / 200000000)) (hi := (131149879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422445495141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422445495141 / 250000000000) = 1/(250000000000 / 422445495141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (104919903 / 200000000) (131149879 / 250000000) (Real.log (422445495141 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (422445495141 / 250000000000) = -Real.log (250000000000 / 422445495141) := by
    rw [show ((422445495141 / 250000000000) : ℝ) = ((250000000000 / 422445495141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22932233 / 62500000) ≤ -Real.log (125000000000 / 180409535863) ∧
    -Real.log (125000000000 / 180409535863) ≤ (366915729 / 1000000000) := by
  have h := checkLog_sound (w := (55409535863 / 305409535863)) (n := 12)
    (lo := (22932233 / 62500000)) (hi := (366915729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180409535863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180409535863 / 125000000000) = 1/(125000000000 / 180409535863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22932233 / 62500000) (366915729 / 1000000000) (Real.log (180409535863 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (180409535863 / 125000000000) = -Real.log (125000000000 / 180409535863) := by
    rw [show ((180409535863 / 125000000000) : ℝ) = ((125000000000 / 180409535863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (183891159 / 500000000) ≤ -Real.log (500000000000 / 722263779191) ∧
    -Real.log (500000000000 / 722263779191) ≤ (367782319 / 1000000000) := by
  have h := checkLog_sound (w := (222263779191 / 1222263779191)) (n := 12)
    (lo := (183891159 / 500000000)) (hi := (367782319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722263779191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722263779191 / 500000000000) = 1/(500000000000 / 722263779191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (183891159 / 500000000) (367782319 / 1000000000) (Real.log (722263779191 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (722263779191 / 500000000000) = -Real.log (500000000000 / 722263779191) := by
    rw [show ((722263779191 / 500000000000) : ℝ) = ((500000000000 / 722263779191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (260399519 / 1000000000) ≤ -Real.log (500000000000 / 648724169501) ∧
    -Real.log (500000000000 / 648724169501) ≤ (1627497 / 6250000) := by
  have h := checkLog_sound (w := (148724169501 / 1148724169501)) (n := 12)
    (lo := (260399519 / 1000000000)) (hi := (1627497 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648724169501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648724169501 / 500000000000) = 1/(500000000000 / 648724169501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (260399519 / 1000000000) (1627497 / 6250000) (Real.log (648724169501 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (648724169501 / 500000000000) = -Real.log (500000000000 / 648724169501) := by
    rw [show ((648724169501 / 500000000000) : ℝ) = ((500000000000 / 648724169501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261019943 / 1000000000) ≤ -Real.log (500000000000 / 649126778561) ∧
    -Real.log (500000000000 / 649126778561) ≤ (32627493 / 125000000) := by
  have h := checkLog_sound (w := (149126778561 / 1149126778561)) (n := 12)
    (lo := (261019943 / 1000000000)) (hi := (32627493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649126778561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649126778561 / 500000000000) = 1/(500000000000 / 649126778561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261019943 / 1000000000) (32627493 / 125000000) (Real.log (649126778561 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649126778561 / 500000000000) = -Real.log (500000000000 / 649126778561) := by
    rw [show ((649126778561 / 500000000000) : ℝ) = ((500000000000 / 649126778561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8492359 / 500000000) ≤ -Real.log (245789677231 / 250000000000) ∧
    -Real.log (245789677231 / 250000000000) ≤ (16984719 / 1000000000) := by
  have h := checkLog_sound (w := (4210322769 / 495789677231)) (n := 12)
    (lo := (8492359 / 500000000)) (hi := (16984719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245789677231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245789677231) = 1/(245789677231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16984719 / 1000000000) (-8492359 / 500000000) (Real.log (245789677231 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16904297 / 1000000000) ≤ -Real.log (983237778039 / 1000000000000) ∧
    -Real.log (983237778039 / 1000000000000) ≤ (8452149 / 500000000) := by
  have h := checkLog_sound (w := (16762221961 / 1983237778039)) (n := 12)
    (lo := (16904297 / 1000000000)) (hi := (8452149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983237778039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983237778039) = 1/(983237778039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8452149 / 500000000) (-16904297 / 1000000000) (Real.log (983237778039 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell010
