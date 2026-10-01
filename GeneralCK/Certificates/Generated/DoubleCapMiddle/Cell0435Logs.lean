import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0435
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

theorem reflection_log_1_neg : (191797997 / 1000000000) ≤ -Real.log (2048 / 2481) ∧
    -Real.log (2048 / 2481) ≤ (95898999 / 500000000) := by
  have h := checkLog_sound (w := (433 / 4529)) (n := 12)
    (lo := (191797997 / 1000000000)) (hi := (95898999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2481 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2481 / 2048) = 1/(2048 / 2481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (191797997 / 1000000000) (95898999 / 500000000) (Real.log (2481 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2481 / 2048) = -Real.log (2048 / 2481) := by
    rw [show ((2481 / 2048) : ℝ) = ((2048 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190023 / 800000) ≤ -Real.log (1615 / 2048) ∧
    -Real.log (1615 / 2048) ≤ (237528751 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 3663)) (n := 12)
    (lo := (190023 / 800000)) (hi := (237528751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1615) = 1/(1615 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237528751 / 1000000000) (-190023 / 800000) (Real.log (1615 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19155613 / 100000000) ≤ -Real.log (5120 / 6201) ∧
    -Real.log (5120 / 6201) ≤ (191556131 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 11321)) (n := 12)
    (lo := (19155613 / 100000000)) (hi := (191556131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6201 / 5120) = 1/(5120 / 6201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19155613 / 100000000) (191556131 / 1000000000) (Real.log (6201 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6201 / 5120) = -Real.log (5120 / 6201) := by
    rw [show ((6201 / 5120) : ℝ) = ((5120 / 6201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (118578651 / 500000000) ≤ -Real.log (4039 / 5120) ∧
    -Real.log (4039 / 5120) ≤ (237157303 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 9159)) (n := 12)
    (lo := (118578651 / 500000000)) (hi := (237157303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4039) = 1/(4039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237157303 / 1000000000) (-118578651 / 500000000) (Real.log (4039 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (352663 / 1000000) ≤ -Real.log (1024 / 1457) ∧
    -Real.log (1024 / 1457) ≤ (352663001 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2481)) (n := 12)
    (lo := (352663 / 1000000)) (hi := (352663001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1024) = 1/(1024 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (352663 / 1000000) (352663001 / 1000000000) (Real.log (1457 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1457 / 1024) = -Real.log (1024 / 1457) := by
    rw [show ((1457 / 1024) : ℝ) = ((1024 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137413947 / 250000000) ≤ -Real.log (591 / 1024) ∧
    -Real.log (591 / 1024) ≤ (549655789 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1615)) (n := 12)
    (lo := (137413947 / 250000000)) (hi := (549655789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 591) = 1/(591 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-549655789 / 1000000000) (-137413947 / 250000000) (Real.log (591 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35225111 / 100000000) ≤ -Real.log (2560 / 3641) ∧
    -Real.log (2560 / 3641) ≤ (352251111 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 6201)) (n := 12)
    (lo := (35225111 / 100000000)) (hi := (352251111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3641 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3641 / 2560) = 1/(2560 / 3641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35225111 / 100000000) (352251111 / 1000000000) (Real.log (3641 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3641 / 2560) = -Real.log (2560 / 3641) := by
    rw [show ((3641 / 2560) : ℝ) = ((2560 / 3641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (274320537 / 500000000) ≤ -Real.log (1479 / 2560) ∧
    -Real.log (1479 / 2560) ≤ (21945643 / 40000000) := by
  have h := checkLog_sound (w := (1081 / 4039)) (n := 12)
    (lo := (274320537 / 500000000)) (hi := (21945643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1479) = 1/(1479 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-21945643 / 40000000) (-274320537 / 500000000) (Real.log (1479 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131561219 / 500000000) ≤ -Real.log (500000 / 650493) ∧
    -Real.log (500000 / 650493) ≤ (263122439 / 1000000000) := by
  have h := checkLog_sound (w := (150493 / 1150493)) (n := 12)
    (lo := (131561219 / 500000000)) (hi := (263122439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650493 / 500000) = 1/(500000 / 650493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131561219 / 500000000) (263122439 / 1000000000) (Real.log (650493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (650493 / 500000) = -Real.log (500000 / 650493) := by
    rw [show ((650493 / 500000) : ℝ) = ((500000 / 650493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89521127 / 250000000) ≤ -Real.log (349507 / 500000) ∧
    -Real.log (349507 / 500000) ≤ (358084509 / 1000000000) := by
  have h := checkLog_sound (w := (150493 / 849507)) (n := 12)
    (lo := (89521127 / 250000000)) (hi := (358084509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349507) = 1/(349507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-358084509 / 1000000000) (-89521127 / 250000000) (Real.log (349507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65862457 / 250000000) ≤ -Real.log (250000 / 325353) ∧
    -Real.log (250000 / 325353) ≤ (263449829 / 1000000000) := by
  have h := checkLog_sound (w := (75353 / 575353)) (n := 12)
    (lo := (65862457 / 250000000)) (hi := (263449829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325353 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325353 / 250000) = 1/(250000 / 325353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65862457 / 250000000) (263449829 / 1000000000) (Real.log (325353 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (325353 / 250000) = -Real.log (250000 / 325353) := by
    rw [show ((325353 / 250000) : ℝ) = ((250000 / 325353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (358694123 / 1000000000) ≤ -Real.log (174647 / 250000) ∧
    -Real.log (174647 / 250000) ≤ (89673531 / 250000000) := by
  have h := checkLog_sound (w := (75353 / 424647)) (n := 12)
    (lo := (358694123 / 1000000000)) (hi := (89673531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174647) = 1/(174647 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89673531 / 250000000) (-358694123 / 1000000000) (Real.log (174647 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49365137 / 250000000) ≤ -Real.log (200000 / 243661) ∧
    -Real.log (200000 / 243661) ≤ (197460549 / 1000000000) := by
  have h := checkLog_sound (w := (43661 / 443661)) (n := 12)
    (lo := (49365137 / 250000000)) (hi := (197460549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243661 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243661 / 200000) = 1/(200000 / 243661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49365137 / 250000000) (197460549 / 1000000000) (Real.log (243661 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (243661 / 200000) = -Real.log (200000 / 243661) := by
    rw [show ((243661 / 200000) : ℝ) = ((200000 / 243661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3078633 / 12500000) ≤ -Real.log (156339 / 200000) ∧
    -Real.log (156339 / 200000) ≤ (246290641 / 1000000000) := by
  have h := checkLog_sound (w := (43661 / 356339)) (n := 12)
    (lo := (3078633 / 12500000)) (hi := (246290641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156339) = 1/(156339 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-246290641 / 1000000000) (-3078633 / 12500000) (Real.log (156339 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (49431819 / 250000000) ≤ -Real.log (100000 / 121863) ∧
    -Real.log (100000 / 121863) ≤ (197727277 / 1000000000) := by
  have h := checkLog_sound (w := (21863 / 221863)) (n := 12)
    (lo := (49431819 / 250000000)) (hi := (197727277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121863 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121863 / 100000) = 1/(100000 / 121863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49431819 / 250000000) (197727277 / 1000000000) (Real.log (121863 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (121863 / 100000) = -Real.log (100000 / 121863) := by
    rw [show ((121863 / 100000) : ℝ) = ((100000 / 121863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (246706489 / 1000000000) ≤ -Real.log (78137 / 100000) ∧
    -Real.log (78137 / 100000) ≤ (24670649 / 100000000) := by
  have h := checkLog_sound (w := (21863 / 178137)) (n := 12)
    (lo := (246706489 / 1000000000)) (hi := (24670649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78137) = 1/(78137 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-24670649 / 100000000) (-246706489 / 1000000000) (Real.log (78137 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (310603473 / 500000000) ≤ -Real.log (250000000000 / 465293255929) ∧
    -Real.log (250000000000 / 465293255929) ≤ (621206947 / 1000000000) := by
  have h := checkLog_sound (w := (215293255929 / 715293255929)) (n := 12)
    (lo := (310603473 / 500000000)) (hi := (621206947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465293255929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465293255929 / 250000000000) = 1/(250000000000 / 465293255929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (310603473 / 500000000) (621206947 / 1000000000) (Real.log (465293255929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465293255929 / 250000000000) = -Real.log (250000000000 / 465293255929) := by
    rw [show ((465293255929 / 250000000000) : ℝ) = ((250000000000 / 465293255929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38883997 / 62500000) ≤ -Real.log (250000000000 / 465729442819) ∧
    -Real.log (250000000000 / 465729442819) ≤ (622143953 / 1000000000) := by
  have h := checkLog_sound (w := (215729442819 / 715729442819)) (n := 12)
    (lo := (38883997 / 62500000)) (hi := (622143953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465729442819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465729442819 / 250000000000) = 1/(250000000000 / 465729442819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38883997 / 62500000) (622143953 / 1000000000) (Real.log (465729442819 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (465729442819 / 250000000000) = -Real.log (250000000000 / 465729442819) := by
    rw [show ((465729442819 / 250000000000) : ℝ) = ((250000000000 / 465729442819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (110937797 / 250000000) ≤ -Real.log (125000000000 / 194817831763) ∧
    -Real.log (125000000000 / 194817831763) ≤ (443751189 / 1000000000) := by
  have h := checkLog_sound (w := (69817831763 / 319817831763)) (n := 12)
    (lo := (110937797 / 250000000)) (hi := (443751189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194817831763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194817831763 / 125000000000) = 1/(125000000000 / 194817831763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (110937797 / 250000000) (443751189 / 1000000000) (Real.log (194817831763 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (194817831763 / 125000000000) = -Real.log (125000000000 / 194817831763) := by
    rw [show ((194817831763 / 125000000000) : ℝ) = ((125000000000 / 194817831763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222216883 / 500000000) ≤ -Real.log (100000000000 / 155960684439) ∧
    -Real.log (100000000000 / 155960684439) ≤ (444433767 / 1000000000) := by
  have h := checkLog_sound (w := (55960684439 / 255960684439)) (n := 12)
    (lo := (222216883 / 500000000)) (hi := (444433767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155960684439 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155960684439 / 100000000000) = 1/(100000000000 / 155960684439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222216883 / 500000000) (444433767 / 1000000000) (Real.log (155960684439 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (155960684439 / 100000000000) = -Real.log (100000000000 / 155960684439) := by
    rw [show ((155960684439 / 100000000000) : ℝ) = ((100000000000 / 155960684439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0435
