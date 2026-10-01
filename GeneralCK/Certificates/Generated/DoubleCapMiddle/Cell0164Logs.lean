import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0164
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

theorem reflection_log_1_neg : (281707227 / 1000000000) ≤ -Real.log (2560 / 3393) ∧
    -Real.log (2560 / 3393) ≤ (70426807 / 250000000) := by
  have h := checkLog_sound (w := (833 / 5953)) (n := 12)
    (lo := (281707227 / 1000000000)) (hi := (70426807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3393 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3393 / 2560) = 1/(2560 / 3393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (281707227 / 1000000000) (70426807 / 250000000) (Real.log (3393 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3393 / 2560) = -Real.log (2560 / 3393) := by
    rw [show ((3393 / 2560) : ℝ) = ((2560 / 3393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (393621459 / 1000000000) ≤ -Real.log (1727 / 2560) ∧
    -Real.log (1727 / 2560) ≤ (19681073 / 50000000) := by
  have h := checkLog_sound (w := (833 / 4287)) (n := 12)
    (lo := (393621459 / 1000000000)) (hi := (19681073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1727) = 1/(1727 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-19681073 / 50000000) (-393621459 / 1000000000) (Real.log (1727 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140632521 / 500000000) ≤ -Real.log (5120 / 6783) ∧
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


theorem reflection_log_3 : Bounds (140632521 / 500000000) (281265043 / 1000000000) (Real.log (6783 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6783 / 5120) = -Real.log (5120 / 6783) := by
    rw [show ((6783 / 5120) : ℝ) = ((5120 / 6783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (196376639 / 500000000) ≤ -Real.log (3457 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-392753279 / 1000000000) (-196376639 / 500000000) (Real.log (3457 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25062433 / 50000000) ≤ -Real.log (1280 / 2113) ∧
    -Real.log (1280 / 2113) ≤ (501248661 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 3393)) (n := 12)
    (lo := (25062433 / 50000000)) (hi := (501248661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2113 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2113 / 1280) = 1/(1280 / 2113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25062433 / 50000000) (501248661 / 1000000000) (Real.log (2113 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2113 / 1280) = -Real.log (1280 / 2113) := by
    rw [show ((2113 / 1280) : ℝ) = ((1280 / 2113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1052056761 / 1000000000) ≤ -Real.log (447 / 1280) ∧
    -Real.log (447 / 1280) ≤ (1052056763 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 447) = 1/(447 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1052056763 / 1000000000) (-1052056761 / 1000000000) (Real.log (447 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (500538517 / 1000000000) ≤ -Real.log (2560 / 4223) ∧
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


theorem reflection_log_7 : Bounds (500538517 / 1000000000) (250269259 / 500000000) (Real.log (4223 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4223 / 2560) = -Real.log (2560 / 4223) := by
    rw [show ((4223 / 2560) : ℝ) = ((2560 / 4223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (524353337 / 500000000) ≤ -Real.log (897 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-262176669 / 250000000) (-524353337 / 500000000) (Real.log (897 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76954633 / 200000000) ≤ -Real.log (1000000 / 1469281) ∧
    -Real.log (1000000 / 1469281) ≤ (192386583 / 500000000) := by
  have h := checkLog_sound (w := (469281 / 2469281)) (n := 12)
    (lo := (76954633 / 200000000)) (hi := (192386583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469281 / 1000000) = 1/(1000000 / 1469281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76954633 / 200000000) (192386583 / 500000000) (Real.log (1469281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1469281 / 1000000) = -Real.log (1000000 / 1469281) := by
    rw [show ((1469281 / 1000000) : ℝ) = ((1000000 / 1469281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (158380647 / 250000000) ≤ -Real.log (530719 / 1000000) ∧
    -Real.log (530719 / 1000000) ≤ (633522589 / 1000000000) := by
  have h := checkLog_sound (w := (469281 / 1530719)) (n := 12)
    (lo := (158380647 / 250000000)) (hi := (633522589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 530719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 530719) = 1/(530719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-633522589 / 1000000000) (-158380647 / 250000000) (Real.log (530719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (385380761 / 1000000000) ≤ -Real.log (500000 / 735087) ∧
    -Real.log (500000 / 735087) ≤ (192690381 / 500000000) := by
  have h := checkLog_sound (w := (235087 / 1235087)) (n := 12)
    (lo := (385380761 / 1000000000)) (hi := (192690381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735087 / 500000) = 1/(500000 / 735087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (385380761 / 1000000000) (192690381 / 500000000) (Real.log (735087 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735087 / 500000) = -Real.log (500000 / 735087) := by
    rw [show ((735087 / 500000) : ℝ) = ((500000 / 735087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158801657 / 250000000) ≤ -Real.log (264913 / 500000) ∧
    -Real.log (264913 / 500000) ≤ (635206629 / 1000000000) := by
  have h := checkLog_sound (w := (235087 / 764913)) (n := 12)
    (lo := (158801657 / 250000000)) (hi := (635206629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264913) = 1/(264913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-635206629 / 1000000000) (-158801657 / 250000000) (Real.log (264913 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2363693 / 7812500) ≤ -Real.log (1000000 / 1353309) ∧
    -Real.log (1000000 / 1353309) ≤ (60510541 / 200000000) := by
  have h := checkLog_sound (w := (353309 / 2353309)) (n := 12)
    (lo := (2363693 / 7812500)) (hi := (60510541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353309 / 1000000) = 1/(1000000 / 1353309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2363693 / 7812500) (60510541 / 200000000) (Real.log (1353309 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1353309 / 1000000) = -Real.log (1000000 / 1353309) := by
    rw [show ((1353309 / 1000000) : ℝ) = ((1000000 / 1353309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (435886687 / 1000000000) ≤ -Real.log (646691 / 1000000) ∧
    -Real.log (646691 / 1000000) ≤ (13621459 / 31250000) := by
  have h := checkLog_sound (w := (353309 / 1646691)) (n := 12)
    (lo := (435886687 / 1000000000)) (hi := (13621459 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646691) = 1/(646691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13621459 / 31250000) (-435886687 / 1000000000) (Real.log (646691 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (151556697 / 500000000) ≤ -Real.log (250000 / 338517) ∧
    -Real.log (250000 / 338517) ≤ (60622679 / 200000000) := by
  have h := checkLog_sound (w := (88517 / 588517)) (n := 12)
    (lo := (151556697 / 500000000)) (hi := (60622679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338517 / 250000) = 1/(250000 / 338517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (151556697 / 500000000) (60622679 / 200000000) (Real.log (338517 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (338517 / 250000) = -Real.log (250000 / 338517) := by
    rw [show ((338517 / 250000) : ℝ) = ((250000 / 338517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (437061043 / 1000000000) ≤ -Real.log (161483 / 250000) ∧
    -Real.log (161483 / 250000) ≤ (109265261 / 250000000) := by
  have h := checkLog_sound (w := (88517 / 411483)) (n := 12)
    (lo := (437061043 / 1000000000)) (hi := (109265261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161483) = 1/(161483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-109265261 / 250000000) (-437061043 / 1000000000) (Real.log (161483 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127286969 / 125000000) ≤ -Real.log (500000000000 / 1384236290767) ∧
    -Real.log (500000000000 / 1384236290767) ≤ (509147877 / 500000000) := by
  have h := checkLog_sound (w := (384236290767 / 2384236290767)) (n := 12)
    (lo := (81287143 / 250000000)) (hi := (325148573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384236290767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1384236290767 / 1000000000000) = 1/(500000000000 / 1384236290767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127286969 / 125000000) (509147877 / 500000000) (Real.log (1384236290767 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1384236290767 / 500000000000) = -Real.log (500000000000 / 1384236290767) := by
    rw [show ((1384236290767 / 500000000000) : ℝ) = ((500000000000 / 1384236290767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (255146847 / 250000000) ≤ -Real.log (250000000000 / 693706046891) ∧
    -Real.log (250000000000 / 693706046891) ≤ (102058739 / 100000000) := by
  have h := checkLog_sound (w := (193706046891 / 1193706046891)) (n := 12)
    (lo := (20465013 / 62500000)) (hi := (327440209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693706046891 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(693706046891 / 500000000000) = 1/(250000000000 / 693706046891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (255146847 / 250000000) (102058739 / 100000000) (Real.log (693706046891 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693706046891 / 250000000000) = -Real.log (250000000000 / 693706046891) := by
    rw [show ((693706046891 / 250000000000) : ℝ) = ((250000000000 / 693706046891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (738439391 / 1000000000) ≤ -Real.log (250000000000 / 523166782899) ∧
    -Real.log (250000000000 / 523166782899) ≤ (738439393 / 1000000000) := by
  have h := checkLog_sound (w := (23166782899 / 1023166782899)) (n := 12)
    (lo := (45292211 / 1000000000)) (hi := (11323053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523166782899 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523166782899 / 500000000000) = 1/(250000000000 / 523166782899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (738439391 / 1000000000) (738439393 / 1000000000) (Real.log (523166782899 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (523166782899 / 250000000000) = -Real.log (250000000000 / 523166782899) := by
    rw [show ((523166782899 / 250000000000) : ℝ) = ((250000000000 / 523166782899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (370087219 / 500000000) ≤ -Real.log (250000000000 / 524075289659) ∧
    -Real.log (250000000000 / 524075289659) ≤ (18504361 / 25000000) := by
  have h := checkLog_sound (w := (24075289659 / 1024075289659)) (n := 12)
    (lo := (23513629 / 500000000)) (hi := (47027259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((524075289659 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(524075289659 / 500000000000) = 1/(250000000000 / 524075289659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (370087219 / 500000000) (18504361 / 25000000) (Real.log (524075289659 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (524075289659 / 250000000000) = -Real.log (250000000000 / 524075289659) := by
    rw [show ((524075289659 / 250000000000) : ℝ) = ((250000000000 / 524075289659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0164
