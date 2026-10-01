import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0434
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

theorem reflection_log_1_neg : (96019903 / 500000000) ≤ -Real.log (1280 / 1551) ∧
    -Real.log (1280 / 1551) ≤ (192039807 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2831)) (n := 12)
    (lo := (96019903 / 500000000)) (hi := (192039807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1280) = 1/(1280 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (96019903 / 500000000) (192039807 / 1000000000) (Real.log (1551 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1551 / 1280) = -Real.log (1280 / 1551) := by
    rw [show ((1551 / 1280) : ℝ) = ((1280 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14868771 / 62500000) ≤ -Real.log (1009 / 1280) ∧
    -Real.log (1009 / 1280) ≤ (237900337 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2289)) (n := 12)
    (lo := (14868771 / 62500000)) (hi := (237900337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1009) = 1/(1009 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237900337 / 1000000000) (-14868771 / 62500000) (Real.log (1009 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (191797997 / 1000000000) ≤ -Real.log (2048 / 2481) ∧
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


theorem reflection_log_3 : Bounds (191797997 / 1000000000) (95898999 / 500000000) (Real.log (2481 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2481 / 2048) = -Real.log (2048 / 2481) := by
    rw [show ((2481 / 2048) : ℝ) = ((2048 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190023 / 800000) ≤ -Real.log (1615 / 2048) ∧
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


theorem reflection_log_4 : Bounds (-237528751 / 1000000000) (-190023 / 800000) (Real.log (1615 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2206717 / 6250000) ≤ -Real.log (640 / 911) ∧
    -Real.log (640 / 911) ≤ (353074721 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1551)) (n := 12)
    (lo := (2206717 / 6250000)) (hi := (353074721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911 / 640) = 1/(640 / 911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2206717 / 6250000) (353074721 / 1000000000) (Real.log (911 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (911 / 640) = -Real.log (640 / 911) := by
    rw [show ((911 / 640) : ℝ) = ((640 / 911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137667883 / 250000000) ≤ -Real.log (369 / 640) ∧
    -Real.log (369 / 640) ≤ (550671533 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 369) = 1/(369 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-550671533 / 1000000000) (-137667883 / 250000000) (Real.log (369 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (352663 / 1000000) ≤ -Real.log (1024 / 1457) ∧
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


theorem reflection_log_7 : Bounds (352663 / 1000000) (352663001 / 1000000000) (Real.log (1457 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1457 / 1024) = -Real.log (1024 / 1457) := by
    rw [show ((1457 / 1024) : ℝ) = ((1024 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (137413947 / 250000000) ≤ -Real.log (591 / 1024) ∧
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


theorem reflection_log_8 : Bounds (-549655789 / 1000000000) (-137413947 / 250000000) (Real.log (591 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13172453 / 50000000) ≤ -Real.log (1000000 / 1301411) ∧
    -Real.log (1000000 / 1301411) ≤ (263449061 / 1000000000) := by
  have h := checkLog_sound (w := (301411 / 2301411)) (n := 12)
    (lo := (13172453 / 50000000)) (hi := (263449061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301411 / 1000000) = 1/(1000000 / 1301411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13172453 / 50000000) (263449061 / 1000000000) (Real.log (1301411 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1301411 / 1000000) = -Real.log (1000000 / 1301411) := by
    rw [show ((1301411 / 1000000) : ℝ) = ((1000000 / 1301411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89673173 / 250000000) ≤ -Real.log (698589 / 1000000) ∧
    -Real.log (698589 / 1000000) ≤ (358692693 / 1000000000) := by
  have h := checkLog_sound (w := (301411 / 1698589)) (n := 12)
    (lo := (89673173 / 250000000)) (hi := (358692693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698589) = 1/(698589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-358692693 / 1000000000) (-89673173 / 250000000) (Real.log (698589 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (263776343 / 1000000000) ≤ -Real.log (1000000 / 1301837) ∧
    -Real.log (1000000 / 1301837) ≤ (32972043 / 125000000) := by
  have h := checkLog_sound (w := (301837 / 2301837)) (n := 12)
    (lo := (263776343 / 1000000000)) (hi := (32972043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301837 / 1000000) = 1/(1000000 / 1301837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (263776343 / 1000000000) (32972043 / 125000000) (Real.log (1301837 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1301837 / 1000000) = -Real.log (1000000 / 1301837) := by
    rw [show ((1301837 / 1000000) : ℝ) = ((1000000 / 1301837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (359302679 / 1000000000) ≤ -Real.log (698163 / 1000000) ∧
    -Real.log (698163 / 1000000) ≤ (8982567 / 25000000) := by
  have h := checkLog_sound (w := (301837 / 1698163)) (n := 12)
    (lo := (359302679 / 1000000000)) (hi := (8982567 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698163) = 1/(698163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8982567 / 25000000) (-359302679 / 1000000000) (Real.log (698163 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24715807 / 125000000) ≤ -Real.log (1000000 / 1218629) ∧
    -Real.log (1000000 / 1218629) ≤ (197726457 / 1000000000) := by
  have h := checkLog_sound (w := (218629 / 2218629)) (n := 12)
    (lo := (24715807 / 125000000)) (hi := (197726457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218629 / 1000000) = 1/(1000000 / 1218629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24715807 / 125000000) (197726457 / 1000000000) (Real.log (1218629 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1218629 / 1000000) = -Real.log (1000000 / 1218629) := by
    rw [show ((1218629 / 1000000) : ℝ) = ((1000000 / 1218629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (246705209 / 1000000000) ≤ -Real.log (781371 / 1000000) ∧
    -Real.log (781371 / 1000000) ≤ (24670521 / 100000000) := by
  have h := checkLog_sound (w := (218629 / 1781371)) (n := 12)
    (lo := (246705209 / 1000000000)) (hi := (24670521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781371) = 1/(781371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24670521 / 100000000) (-246705209 / 1000000000) (Real.log (781371 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (197993113 / 1000000000) ≤ -Real.log (500000 / 609477) ∧
    -Real.log (500000 / 609477) ≤ (98996557 / 500000000) := by
  have h := checkLog_sound (w := (109477 / 1109477)) (n := 12)
    (lo := (197993113 / 1000000000)) (hi := (98996557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609477 / 500000) = 1/(500000 / 609477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (197993113 / 1000000000) (98996557 / 500000000) (Real.log (609477 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609477 / 500000) = -Real.log (500000 / 609477) := by
    rw [show ((609477 / 500000) : ℝ) = ((500000 / 609477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15445077 / 62500000) ≤ -Real.log (390523 / 500000) ∧
    -Real.log (390523 / 500000) ≤ (247121233 / 1000000000) := by
  have h := checkLog_sound (w := (109477 / 890523)) (n := 12)
    (lo := (15445077 / 62500000)) (hi := (247121233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390523) = 1/(390523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247121233 / 1000000000) (-15445077 / 62500000) (Real.log (390523 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (77767719 / 125000000) ≤ -Real.log (250000000000 / 465728418283) ∧
    -Real.log (250000000000 / 465728418283) ≤ (622141753 / 1000000000) := by
  have h := checkLog_sound (w := (215728418283 / 715728418283)) (n := 12)
    (lo := (77767719 / 125000000)) (hi := (622141753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465728418283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465728418283 / 250000000000) = 1/(250000000000 / 465728418283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77767719 / 125000000) (622141753 / 1000000000) (Real.log (465728418283 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465728418283 / 250000000000) = -Real.log (250000000000 / 465728418283) := by
    rw [show ((465728418283 / 250000000000) : ℝ) = ((250000000000 / 465728418283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (623079023 / 1000000000) ≤ -Real.log (125000000000 / 233082568111) ∧
    -Real.log (125000000000 / 233082568111) ≤ (38942439 / 62500000) := by
  have h := checkLog_sound (w := (108082568111 / 358082568111)) (n := 12)
    (lo := (623079023 / 1000000000)) (hi := (38942439 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233082568111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233082568111 / 125000000000) = 1/(125000000000 / 233082568111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (623079023 / 1000000000) (38942439 / 62500000) (Real.log (233082568111 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (233082568111 / 125000000000) = -Real.log (125000000000 / 233082568111) := by
    rw [show ((233082568111 / 125000000000) : ℝ) = ((125000000000 / 233082568111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (222215833 / 500000000) ≤ -Real.log (500000000000 / 779801784299) ∧
    -Real.log (500000000000 / 779801784299) ≤ (444431667 / 1000000000) := by
  have h := checkLog_sound (w := (279801784299 / 1279801784299)) (n := 12)
    (lo := (222215833 / 500000000)) (hi := (444431667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779801784299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779801784299 / 500000000000) = 1/(500000000000 / 779801784299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (222215833 / 500000000) (444431667 / 1000000000) (Real.log (779801784299 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (779801784299 / 500000000000) = -Real.log (500000000000 / 779801784299) := by
    rw [show ((779801784299 / 500000000000) : ℝ) = ((500000000000 / 779801784299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (89022869 / 200000000) ≤ -Real.log (250000000000 / 390167160449) ∧
    -Real.log (250000000000 / 390167160449) ≤ (222557173 / 500000000) := by
  have h := checkLog_sound (w := (140167160449 / 640167160449)) (n := 12)
    (lo := (89022869 / 200000000)) (hi := (222557173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390167160449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390167160449 / 250000000000) = 1/(250000000000 / 390167160449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (89022869 / 200000000) (222557173 / 500000000) (Real.log (390167160449 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (390167160449 / 250000000000) = -Real.log (250000000000 / 390167160449) := by
    rw [show ((390167160449 / 250000000000) : ℝ) = ((250000000000 / 390167160449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0434
