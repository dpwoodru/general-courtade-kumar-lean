import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0231
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

theorem reflection_log_1_neg : (31454987 / 125000000) ≤ -Real.log (1024 / 1317) ∧
    -Real.log (1024 / 1317) ≤ (251639897 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2341)) (n := 12)
    (lo := (31454987 / 125000000)) (hi := (251639897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1024) = 1/(1024 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31454987 / 125000000) (251639897 / 1000000000) (Real.log (1317 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1317 / 1024) = -Real.log (1024 / 1317) := by
    rw [show ((1317 / 1024) : ℝ) = ((1024 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (67411669 / 200000000) ≤ -Real.log (731 / 1024) ∧
    -Real.log (731 / 1024) ≤ (168529173 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1755)) (n := 12)
    (lo := (67411669 / 200000000)) (hi := (168529173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 731) = 1/(731 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-168529173 / 500000000) (-67411669 / 200000000) (Real.log (731 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (251184211 / 1000000000) ≤ -Real.log (2560 / 3291) ∧
    -Real.log (2560 / 3291) ≤ (62796053 / 250000000) := by
  have h := checkLog_sound (w := (731 / 5851)) (n := 12)
    (lo := (251184211 / 1000000000)) (hi := (62796053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3291 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3291 / 2560) = 1/(2560 / 3291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (251184211 / 1000000000) (62796053 / 250000000) (Real.log (3291 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3291 / 2560) = -Real.log (2560 / 3291) := by
    rw [show ((3291 / 2560) : ℝ) = ((2560 / 3291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (336237889 / 1000000000) ≤ -Real.log (1829 / 2560) ∧
    -Real.log (1829 / 2560) ≤ (33623789 / 100000000) := by
  have h := checkLog_sound (w := (731 / 4389)) (n := 12)
    (lo := (336237889 / 1000000000)) (hi := (33623789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1829) = 1/(1829 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33623789 / 100000000) (-336237889 / 1000000000) (Real.log (1829 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113129413 / 250000000) ≤ -Real.log (512 / 805) ∧
    -Real.log (512 / 805) ≤ (452517653 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1317)) (n := 12)
    (lo := (113129413 / 250000000)) (hi := (452517653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805 / 512) = 1/(512 / 805) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113129413 / 250000000) (452517653 / 1000000000) (Real.log (805 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (805 / 512) = -Real.log (512 / 805) := by
    rw [show ((805 / 512) : ℝ) = ((512 / 805) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (424626447 / 500000000) ≤ -Real.log (219 / 512) ∧
    -Real.log (219 / 512) ≤ (26539153 / 31250000) := by
  have h := checkLog_sound (w := (37 / 475)) (n := 12)
    (lo := (78052857 / 500000000)) (hi := (31221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 219) = 1/(219 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26539153 / 31250000) (-424626447 / 500000000) (Real.log (219 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3529469 / 7812500) ≤ -Real.log (1280 / 2011) ∧
    -Real.log (1280 / 2011) ≤ (451772033 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 3291)) (n := 12)
    (lo := (3529469 / 7812500)) (hi := (451772033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2011 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2011 / 1280) = 1/(1280 / 2011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3529469 / 7812500) (451772033 / 1000000000) (Real.log (2011 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2011 / 1280) = -Real.log (1280 / 2011) := by
    rw [show ((2011 / 1280) : ℝ) = ((1280 / 2011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (423258457 / 500000000) ≤ -Real.log (549 / 1280) ∧
    -Real.log (549 / 1280) ≤ (211629229 / 250000000) := by
  have h := checkLog_sound (w := (91 / 1189)) (n := 12)
    (lo := (76684867 / 500000000)) (hi := (30673947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 549) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 549) = 1/(549 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-211629229 / 250000000) (-423258457 / 500000000) (Real.log (549 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8593643 / 25000000) ≤ -Real.log (50000 / 70511) ∧
    -Real.log (50000 / 70511) ≤ (343745721 / 1000000000) := by
  have h := checkLog_sound (w := (20511 / 120511)) (n := 12)
    (lo := (8593643 / 25000000)) (hi := (343745721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70511 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70511 / 50000) = 1/(50000 / 70511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8593643 / 25000000) (343745721 / 1000000000) (Real.log (70511 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (70511 / 50000) = -Real.log (50000 / 70511) := by
    rw [show ((70511 / 50000) : ℝ) = ((50000 / 70511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (132001423 / 250000000) ≤ -Real.log (29489 / 50000) ∧
    -Real.log (29489 / 50000) ≤ (528005693 / 1000000000) := by
  have h := checkLog_sound (w := (20511 / 79489)) (n := 12)
    (lo := (132001423 / 250000000)) (hi := (528005693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 29489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 29489) = 1/(29489 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-528005693 / 1000000000) (-132001423 / 250000000) (Real.log (29489 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (344364581 / 1000000000) ≤ -Real.log (1000000 / 1411093) ∧
    -Real.log (1000000 / 1411093) ≤ (172182291 / 500000000) := by
  have h := checkLog_sound (w := (411093 / 2411093)) (n := 12)
    (lo := (344364581 / 1000000000)) (hi := (172182291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411093 / 1000000) = 1/(1000000 / 1411093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (344364581 / 1000000000) (172182291 / 500000000) (Real.log (1411093 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1411093 / 1000000) = -Real.log (1000000 / 1411093) := by
    rw [show ((1411093 / 1000000) : ℝ) = ((1000000 / 1411093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (264743501 / 500000000) ≤ -Real.log (588907 / 1000000) ∧
    -Real.log (588907 / 1000000) ≤ (529487003 / 1000000000) := by
  have h := checkLog_sound (w := (411093 / 1588907)) (n := 12)
    (lo := (264743501 / 500000000)) (hi := (529487003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 588907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 588907) = 1/(588907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-529487003 / 1000000000) (-264743501 / 500000000) (Real.log (588907 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132802197 / 500000000) ≤ -Real.log (1000000 / 1304219) ∧
    -Real.log (1000000 / 1304219) ≤ (53120879 / 200000000) := by
  have h := checkLog_sound (w := (304219 / 2304219)) (n := 12)
    (lo := (132802197 / 500000000)) (hi := (53120879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304219 / 1000000) = 1/(1000000 / 1304219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132802197 / 500000000) (53120879 / 200000000) (Real.log (1304219 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1304219 / 1000000) = -Real.log (1000000 / 1304219) := by
    rw [show ((1304219 / 1000000) : ℝ) = ((1000000 / 1304219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (362720323 / 1000000000) ≤ -Real.log (695781 / 1000000) ∧
    -Real.log (695781 / 1000000) ≤ (90680081 / 250000000) := by
  have h := checkLog_sound (w := (304219 / 1695781)) (n := 12)
    (lo := (362720323 / 1000000000)) (hi := (90680081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695781) = 1/(695781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90680081 / 250000000) (-362720323 / 1000000000) (Real.log (695781 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266149399 / 1000000000) ≤ -Real.log (100000 / 130493) ∧
    -Real.log (100000 / 130493) ≤ (1330747 / 5000000) := by
  have h := checkLog_sound (w := (30493 / 230493)) (n := 12)
    (lo := (266149399 / 1000000000)) (hi := (1330747 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130493 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130493 / 100000) = 1/(100000 / 130493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266149399 / 1000000000) (1330747 / 5000000) (Real.log (130493 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (130493 / 100000) = -Real.log (100000 / 130493) := by
    rw [show ((130493 / 100000) : ℝ) = ((100000 / 130493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (363742719 / 1000000000) ≤ -Real.log (69507 / 100000) ∧
    -Real.log (69507 / 100000) ≤ (142087 / 390625) := by
  have h := checkLog_sound (w := (30493 / 169507)) (n := 12)
    (lo := (363742719 / 1000000000)) (hi := (142087 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69507) = 1/(69507 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-142087 / 390625) (-363742719 / 1000000000) (Real.log (69507 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (871751413 / 1000000000) ≤ -Real.log (100000000000 / 239109498457) ∧
    -Real.log (100000000000 / 239109498457) ≤ (174350283 / 200000000) := by
  have h := checkLog_sound (w := (39109498457 / 439109498457)) (n := 12)
    (lo := (178604233 / 1000000000)) (hi := (89302117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239109498457 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239109498457 / 200000000000) = 1/(100000000000 / 239109498457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (871751413 / 1000000000) (174350283 / 200000000) (Real.log (239109498457 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239109498457 / 100000000000) = -Real.log (100000000000 / 239109498457) := by
    rw [show ((239109498457 / 100000000000) : ℝ) = ((100000000000 / 239109498457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (873851583 / 1000000000) ≤ -Real.log (500000000000 / 1198060984163) ∧
    -Real.log (500000000000 / 1198060984163) ≤ (174770317 / 200000000) := by
  have h := checkLog_sound (w := (198060984163 / 2198060984163)) (n := 12)
    (lo := (180704403 / 1000000000)) (hi := (45176101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198060984163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1198060984163 / 1000000000000) = 1/(500000000000 / 1198060984163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (873851583 / 1000000000) (174770317 / 200000000) (Real.log (1198060984163 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1198060984163 / 500000000000) = -Real.log (500000000000 / 1198060984163) := by
    rw [show ((1198060984163 / 500000000000) : ℝ) = ((500000000000 / 1198060984163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (628324717 / 1000000000) ≤ -Real.log (500000000000 / 937233842257) ∧
    -Real.log (500000000000 / 937233842257) ≤ (314162359 / 500000000) := by
  have h := checkLog_sound (w := (437233842257 / 1437233842257)) (n := 12)
    (lo := (628324717 / 1000000000)) (hi := (314162359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((937233842257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(937233842257 / 500000000000) = 1/(500000000000 / 937233842257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (628324717 / 1000000000) (314162359 / 500000000) (Real.log (937233842257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (937233842257 / 500000000000) = -Real.log (500000000000 / 937233842257) := by
    rw [show ((937233842257 / 500000000000) : ℝ) = ((500000000000 / 937233842257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (314946059 / 500000000) ≤ -Real.log (500000000000 / 938704015423) ∧
    -Real.log (500000000000 / 938704015423) ≤ (629892119 / 1000000000) := by
  have h := checkLog_sound (w := (438704015423 / 1438704015423)) (n := 12)
    (lo := (314946059 / 500000000)) (hi := (629892119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938704015423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938704015423 / 500000000000) = 1/(500000000000 / 938704015423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (314946059 / 500000000) (629892119 / 1000000000) (Real.log (938704015423 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (938704015423 / 500000000000) = -Real.log (500000000000 / 938704015423) := by
    rw [show ((938704015423 / 500000000000) : ℝ) = ((500000000000 / 938704015423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0231
