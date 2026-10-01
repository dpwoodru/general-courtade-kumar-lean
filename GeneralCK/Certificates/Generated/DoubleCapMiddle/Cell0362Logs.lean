import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0362
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

theorem reflection_log_1_neg : (6540567 / 31250000) ≤ -Real.log (640 / 789) ∧
    -Real.log (640 / 789) ≤ (41859629 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1429)) (n := 12)
    (lo := (6540567 / 31250000)) (hi := (41859629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 640) = 1/(640 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6540567 / 31250000) (41859629 / 200000000) (Real.log (789 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (789 / 640) = -Real.log (640 / 789) := by
    rw [show ((789 / 640) : ℝ) = ((640 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16564003 / 62500000) ≤ -Real.log (491 / 640) ∧
    -Real.log (491 / 640) ≤ (265024049 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1131)) (n := 12)
    (lo := (16564003 / 62500000)) (hi := (265024049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 491) = 1/(491 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-265024049 / 1000000000) (-16564003 / 62500000) (Real.log (491 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (209060473 / 1000000000) ≤ -Real.log (10240 / 12621) ∧
    -Real.log (10240 / 12621) ≤ (104530237 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 22861)) (n := 12)
    (lo := (209060473 / 1000000000)) (hi := (104530237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12621 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12621 / 10240) = 1/(10240 / 12621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (209060473 / 1000000000) (104530237 / 500000000) (Real.log (12621 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12621 / 10240) = -Real.log (10240 / 12621) := by
    rw [show ((12621 / 10240) : ℝ) = ((10240 / 12621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (264642247 / 1000000000) ≤ -Real.log (7859 / 10240) ∧
    -Real.log (7859 / 10240) ≤ (33080281 / 125000000) := by
  have h := checkLog_sound (w := (2381 / 18099)) (n := 12)
    (lo := (264642247 / 1000000000)) (hi := (33080281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7859) = 1/(7859 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33080281 / 125000000) (-264642247 / 1000000000) (Real.log (7859 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95570443 / 250000000) ≤ -Real.log (320 / 469) ∧
    -Real.log (320 / 469) ≤ (382281773 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 789)) (n := 12)
    (lo := (95570443 / 250000000)) (hi := (382281773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469 / 320) = 1/(320 / 469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95570443 / 250000000) (382281773 / 1000000000) (Real.log (469 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (469 / 320) = -Real.log (320 / 469) := by
    rw [show ((469 / 320) : ℝ) = ((320 / 469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (626657439 / 1000000000) ≤ -Real.log (171 / 320) ∧
    -Real.log (171 / 320) ≤ (3916609 / 6250000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 171) = 1/(171 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3916609 / 6250000) (-626657439 / 1000000000) (Real.log (171 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76376381 / 200000000) ≤ -Real.log (5120 / 7501) ∧
    -Real.log (5120 / 7501) ≤ (190940953 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 12621)) (n := 12)
    (lo := (76376381 / 200000000)) (hi := (190940953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7501 / 5120) = 1/(5120 / 7501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76376381 / 200000000) (190940953 / 500000000) (Real.log (7501 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7501 / 5120) = -Real.log (5120 / 7501) := by
    rw [show ((7501 / 5120) : ℝ) = ((5120 / 7501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156390387 / 250000000) ≤ -Real.log (2739 / 5120) ∧
    -Real.log (2739 / 5120) ≤ (625561549 / 1000000000) := by
  have h := checkLog_sound (w := (2381 / 7859)) (n := 12)
    (lo := (156390387 / 250000000)) (hi := (625561549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2739) = 1/(2739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-625561549 / 1000000000) (-156390387 / 250000000) (Real.log (2739 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (286753641 / 1000000000) ≤ -Real.log (15625 / 20814) ∧
    -Real.log (15625 / 20814) ≤ (143376821 / 500000000) := by
  have h := checkLog_sound (w := (5189 / 36439)) (n := 12)
    (lo := (286753641 / 1000000000)) (hi := (143376821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20814 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20814 / 15625) = 1/(15625 / 20814) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (286753641 / 1000000000) (143376821 / 500000000) (Real.log (20814 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20814 / 15625) = -Real.log (15625 / 20814) := by
    rw [show ((20814 / 15625) : ℝ) = ((15625 / 20814) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100902707 / 250000000) ≤ -Real.log (10436 / 15625) ∧
    -Real.log (10436 / 15625) ≤ (403610829 / 1000000000) := by
  have h := checkLog_sound (w := (5189 / 26061)) (n := 12)
    (lo := (100902707 / 250000000)) (hi := (403610829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10436) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10436) = 1/(10436 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-403610829 / 1000000000) (-100902707 / 250000000) (Real.log (10436 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143537819 / 500000000) ≤ -Real.log (40000 / 53301) ∧
    -Real.log (40000 / 53301) ≤ (287075639 / 1000000000) := by
  have h := checkLog_sound (w := (13301 / 93301)) (n := 12)
    (lo := (143537819 / 500000000)) (hi := (287075639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53301 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53301 / 40000) = 1/(40000 / 53301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143537819 / 500000000) (287075639 / 1000000000) (Real.log (53301 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (53301 / 40000) = -Real.log (40000 / 53301) := by
    rw [show ((53301 / 40000) : ℝ) = ((40000 / 53301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (202126671 / 500000000) ≤ -Real.log (26699 / 40000) ∧
    -Real.log (26699 / 40000) ≤ (404253343 / 1000000000) := by
  have h := checkLog_sound (w := (13301 / 66699)) (n := 12)
    (lo := (202126671 / 500000000)) (hi := (404253343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26699) = 1/(26699 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-404253343 / 1000000000) (-202126671 / 500000000) (Real.log (26699 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108450453 / 500000000) ≤ -Real.log (1000000 / 1242221) ∧
    -Real.log (1000000 / 1242221) ≤ (216900907 / 1000000000) := by
  have h := checkLog_sound (w := (242221 / 2242221)) (n := 12)
    (lo := (108450453 / 500000000)) (hi := (216900907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242221 / 1000000) = 1/(1000000 / 1242221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108450453 / 500000000) (216900907 / 1000000000) (Real.log (1242221 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1242221 / 1000000) = -Real.log (1000000 / 1242221) := by
    rw [show ((1242221 / 1000000) : ℝ) = ((1000000 / 1242221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69340873 / 250000000) ≤ -Real.log (757779 / 1000000) ∧
    -Real.log (757779 / 1000000) ≤ (277363493 / 1000000000) := by
  have h := checkLog_sound (w := (242221 / 1757779)) (n := 12)
    (lo := (69340873 / 250000000)) (hi := (277363493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757779) = 1/(757779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-277363493 / 1000000000) (-69340873 / 250000000) (Real.log (757779 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (108584067 / 500000000) ≤ -Real.log (1000000 / 1242553) ∧
    -Real.log (1000000 / 1242553) ≤ (43433627 / 200000000) := by
  have h := checkLog_sound (w := (242553 / 2242553)) (n := 12)
    (lo := (108584067 / 500000000)) (hi := (43433627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242553 / 1000000) = 1/(1000000 / 1242553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108584067 / 500000000) (43433627 / 200000000) (Real.log (1242553 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1242553 / 1000000) = -Real.log (1000000 / 1242553) := by
    rw [show ((1242553 / 1000000) : ℝ) = ((1000000 / 1242553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (277801711 / 1000000000) ≤ -Real.log (757447 / 1000000) ∧
    -Real.log (757447 / 1000000) ≤ (17362607 / 62500000) := by
  have h := checkLog_sound (w := (242553 / 1757447)) (n := 12)
    (lo := (277801711 / 1000000000)) (hi := (17362607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757447) = 1/(757447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-17362607 / 62500000) (-277801711 / 1000000000) (Real.log (757447 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (690364469 / 1000000000) ≤ -Real.log (500000000000 / 997221157531) ∧
    -Real.log (500000000000 / 997221157531) ≤ (69036447 / 100000000) := by
  have h := checkLog_sound (w := (497221157531 / 1497221157531)) (n := 12)
    (lo := (690364469 / 1000000000)) (hi := (69036447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997221157531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997221157531 / 500000000000) = 1/(500000000000 / 997221157531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (690364469 / 1000000000) (69036447 / 100000000) (Real.log (997221157531 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (997221157531 / 500000000000) = -Real.log (500000000000 / 997221157531) := by
    rw [show ((997221157531 / 500000000000) : ℝ) = ((500000000000 / 997221157531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (691328981 / 1000000000) ≤ -Real.log (125000000000 / 249545863141) ∧
    -Real.log (125000000000 / 249545863141) ≤ (345664491 / 500000000) := by
  have h := checkLog_sound (w := (124545863141 / 374545863141)) (n := 12)
    (lo := (691328981 / 1000000000)) (hi := (345664491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249545863141 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249545863141 / 125000000000) = 1/(125000000000 / 249545863141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (691328981 / 1000000000) (345664491 / 500000000) (Real.log (249545863141 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (249545863141 / 125000000000) = -Real.log (125000000000 / 249545863141) := by
    rw [show ((249545863141 / 125000000000) : ℝ) = ((125000000000 / 249545863141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (494264399 / 1000000000) ≤ -Real.log (25000000000 / 40982298269) ∧
    -Real.log (25000000000 / 40982298269) ≤ (1235661 / 2500000) := by
  have h := checkLog_sound (w := (15982298269 / 65982298269)) (n := 12)
    (lo := (494264399 / 1000000000)) (hi := (1235661 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40982298269 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40982298269 / 25000000000) = 1/(25000000000 / 40982298269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (494264399 / 1000000000) (1235661 / 2500000) (Real.log (40982298269 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (40982298269 / 25000000000) = -Real.log (25000000000 / 40982298269) := by
    rw [show ((40982298269 / 25000000000) : ℝ) = ((25000000000 / 40982298269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (98993969 / 200000000) ≤ -Real.log (500000000000 / 820224385337) ∧
    -Real.log (500000000000 / 820224385337) ≤ (247484923 / 500000000) := by
  have h := checkLog_sound (w := (320224385337 / 1320224385337)) (n := 12)
    (lo := (98993969 / 200000000)) (hi := (247484923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820224385337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820224385337 / 500000000000) = 1/(500000000000 / 820224385337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (98993969 / 200000000) (247484923 / 500000000) (Real.log (820224385337 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (820224385337 / 500000000000) = -Real.log (500000000000 / 820224385337) := by
    rw [show ((820224385337 / 500000000000) : ℝ) = ((500000000000 / 820224385337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0362
