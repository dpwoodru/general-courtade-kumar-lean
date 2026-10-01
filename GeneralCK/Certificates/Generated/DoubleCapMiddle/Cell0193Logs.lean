import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0193
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

theorem reflection_log_1_neg : (134401911 / 500000000) ≤ -Real.log (5120 / 6699) ∧
    -Real.log (5120 / 6699) ≤ (268803823 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 11819)) (n := 12)
    (lo := (134401911 / 500000000)) (hi := (268803823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6699 / 5120) = 1/(5120 / 6699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134401911 / 500000000) (268803823 / 1000000000) (Real.log (6699 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6699 / 5120) = -Real.log (5120 / 6699) := by
    rw [show ((6699 / 5120) : ℝ) = ((5120 / 6699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73749053 / 200000000) ≤ -Real.log (3541 / 5120) ∧
    -Real.log (3541 / 5120) ≤ (184372633 / 500000000) := by
  have h := checkLog_sound (w := (1579 / 8661)) (n := 12)
    (lo := (73749053 / 200000000)) (hi := (184372633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3541) = 1/(3541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-184372633 / 500000000) (-73749053 / 200000000) (Real.log (3541 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134177947 / 500000000) ≤ -Real.log (640 / 837) ∧
    -Real.log (640 / 837) ≤ (53671179 / 200000000) := by
  have h := checkLog_sound (w := (197 / 1477)) (n := 12)
    (lo := (134177947 / 500000000)) (hi := (53671179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 640) = 1/(640 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134177947 / 500000000) (53671179 / 200000000) (Real.log (837 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (837 / 640) = -Real.log (640 / 837) := by
    rw [show ((837 / 640) : ℝ) = ((640 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (183949203 / 500000000) ≤ -Real.log (443 / 640) ∧
    -Real.log (443 / 640) ≤ (367898407 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1083)) (n := 12)
    (lo := (183949203 / 500000000)) (hi := (367898407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 443) = 1/(443 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-367898407 / 1000000000) (-183949203 / 500000000) (Real.log (443 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240223477 / 500000000) ≤ -Real.log (2560 / 4139) ∧
    -Real.log (2560 / 4139) ≤ (96089391 / 200000000) := by
  have h := checkLog_sound (w := (1579 / 6699)) (n := 12)
    (lo := (240223477 / 500000000)) (hi := (96089391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4139 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4139 / 2560) = 1/(2560 / 4139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240223477 / 500000000) (96089391 / 200000000) (Real.log (4139 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4139 / 2560) = -Real.log (2560 / 4139) := by
    rw [show ((4139 / 2560) : ℝ) = ((2560 / 4139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (959190077 / 1000000000) ≤ -Real.log (981 / 2560) ∧
    -Real.log (981 / 2560) ≤ (959190079 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2261)) (n := 12)
    (lo := (266042897 / 1000000000)) (hi := (133021449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 981) = 1/(981 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-959190079 / 1000000000) (-959190077 / 1000000000) (Real.log (981 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36711367 / 100000000) ≤ -Real.log (500000 / 721781) ∧
    -Real.log (500000 / 721781) ≤ (367113671 / 1000000000) := by
  have h := checkLog_sound (w := (221781 / 1221781)) (n := 12)
    (lo := (36711367 / 100000000)) (hi := (367113671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721781 / 500000) = 1/(500000 / 721781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36711367 / 100000000) (367113671 / 1000000000) (Real.log (721781 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (721781 / 500000) = -Real.log (500000 / 721781) := by
    rw [show ((721781 / 500000) : ℝ) = ((500000 / 721781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23447981 / 40000000) ≤ -Real.log (278219 / 500000) ∧
    -Real.log (278219 / 500000) ≤ (293099763 / 500000000) := by
  have h := checkLog_sound (w := (221781 / 778219)) (n := 12)
    (lo := (23447981 / 40000000)) (hi := (293099763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 278219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 278219) = 1/(278219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-293099763 / 500000000) (-23447981 / 40000000) (Real.log (278219 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91931291 / 250000000) ≤ -Real.log (200000 / 288889) ∧
    -Real.log (200000 / 288889) ≤ (73545033 / 200000000) := by
  have h := checkLog_sound (w := (88889 / 488889)) (n := 12)
    (lo := (91931291 / 250000000)) (hi := (73545033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288889 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288889 / 200000) = 1/(200000 / 288889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91931291 / 250000000) (73545033 / 200000000) (Real.log (288889 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288889 / 200000) = -Real.log (200000 / 288889) := by
    rw [show ((288889 / 200000) : ℝ) = ((200000 / 288889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36736729 / 62500000) ≤ -Real.log (111111 / 200000) ∧
    -Real.log (111111 / 200000) ≤ (117557533 / 200000000) := by
  have h := checkLog_sound (w := (88889 / 311111)) (n := 12)
    (lo := (36736729 / 62500000)) (hi := (117557533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111111) = 1/(111111 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-117557533 / 200000000) (-36736729 / 62500000) (Real.log (111111 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (143216521 / 500000000) ≤ -Real.log (1000000 / 1331669) ∧
    -Real.log (1000000 / 1331669) ≤ (286433043 / 1000000000) := by
  have h := checkLog_sound (w := (331669 / 2331669)) (n := 12)
    (lo := (143216521 / 500000000)) (hi := (286433043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331669 / 1000000) = 1/(1000000 / 1331669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (143216521 / 500000000) (286433043 / 1000000000) (Real.log (1331669 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1331669 / 1000000) = -Real.log (1000000 / 1331669) := by
    rw [show ((1331669 / 1000000) : ℝ) = ((1000000 / 1331669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (402971719 / 1000000000) ≤ -Real.log (668331 / 1000000) ∧
    -Real.log (668331 / 1000000) ≤ (10074293 / 25000000) := by
  have h := checkLog_sound (w := (331669 / 1668331)) (n := 12)
    (lo := (402971719 / 1000000000)) (hi := (10074293 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668331) = 1/(668331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10074293 / 25000000) (-402971719 / 1000000000) (Real.log (668331 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28698633 / 100000000) ≤ -Real.log (500000 / 666203) ∧
    -Real.log (500000 / 666203) ≤ (286986331 / 1000000000) := by
  have h := checkLog_sound (w := (166203 / 1166203)) (n := 12)
    (lo := (28698633 / 100000000)) (hi := (286986331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666203 / 500000) = 1/(500000 / 666203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28698633 / 100000000) (286986331 / 1000000000) (Real.log (666203 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (666203 / 500000) = -Real.log (500000 / 666203) := by
    rw [show ((666203 / 500000) : ℝ) = ((500000 / 666203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (202037537 / 500000000) ≤ -Real.log (333797 / 500000) ∧
    -Real.log (333797 / 500000) ≤ (16163003 / 40000000) := by
  have h := checkLog_sound (w := (166203 / 833797)) (n := 12)
    (lo := (202037537 / 500000000)) (hi := (16163003 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333797) = 1/(333797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16163003 / 40000000) (-202037537 / 500000000) (Real.log (333797 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (476656597 / 500000000) ≤ -Real.log (31250000000 / 81071588389) ∧
    -Real.log (31250000000 / 81071588389) ≤ (238328299 / 250000000) := by
  have h := checkLog_sound (w := (18571588389 / 143571588389)) (n := 12)
    (lo := (130083007 / 500000000)) (hi := (52033203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81071588389 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(81071588389 / 62500000000) = 1/(31250000000 / 81071588389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (476656597 / 500000000) (238328299 / 250000000) (Real.log (81071588389 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (81071588389 / 31250000000) = -Real.log (31250000000 / 81071588389) := by
    rw [show ((81071588389 / 31250000000) : ℝ) = ((31250000000 / 81071588389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (955512829 / 1000000000) ≤ -Real.log (250000000000 / 650000900001) ∧
    -Real.log (250000000000 / 650000900001) ≤ (955512831 / 1000000000) := by
  have h := checkLog_sound (w := (150000900001 / 1150000900001)) (n := 12)
    (lo := (262365649 / 1000000000)) (hi := (5247313 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650000900001 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(650000900001 / 500000000000) = 1/(250000000000 / 650000900001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (955512829 / 1000000000) (955512831 / 1000000000) (Real.log (650000900001 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (650000900001 / 250000000000) = -Real.log (250000000000 / 650000900001) := by
    rw [show ((650000900001 / 250000000000) : ℝ) = ((250000000000 / 650000900001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (689404761 / 1000000000) ≤ -Real.log (500000000000 / 996264575487) ∧
    -Real.log (500000000000 / 996264575487) ≤ (344702381 / 500000000) := by
  have h := checkLog_sound (w := (496264575487 / 1496264575487)) (n := 12)
    (lo := (689404761 / 1000000000)) (hi := (344702381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996264575487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996264575487 / 500000000000) = 1/(500000000000 / 996264575487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (689404761 / 1000000000) (344702381 / 500000000) (Real.log (996264575487 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (996264575487 / 500000000000) = -Real.log (500000000000 / 996264575487) := by
    rw [show ((996264575487 / 500000000000) : ℝ) = ((500000000000 / 996264575487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (138212281 / 200000000) ≤ -Real.log (50000000000 / 99791639829) ∧
    -Real.log (50000000000 / 99791639829) ≤ (345530703 / 500000000) := by
  have h := checkLog_sound (w := (49791639829 / 149791639829)) (n := 12)
    (lo := (138212281 / 200000000)) (hi := (345530703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99791639829 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99791639829 / 50000000000) = 1/(50000000000 / 99791639829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (138212281 / 200000000) (345530703 / 500000000) (Real.log (99791639829 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (99791639829 / 50000000000) = -Real.log (50000000000 / 99791639829) := by
    rw [show ((99791639829 / 50000000000) : ℝ) = ((50000000000 / 99791639829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0193
