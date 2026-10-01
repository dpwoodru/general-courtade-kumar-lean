import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0413
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

theorem reflection_log_1_neg : (197104329 / 1000000000) ≤ -Real.log (10240 / 12471) ∧
    -Real.log (10240 / 12471) ≤ (19710433 / 100000000) := by
  have h := checkLog_sound (w := (2231 / 22711)) (n := 12)
    (lo := (197104329 / 1000000000)) (hi := (19710433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12471 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12471 / 10240) = 1/(10240 / 12471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (197104329 / 1000000000) (19710433 / 100000000) (Real.log (12471 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12471 / 10240) = -Real.log (10240 / 12471) := by
    rw [show ((12471 / 10240) : ℝ) = ((10240 / 12471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24573571 / 100000000) ≤ -Real.log (8009 / 10240) ∧
    -Real.log (8009 / 10240) ≤ (245735711 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 18249)) (n := 12)
    (lo := (24573571 / 100000000)) (hi := (245735711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8009) = 1/(8009 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-245735711 / 1000000000) (-24573571 / 100000000) (Real.log (8009 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (98431871 / 500000000) ≤ -Real.log (2560 / 3117) ∧
    -Real.log (2560 / 3117) ≤ (196863743 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 5677)) (n := 12)
    (lo := (98431871 / 500000000)) (hi := (196863743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 2560) = 1/(2560 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (98431871 / 500000000) (196863743 / 1000000000) (Real.log (3117 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3117 / 2560) = -Real.log (2560 / 3117) := by
    rw [show ((3117 / 2560) : ℝ) = ((2560 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (245361201 / 1000000000) ≤ -Real.log (2003 / 2560) ∧
    -Real.log (2003 / 2560) ≤ (122680601 / 500000000) := by
  have h := checkLog_sound (w := (557 / 4563)) (n := 12)
    (lo := (245361201 / 1000000000)) (hi := (122680601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2003) = 1/(2003 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122680601 / 500000000) (-245361201 / 1000000000) (Real.log (2003 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (361681919 / 1000000000) ≤ -Real.log (5120 / 7351) ∧
    -Real.log (5120 / 7351) ≤ (141282 / 390625) := by
  have h := checkLog_sound (w := (2231 / 12471)) (n := 12)
    (lo := (361681919 / 1000000000)) (hi := (141282 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7351 / 5120) = 1/(5120 / 7351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (361681919 / 1000000000) (141282 / 390625) (Real.log (7351 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7351 / 5120) = -Real.log (5120 / 7351) := by
    rw [show ((7351 / 5120) : ℝ) = ((5120 / 7351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (572244017 / 1000000000) ≤ -Real.log (2889 / 5120) ∧
    -Real.log (2889 / 5120) ≤ (286122009 / 500000000) := by
  have h := checkLog_sound (w := (2231 / 8009)) (n := 12)
    (lo := (572244017 / 1000000000)) (hi := (286122009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2889) = 1/(2889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-286122009 / 500000000) (-572244017 / 1000000000) (Real.log (2889 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2822451 / 7812500) ≤ -Real.log (1280 / 1837) ∧
    -Real.log (1280 / 1837) ≤ (361273729 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 3117)) (n := 12)
    (lo := (2822451 / 7812500)) (hi := (361273729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1837 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1837 / 1280) = 1/(1280 / 1837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2822451 / 7812500) (361273729 / 1000000000) (Real.log (1837 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1837 / 1280) = -Real.log (1280 / 1837) := by
    rw [show ((1837 / 1280) : ℝ) = ((1280 / 1837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285603067 / 500000000) ≤ -Real.log (723 / 1280) ∧
    -Real.log (723 / 1280) ≤ (114241227 / 200000000) := by
  have h := checkLog_sound (w := (557 / 2003)) (n := 12)
    (lo := (285603067 / 500000000)) (hi := (114241227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 723) = 1/(723 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-114241227 / 200000000) (-285603067 / 500000000) (Real.log (723 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270288171 / 1000000000) ≤ -Real.log (500000 / 655171) ∧
    -Real.log (500000 / 655171) ≤ (67572043 / 250000000) := by
  have h := checkLog_sound (w := (155171 / 1155171)) (n := 12)
    (lo := (270288171 / 1000000000)) (hi := (67572043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655171 / 500000) = 1/(500000 / 655171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270288171 / 1000000000) (67572043 / 250000000) (Real.log (655171 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (655171 / 500000) = -Real.log (500000 / 655171) := by
    rw [show ((655171 / 500000) : ℝ) = ((500000 / 655171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11611233 / 31250000) ≤ -Real.log (344829 / 500000) ∧
    -Real.log (344829 / 500000) ≤ (371559457 / 1000000000) := by
  have h := checkLog_sound (w := (155171 / 844829)) (n := 12)
    (lo := (11611233 / 31250000)) (hi := (371559457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344829) = 1/(344829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-371559457 / 1000000000) (-11611233 / 31250000) (Real.log (344829 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33826653 / 125000000) ≤ -Real.log (62500 / 81923) ∧
    -Real.log (62500 / 81923) ≤ (10824529 / 40000000) := by
  have h := checkLog_sound (w := (19423 / 144423)) (n := 12)
    (lo := (33826653 / 125000000)) (hi := (10824529 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81923 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81923 / 62500) = 1/(62500 / 81923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33826653 / 125000000) (10824529 / 40000000) (Real.log (81923 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (81923 / 62500) = -Real.log (62500 / 81923) := by
    rw [show ((81923 / 62500) : ℝ) = ((62500 / 81923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5815271 / 15625000) ≤ -Real.log (43077 / 62500) ∧
    -Real.log (43077 / 62500) ≤ (74435469 / 200000000) := by
  have h := checkLog_sound (w := (19423 / 105577)) (n := 12)
    (lo := (5815271 / 15625000)) (hi := (74435469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43077) = 1/(43077 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-74435469 / 200000000) (-5815271 / 15625000) (Real.log (43077 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (203313019 / 1000000000) ≤ -Real.log (62500 / 76591) ∧
    -Real.log (62500 / 76591) ≤ (10165651 / 50000000) := by
  have h := checkLog_sound (w := (14091 / 139091)) (n := 12)
    (lo := (203313019 / 1000000000)) (hi := (10165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76591 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76591 / 62500) = 1/(62500 / 76591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (203313019 / 1000000000) (10165651 / 50000000) (Real.log (76591 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (76591 / 62500) = -Real.log (62500 / 76591) := by
    rw [show ((76591 / 62500) : ℝ) = ((62500 / 76591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (255480809 / 1000000000) ≤ -Real.log (48409 / 62500) ∧
    -Real.log (48409 / 62500) ≤ (25548081 / 100000000) := by
  have h := checkLog_sound (w := (14091 / 110909)) (n := 12)
    (lo := (255480809 / 1000000000)) (hi := (25548081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48409) = 1/(48409 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-25548081 / 100000000) (-255480809 / 1000000000) (Real.log (48409 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203579823 / 1000000000) ≤ -Real.log (1000000 / 1225783) ∧
    -Real.log (1000000 / 1225783) ≤ (12723739 / 62500000) := by
  have h := checkLog_sound (w := (225783 / 2225783)) (n := 12)
    (lo := (203579823 / 1000000000)) (hi := (12723739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225783 / 1000000) = 1/(1000000 / 1225783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203579823 / 1000000000) (12723739 / 62500000) (Real.log (1225783 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225783 / 1000000) = -Real.log (1000000 / 1225783) := by
    rw [show ((1225783 / 1000000) : ℝ) = ((1000000 / 1225783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (127951541 / 500000000) ≤ -Real.log (774217 / 1000000) ∧
    -Real.log (774217 / 1000000) ≤ (255903083 / 1000000000) := by
  have h := checkLog_sound (w := (225783 / 1774217)) (n := 12)
    (lo := (127951541 / 500000000)) (hi := (255903083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774217) = 1/(774217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255903083 / 1000000000) (-127951541 / 500000000) (Real.log (774217 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (160461907 / 250000000) ≤ -Real.log (31250000000 / 59374628439) ∧
    -Real.log (31250000000 / 59374628439) ≤ (641847629 / 1000000000) := by
  have h := checkLog_sound (w := (28124628439 / 90624628439)) (n := 12)
    (lo := (160461907 / 250000000)) (hi := (641847629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59374628439 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59374628439 / 31250000000) = 1/(31250000000 / 59374628439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (160461907 / 250000000) (641847629 / 1000000000) (Real.log (59374628439 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (59374628439 / 31250000000) = -Real.log (31250000000 / 59374628439) := by
    rw [show ((59374628439 / 31250000000) : ℝ) = ((31250000000 / 59374628439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (642790569 / 1000000000) ≤ -Real.log (125000000000 / 237722566567) ∧
    -Real.log (125000000000 / 237722566567) ≤ (64279057 / 100000000) := by
  have h := checkLog_sound (w := (112722566567 / 362722566567)) (n := 12)
    (lo := (642790569 / 1000000000)) (hi := (64279057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237722566567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237722566567 / 125000000000) = 1/(125000000000 / 237722566567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (642790569 / 1000000000) (64279057 / 100000000) (Real.log (237722566567 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (237722566567 / 125000000000) = -Real.log (125000000000 / 237722566567) := by
    rw [show ((237722566567 / 125000000000) : ℝ) = ((125000000000 / 237722566567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (458793829 / 1000000000) ≤ -Real.log (250000000000 / 395541118387) ∧
    -Real.log (250000000000 / 395541118387) ≤ (45879383 / 100000000) := by
  have h := checkLog_sound (w := (145541118387 / 645541118387)) (n := 12)
    (lo := (458793829 / 1000000000)) (hi := (45879383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395541118387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395541118387 / 250000000000) = 1/(250000000000 / 395541118387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (458793829 / 1000000000) (45879383 / 100000000) (Real.log (395541118387 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (395541118387 / 250000000000) = -Real.log (250000000000 / 395541118387) := by
    rw [show ((395541118387 / 250000000000) : ℝ) = ((250000000000 / 395541118387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (229741453 / 500000000) ≤ -Real.log (125000000000 / 197906885279) ∧
    -Real.log (125000000000 / 197906885279) ≤ (459482907 / 1000000000) := by
  have h := checkLog_sound (w := (72906885279 / 322906885279)) (n := 12)
    (lo := (229741453 / 500000000)) (hi := (459482907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197906885279 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197906885279 / 125000000000) = 1/(125000000000 / 197906885279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (229741453 / 500000000) (459482907 / 1000000000) (Real.log (197906885279 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (197906885279 / 125000000000) = -Real.log (125000000000 / 197906885279) := by
    rw [show ((197906885279 / 125000000000) : ℝ) = ((125000000000 / 197906885279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0413
