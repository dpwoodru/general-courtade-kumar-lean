import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0406
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

theorem reflection_log_1_neg : (198786819 / 1000000000) ≤ -Real.log (2560 / 3123) ∧
    -Real.log (2560 / 3123) ≤ (9939341 / 50000000) := by
  have h := checkLog_sound (w := (563 / 5683)) (n := 12)
    (lo := (198786819 / 1000000000)) (hi := (9939341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123 / 2560) = 1/(2560 / 3123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198786819 / 1000000000) (9939341 / 50000000) (Real.log (3123 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3123 / 2560) = -Real.log (2560 / 3123) := by
    rw [show ((3123 / 2560) : ℝ) = ((2560 / 3123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (62090301 / 250000000) ≤ -Real.log (1997 / 2560) ∧
    -Real.log (1997 / 2560) ≤ (49672241 / 200000000) := by
  have h := checkLog_sound (w := (563 / 4557)) (n := 12)
    (lo := (62090301 / 250000000)) (hi := (49672241 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1997) = 1/(1997 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49672241 / 200000000) (-62090301 / 250000000) (Real.log (1997 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198546637 / 1000000000) ≤ -Real.log (10240 / 12489) ∧
    -Real.log (10240 / 12489) ≤ (99273319 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 22729)) (n := 12)
    (lo := (198546637 / 1000000000)) (hi := (99273319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12489 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12489 / 10240) = 1/(10240 / 12489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198546637 / 1000000000) (99273319 / 500000000) (Real.log (12489 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12489 / 10240) = -Real.log (10240 / 12489) := by
    rw [show ((12489 / 10240) : ℝ) = ((10240 / 12489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (247985711 / 1000000000) ≤ -Real.log (7991 / 10240) ∧
    -Real.log (7991 / 10240) ≤ (15499107 / 62500000) := by
  have h := checkLog_sound (w := (2249 / 18231)) (n := 12)
    (lo := (247985711 / 1000000000)) (hi := (15499107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7991) = 1/(7991 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15499107 / 62500000) (-247985711 / 1000000000) (Real.log (7991 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1822673 / 5000000) ≤ -Real.log (1280 / 1843) ∧
    -Real.log (1280 / 1843) ≤ (364534601 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3123)) (n := 12)
    (lo := (1822673 / 5000000)) (hi := (364534601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843 / 1280) = 1/(1280 / 1843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1822673 / 5000000) (364534601 / 1000000000) (Real.log (1843 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1843 / 1280) = -Real.log (1280 / 1843) := by
    rw [show ((1843 / 1280) : ℝ) = ((1280 / 1843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (144884879 / 250000000) ≤ -Real.log (717 / 1280) ∧
    -Real.log (717 / 1280) ≤ (579539517 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1997)) (n := 12)
    (lo := (144884879 / 250000000)) (hi := (579539517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 717) = 1/(717 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-579539517 / 1000000000) (-144884879 / 250000000) (Real.log (717 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (91031893 / 250000000) ≤ -Real.log (5120 / 7369) ∧
    -Real.log (5120 / 7369) ≤ (364127573 / 1000000000) := by
  have h := checkLog_sound (w := (2249 / 12489)) (n := 12)
    (lo := (91031893 / 250000000)) (hi := (364127573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7369 / 5120) = 1/(5120 / 7369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (91031893 / 250000000) (364127573 / 1000000000) (Real.log (7369 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7369 / 5120) = -Real.log (5120 / 7369) := by
    rw [show ((7369 / 5120) : ℝ) = ((5120 / 7369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (578494037 / 1000000000) ≤ -Real.log (2871 / 5120) ∧
    -Real.log (2871 / 5120) ≤ (289247019 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 7991)) (n := 12)
    (lo := (578494037 / 1000000000)) (hi := (289247019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2871) = 1/(2871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-289247019 / 500000000) (-578494037 / 1000000000) (Real.log (2871 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (54511961 / 200000000) ≤ -Real.log (500000 / 656661) ∧
    -Real.log (500000 / 656661) ≤ (136279903 / 500000000) := by
  have h := checkLog_sound (w := (156661 / 1156661)) (n := 12)
    (lo := (54511961 / 200000000)) (hi := (136279903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656661 / 500000) = 1/(500000 / 656661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (54511961 / 200000000) (136279903 / 500000000) (Real.log (656661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (656661 / 500000) = -Real.log (500000 / 656661) := by
    rw [show ((656661 / 500000) : ℝ) = ((500000 / 656661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (375889801 / 1000000000) ≤ -Real.log (343339 / 500000) ∧
    -Real.log (343339 / 500000) ≤ (187944901 / 500000000) := by
  have h := checkLog_sound (w := (156661 / 843339)) (n := 12)
    (lo := (375889801 / 1000000000)) (hi := (187944901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 343339) = 1/(343339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-187944901 / 500000000) (-375889801 / 1000000000) (Real.log (343339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136442441 / 500000000) ≤ -Real.log (1000000 / 1313749) ∧
    -Real.log (1000000 / 1313749) ≤ (272884883 / 1000000000) := by
  have h := checkLog_sound (w := (313749 / 2313749)) (n := 12)
    (lo := (136442441 / 500000000)) (hi := (272884883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313749 / 1000000) = 1/(1000000 / 1313749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136442441 / 500000000) (272884883 / 1000000000) (Real.log (1313749 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1313749 / 1000000) = -Real.log (1000000 / 1313749) := by
    rw [show ((1313749 / 1000000) : ℝ) = ((1000000 / 1313749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94127957 / 250000000) ≤ -Real.log (686251 / 1000000) ∧
    -Real.log (686251 / 1000000) ≤ (376511829 / 1000000000) := by
  have h := checkLog_sound (w := (313749 / 1686251)) (n := 12)
    (lo := (94127957 / 250000000)) (hi := (376511829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686251) = 1/(686251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-376511829 / 1000000000) (-94127957 / 250000000) (Real.log (686251 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41035179 / 200000000) ≤ -Real.log (1000000 / 1227741) ∧
    -Real.log (1000000 / 1227741) ≤ (25646987 / 125000000) := by
  have h := checkLog_sound (w := (227741 / 2227741)) (n := 12)
    (lo := (41035179 / 200000000)) (hi := (25646987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227741 / 1000000) = 1/(1000000 / 1227741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41035179 / 200000000) (25646987 / 125000000) (Real.log (1227741 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1227741 / 1000000) = -Real.log (1000000 / 1227741) := by
    rw [show ((1227741 / 1000000) : ℝ) = ((1000000 / 1227741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64608823 / 250000000) ≤ -Real.log (772259 / 1000000) ∧
    -Real.log (772259 / 1000000) ≤ (258435293 / 1000000000) := by
  have h := checkLog_sound (w := (227741 / 1772259)) (n := 12)
    (lo := (64608823 / 250000000)) (hi := (258435293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772259) = 1/(772259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-258435293 / 1000000000) (-64608823 / 250000000) (Real.log (772259 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205443017 / 1000000000) ≤ -Real.log (1000000 / 1228069) ∧
    -Real.log (1000000 / 1228069) ≤ (102721509 / 500000000) := by
  have h := checkLog_sound (w := (228069 / 2228069)) (n := 12)
    (lo := (205443017 / 1000000000)) (hi := (102721509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228069 / 1000000) = 1/(1000000 / 1228069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205443017 / 1000000000) (102721509 / 500000000) (Real.log (1228069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1228069 / 1000000) = -Real.log (1000000 / 1228069) := by
    rw [show ((1228069 / 1000000) : ℝ) = ((1000000 / 1228069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258860111 / 1000000000) ≤ -Real.log (771931 / 1000000) ∧
    -Real.log (771931 / 1000000) ≤ (16178757 / 62500000) := by
  have h := checkLog_sound (w := (228069 / 1771931)) (n := 12)
    (lo := (258860111 / 1000000000)) (hi := (16178757 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771931) = 1/(771931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16178757 / 62500000) (-258860111 / 1000000000) (Real.log (771931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (324224803 / 500000000) ≤ -Real.log (125000000000 / 239071660953) ∧
    -Real.log (125000000000 / 239071660953) ≤ (648449607 / 1000000000) := by
  have h := checkLog_sound (w := (114071660953 / 364071660953)) (n := 12)
    (lo := (324224803 / 500000000)) (hi := (648449607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239071660953 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239071660953 / 125000000000) = 1/(125000000000 / 239071660953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (324224803 / 500000000) (648449607 / 1000000000) (Real.log (239071660953 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239071660953 / 125000000000) = -Real.log (125000000000 / 239071660953) := by
    rw [show ((239071660953 / 125000000000) : ℝ) = ((125000000000 / 239071660953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64939671 / 100000000) ≤ -Real.log (125000000000 / 239298194101) ∧
    -Real.log (125000000000 / 239298194101) ≤ (649396711 / 1000000000) := by
  have h := checkLog_sound (w := (114298194101 / 364298194101)) (n := 12)
    (lo := (64939671 / 100000000)) (hi := (649396711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239298194101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239298194101 / 125000000000) = 1/(125000000000 / 239298194101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64939671 / 100000000) (649396711 / 1000000000) (Real.log (239298194101 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (239298194101 / 125000000000) = -Real.log (125000000000 / 239298194101) := by
    rw [show ((239298194101 / 125000000000) : ℝ) = ((125000000000 / 239298194101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (115902797 / 250000000) ≤ -Real.log (500000000000 / 794902357887) ∧
    -Real.log (500000000000 / 794902357887) ≤ (463611189 / 1000000000) := by
  have h := checkLog_sound (w := (294902357887 / 1294902357887)) (n := 12)
    (lo := (115902797 / 250000000)) (hi := (463611189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794902357887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794902357887 / 500000000000) = 1/(500000000000 / 794902357887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (115902797 / 250000000) (463611189 / 1000000000) (Real.log (794902357887 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (794902357887 / 500000000000) = -Real.log (500000000000 / 794902357887) := by
    rw [show ((794902357887 / 500000000000) : ℝ) = ((500000000000 / 794902357887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (58037891 / 125000000) ≤ -Real.log (250000000000 / 397726286417) ∧
    -Real.log (250000000000 / 397726286417) ≤ (464303129 / 1000000000) := by
  have h := checkLog_sound (w := (147726286417 / 647726286417)) (n := 12)
    (lo := (58037891 / 125000000)) (hi := (464303129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397726286417 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397726286417 / 250000000000) = 1/(250000000000 / 397726286417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (58037891 / 125000000) (464303129 / 1000000000) (Real.log (397726286417 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (397726286417 / 250000000000) = -Real.log (250000000000 / 397726286417) := by
    rw [show ((397726286417 / 250000000000) : ℝ) = ((250000000000 / 397726286417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0406
