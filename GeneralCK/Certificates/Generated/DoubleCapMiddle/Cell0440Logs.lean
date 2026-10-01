import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0440
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

theorem reflection_log_1_neg : (47647019 / 250000000) ≤ -Real.log (1024 / 1239) ∧
    -Real.log (1024 / 1239) ≤ (190588077 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 2263)) (n := 12)
    (lo := (47647019 / 250000000)) (hi := (190588077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239 / 1024) = 1/(1024 / 1239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47647019 / 250000000) (190588077 / 1000000000) (Real.log (1239 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1239 / 1024) = -Real.log (1024 / 1239) := by
    rw [show ((1239 / 1024) : ℝ) = ((1024 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29459111 / 125000000) ≤ -Real.log (809 / 1024) ∧
    -Real.log (809 / 1024) ≤ (235672889 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1833)) (n := 12)
    (lo := (29459111 / 125000000)) (hi := (235672889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 809) = 1/(809 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-235672889 / 1000000000) (-29459111 / 125000000) (Real.log (809 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38069183 / 200000000) ≤ -Real.log (10240 / 12387) ∧
    -Real.log (10240 / 12387) ≤ (47586479 / 250000000) := by
  have h := checkLog_sound (w := (2147 / 22627)) (n := 12)
    (lo := (38069183 / 200000000)) (hi := (47586479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 10240) = 1/(10240 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38069183 / 200000000) (47586479 / 250000000) (Real.log (12387 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12387 / 10240) = -Real.log (10240 / 12387) := by
    rw [show ((12387 / 10240) : ℝ) = ((10240 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (235302129 / 1000000000) ≤ -Real.log (8093 / 10240) ∧
    -Real.log (8093 / 10240) ≤ (23530213 / 100000000) := by
  have h := checkLog_sound (w := (2147 / 18333)) (n := 12)
    (lo := (235302129 / 1000000000)) (hi := (23530213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8093) = 1/(8093 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-23530213 / 100000000) (-235302129 / 1000000000) (Real.log (8093 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87650463 / 250000000) ≤ -Real.log (512 / 727) ∧
    -Real.log (512 / 727) ≤ (350601853 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 1239)) (n := 12)
    (lo := (87650463 / 250000000)) (hi := (350601853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 512) = 1/(512 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87650463 / 250000000) (350601853 / 1000000000) (Real.log (727 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (727 / 512) = -Real.log (512 / 727) := by
    rw [show ((727 / 512) : ℝ) = ((512 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (272296243 / 500000000) ≤ -Real.log (297 / 512) ∧
    -Real.log (297 / 512) ≤ (544592487 / 1000000000) := by
  have h := checkLog_sound (w := (215 / 809)) (n := 12)
    (lo := (272296243 / 500000000)) (hi := (544592487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 297) = 1/(297 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-544592487 / 1000000000) (-272296243 / 500000000) (Real.log (297 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43773639 / 125000000) ≤ -Real.log (5120 / 7267) ∧
    -Real.log (5120 / 7267) ≤ (350189113 / 1000000000) := by
  have h := checkLog_sound (w := (2147 / 12387)) (n := 12)
    (lo := (43773639 / 125000000)) (hi := (350189113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7267 / 5120) = 1/(5120 / 7267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43773639 / 125000000) (350189113 / 1000000000) (Real.log (7267 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7267 / 5120) = -Real.log (5120 / 7267) := by
    rw [show ((7267 / 5120) : ℝ) = ((5120 / 7267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108716579 / 200000000) ≤ -Real.log (2973 / 5120) ∧
    -Real.log (2973 / 5120) ≤ (33973931 / 62500000) := by
  have h := checkLog_sound (w := (2147 / 8093)) (n := 12)
    (lo := (108716579 / 200000000)) (hi := (33973931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2973) = 1/(2973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33973931 / 62500000) (-108716579 / 200000000) (Real.log (2973 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16343031 / 62500000) ≤ -Real.log (500000 / 649431) ∧
    -Real.log (500000 / 649431) ≤ (261488497 / 1000000000) := by
  have h := checkLog_sound (w := (149431 / 1149431)) (n := 12)
    (lo := (16343031 / 62500000)) (hi := (261488497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649431 / 500000) = 1/(500000 / 649431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16343031 / 62500000) (261488497 / 1000000000) (Real.log (649431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (649431 / 500000) = -Real.log (500000 / 649431) := by
    rw [show ((649431 / 500000) : ℝ) = ((500000 / 649431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (355050549 / 1000000000) ≤ -Real.log (350569 / 500000) ∧
    -Real.log (350569 / 500000) ≤ (7101011 / 20000000) := by
  have h := checkLog_sound (w := (149431 / 850569)) (n := 12)
    (lo := (355050549 / 1000000000)) (hi := (7101011 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350569) = 1/(350569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7101011 / 20000000) (-355050549 / 1000000000) (Real.log (350569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130908211 / 500000000) ≤ -Real.log (125000 / 162411) ∧
    -Real.log (125000 / 162411) ≤ (261816423 / 1000000000) := by
  have h := checkLog_sound (w := (37411 / 287411)) (n := 12)
    (lo := (130908211 / 500000000)) (hi := (261816423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162411 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162411 / 125000) = 1/(125000 / 162411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130908211 / 500000000) (261816423 / 1000000000) (Real.log (162411 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (162411 / 125000) = -Real.log (125000 / 162411) := by
    rw [show ((162411 / 125000) : ℝ) = ((125000 / 162411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (177829159 / 500000000) ≤ -Real.log (87589 / 125000) ∧
    -Real.log (87589 / 125000) ≤ (355658319 / 1000000000) := by
  have h := checkLog_sound (w := (37411 / 212589)) (n := 12)
    (lo := (177829159 / 500000000)) (hi := (355658319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87589) = 1/(87589 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-355658319 / 1000000000) (-177829159 / 500000000) (Real.log (87589 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (196130769 / 1000000000) ≤ -Real.log (500000 / 608343) ∧
    -Real.log (500000 / 608343) ≤ (19613077 / 100000000) := by
  have h := checkLog_sound (w := (108343 / 1108343)) (n := 12)
    (lo := (196130769 / 1000000000)) (hi := (19613077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608343 / 500000) = 1/(500000 / 608343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (196130769 / 1000000000) (19613077 / 100000000) (Real.log (608343 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (608343 / 500000) = -Real.log (500000 / 608343) := by
    rw [show ((608343 / 500000) : ℝ) = ((500000 / 608343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (244221641 / 1000000000) ≤ -Real.log (391657 / 500000) ∧
    -Real.log (391657 / 500000) ≤ (122110821 / 500000000) := by
  have h := checkLog_sound (w := (108343 / 891657)) (n := 12)
    (lo := (244221641 / 1000000000)) (hi := (122110821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391657) = 1/(391657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122110821 / 500000000) (-244221641 / 1000000000) (Real.log (391657 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (49099463 / 250000000) ≤ -Real.log (1000000 / 1217011) ∧
    -Real.log (1000000 / 1217011) ≤ (196397853 / 1000000000) := by
  have h := checkLog_sound (w := (217011 / 2217011)) (n := 12)
    (lo := (49099463 / 250000000)) (hi := (196397853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217011 / 1000000) = 1/(1000000 / 1217011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49099463 / 250000000) (196397853 / 1000000000) (Real.log (1217011 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1217011 / 1000000) = -Real.log (1000000 / 1217011) := by
    rw [show ((1217011 / 1000000) : ℝ) = ((1000000 / 1217011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (244636631 / 1000000000) ≤ -Real.log (782989 / 1000000) ∧
    -Real.log (782989 / 1000000) ≤ (30579579 / 125000000) := by
  have h := checkLog_sound (w := (217011 / 1782989)) (n := 12)
    (lo := (244636631 / 1000000000)) (hi := (30579579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782989) = 1/(782989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30579579 / 125000000) (-244636631 / 1000000000) (Real.log (782989 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (308269523 / 500000000) ≤ -Real.log (250000000000 / 463126374551) ∧
    -Real.log (250000000000 / 463126374551) ≤ (616539047 / 1000000000) := by
  have h := checkLog_sound (w := (213126374551 / 713126374551)) (n := 12)
    (lo := (308269523 / 500000000)) (hi := (616539047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463126374551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463126374551 / 250000000000) = 1/(250000000000 / 463126374551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (308269523 / 500000000) (616539047 / 1000000000) (Real.log (463126374551 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (463126374551 / 250000000000) = -Real.log (250000000000 / 463126374551) := by
    rw [show ((463126374551 / 250000000000) : ℝ) = ((250000000000 / 463126374551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (30873737 / 50000000) ≤ -Real.log (500000000000 / 927119843817) ∧
    -Real.log (500000000000 / 927119843817) ≤ (617474741 / 1000000000) := by
  have h := checkLog_sound (w := (427119843817 / 1427119843817)) (n := 12)
    (lo := (30873737 / 50000000)) (hi := (617474741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927119843817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927119843817 / 500000000000) = 1/(500000000000 / 927119843817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (30873737 / 50000000) (617474741 / 1000000000) (Real.log (927119843817 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (927119843817 / 500000000000) = -Real.log (500000000000 / 927119843817) := by
    rw [show ((927119843817 / 500000000000) : ℝ) = ((500000000000 / 927119843817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (44035241 / 100000000) ≤ -Real.log (500000000000 / 776627252927) ∧
    -Real.log (500000000000 / 776627252927) ≤ (440352411 / 1000000000) := by
  have h := checkLog_sound (w := (276627252927 / 1276627252927)) (n := 12)
    (lo := (44035241 / 100000000)) (hi := (440352411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776627252927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776627252927 / 500000000000) = 1/(500000000000 / 776627252927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (44035241 / 100000000) (440352411 / 1000000000) (Real.log (776627252927 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (776627252927 / 500000000000) = -Real.log (500000000000 / 776627252927) := by
    rw [show ((776627252927 / 500000000000) : ℝ) = ((500000000000 / 776627252927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (110258621 / 250000000) ≤ -Real.log (125000000000 / 194289287589) ∧
    -Real.log (125000000000 / 194289287589) ≤ (88206897 / 200000000) := by
  have h := checkLog_sound (w := (69289287589 / 319289287589)) (n := 12)
    (lo := (110258621 / 250000000)) (hi := (88206897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194289287589 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194289287589 / 125000000000) = 1/(125000000000 / 194289287589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (110258621 / 250000000) (88206897 / 200000000) (Real.log (194289287589 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (194289287589 / 125000000000) = -Real.log (125000000000 / 194289287589) := by
    rw [show ((194289287589 / 125000000000) : ℝ) = ((125000000000 / 194289287589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0440
