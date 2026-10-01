import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0439
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

theorem reflection_log_1_neg : (190830177 / 1000000000) ≤ -Real.log (10240 / 12393) ∧
    -Real.log (10240 / 12393) ≤ (95415089 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 22633)) (n := 12)
    (lo := (190830177 / 1000000000)) (hi := (95415089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12393 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12393 / 10240) = 1/(10240 / 12393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (190830177 / 1000000000) (95415089 / 500000000) (Real.log (12393 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12393 / 10240) = -Real.log (10240 / 12393) := by
    rw [show ((12393 / 10240) : ℝ) = ((10240 / 12393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47208757 / 200000000) ≤ -Real.log (8087 / 10240) ∧
    -Real.log (8087 / 10240) ≤ (118021893 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 18327)) (n := 12)
    (lo := (47208757 / 200000000)) (hi := (118021893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8087) = 1/(8087 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118021893 / 500000000) (-47208757 / 200000000) (Real.log (8087 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47647019 / 250000000) ≤ -Real.log (1024 / 1239) ∧
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


theorem reflection_log_3 : Bounds (47647019 / 250000000) (190588077 / 1000000000) (Real.log (1239 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1239 / 1024) = -Real.log (1024 / 1239) := by
    rw [show ((1239 / 1024) : ℝ) = ((1024 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29459111 / 125000000) ≤ -Real.log (809 / 1024) ∧
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


theorem reflection_log_4 : Bounds (-235672889 / 1000000000) (-29459111 / 125000000) (Real.log (809 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (175507211 / 500000000) ≤ -Real.log (5120 / 7273) ∧
    -Real.log (5120 / 7273) ≤ (351014423 / 1000000000) := by
  have h := checkLog_sound (w := (2153 / 12393)) (n := 12)
    (lo := (175507211 / 500000000)) (hi := (351014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7273 / 5120) = 1/(5120 / 7273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (175507211 / 500000000) (351014423 / 1000000000) (Real.log (7273 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7273 / 5120) = -Real.log (5120 / 7273) := by
    rw [show ((7273 / 5120) : ℝ) = ((5120 / 7273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (545603097 / 1000000000) ≤ -Real.log (2967 / 5120) ∧
    -Real.log (2967 / 5120) ≤ (272801549 / 500000000) := by
  have h := checkLog_sound (w := (2153 / 8087)) (n := 12)
    (lo := (545603097 / 1000000000)) (hi := (272801549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2967) = 1/(2967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-272801549 / 500000000) (-545603097 / 1000000000) (Real.log (2967 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87650463 / 250000000) ≤ -Real.log (512 / 727) ∧
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


theorem reflection_log_7 : Bounds (87650463 / 250000000) (350601853 / 1000000000) (Real.log (727 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (727 / 512) = -Real.log (512 / 727) := by
    rw [show ((727 / 512) : ℝ) = ((512 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272296243 / 500000000) ≤ -Real.log (297 / 512) ∧
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


theorem reflection_log_8 : Bounds (-544592487 / 1000000000) (-272296243 / 500000000) (Real.log (297 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65453913 / 250000000) ≤ -Real.log (1000000 / 1299287) ∧
    -Real.log (1000000 / 1299287) ≤ (261815653 / 1000000000) := by
  have h := checkLog_sound (w := (299287 / 2299287)) (n := 12)
    (lo := (65453913 / 250000000)) (hi := (261815653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299287 / 1000000) = 1/(1000000 / 1299287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65453913 / 250000000) (261815653 / 1000000000) (Real.log (1299287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1299287 / 1000000) = -Real.log (1000000 / 1299287) := by
    rw [show ((1299287 / 1000000) : ℝ) = ((1000000 / 1299287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35565689 / 100000000) ≤ -Real.log (700713 / 1000000) ∧
    -Real.log (700713 / 1000000) ≤ (355656891 / 1000000000) := by
  have h := checkLog_sound (w := (299287 / 1700713)) (n := 12)
    (lo := (35565689 / 100000000)) (hi := (355656891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700713) = 1/(700713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-355656891 / 1000000000) (-35565689 / 100000000) (Real.log (700713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26214347 / 100000000) ≤ -Real.log (1000000 / 1299713) ∧
    -Real.log (1000000 / 1299713) ≤ (262143471 / 1000000000) := by
  have h := checkLog_sound (w := (299713 / 2299713)) (n := 12)
    (lo := (26214347 / 100000000)) (hi := (262143471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299713 / 1000000) = 1/(1000000 / 1299713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26214347 / 100000000) (262143471 / 1000000000) (Real.log (1299713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1299713 / 1000000) = -Real.log (1000000 / 1299713) := by
    rw [show ((1299713 / 1000000) : ℝ) = ((1000000 / 1299713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (356265027 / 1000000000) ≤ -Real.log (700287 / 1000000) ∧
    -Real.log (700287 / 1000000) ≤ (89066257 / 250000000) := by
  have h := checkLog_sound (w := (299713 / 1700287)) (n := 12)
    (lo := (356265027 / 1000000000)) (hi := (89066257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700287) = 1/(700287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89066257 / 250000000) (-356265027 / 1000000000) (Real.log (700287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19639703 / 100000000) ≤ -Real.log (100000 / 121701) ∧
    -Real.log (100000 / 121701) ≤ (196397031 / 1000000000) := by
  have h := checkLog_sound (w := (21701 / 221701)) (n := 12)
    (lo := (19639703 / 100000000)) (hi := (196397031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121701 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121701 / 100000) = 1/(100000 / 121701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19639703 / 100000000) (196397031 / 1000000000) (Real.log (121701 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121701 / 100000) = -Real.log (100000 / 121701) := by
    rw [show ((121701 / 100000) : ℝ) = ((100000 / 121701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122317677 / 500000000) ≤ -Real.log (78299 / 100000) ∧
    -Real.log (78299 / 100000) ≤ (48927071 / 200000000) := by
  have h := checkLog_sound (w := (21701 / 178299)) (n := 12)
    (lo := (122317677 / 500000000)) (hi := (48927071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78299) = 1/(78299 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48927071 / 200000000) (-122317677 / 500000000) (Real.log (78299 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196663221 / 1000000000) ≤ -Real.log (500000 / 608667) ∧
    -Real.log (500000 / 608667) ≤ (98331611 / 500000000) := by
  have h := checkLog_sound (w := (108667 / 1108667)) (n := 12)
    (lo := (196663221 / 1000000000)) (hi := (98331611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608667 / 500000) = 1/(500000 / 608667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196663221 / 1000000000) (98331611 / 500000000) (Real.log (608667 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (608667 / 500000) = -Real.log (500000 / 608667) := by
    rw [show ((608667 / 500000) : ℝ) = ((500000 / 608667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (122524619 / 500000000) ≤ -Real.log (391333 / 500000) ∧
    -Real.log (391333 / 500000) ≤ (245049239 / 1000000000) := by
  have h := checkLog_sound (w := (108667 / 891333)) (n := 12)
    (lo := (122524619 / 500000000)) (hi := (245049239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391333) = 1/(391333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-245049239 / 1000000000) (-122524619 / 500000000) (Real.log (391333 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (617472543 / 1000000000) ≤ -Real.log (500000000000 / 927117807147) ∧
    -Real.log (500000000000 / 927117807147) ≤ (19296017 / 31250000) := by
  have h := checkLog_sound (w := (427117807147 / 1427117807147)) (n := 12)
    (lo := (617472543 / 1000000000)) (hi := (19296017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927117807147 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927117807147 / 500000000000) = 1/(500000000000 / 927117807147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (617472543 / 1000000000) (19296017 / 31250000) (Real.log (927117807147 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (927117807147 / 500000000000) = -Real.log (500000000000 / 927117807147) := by
    rw [show ((927117807147 / 500000000000) : ℝ) = ((500000000000 / 927117807147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309204249 / 500000000) ≤ -Real.log (500000000000 / 927985954331) ∧
    -Real.log (500000000000 / 927985954331) ≤ (618408499 / 1000000000) := by
  have h := checkLog_sound (w := (427985954331 / 1427985954331)) (n := 12)
    (lo := (309204249 / 500000000)) (hi := (618408499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927985954331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927985954331 / 500000000000) = 1/(500000000000 / 927985954331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309204249 / 500000000) (618408499 / 1000000000) (Real.log (927985954331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (927985954331 / 500000000000) = -Real.log (500000000000 / 927985954331) := by
    rw [show ((927985954331 / 500000000000) : ℝ) = ((500000000000 / 927985954331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (88206477 / 200000000) ≤ -Real.log (500000000000 / 777155519227) ∧
    -Real.log (500000000000 / 777155519227) ≤ (220516193 / 500000000) := by
  have h := checkLog_sound (w := (277155519227 / 1277155519227)) (n := 12)
    (lo := (88206477 / 200000000)) (hi := (220516193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777155519227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777155519227 / 500000000000) = 1/(500000000000 / 777155519227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (88206477 / 200000000) (220516193 / 500000000) (Real.log (777155519227 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (777155519227 / 500000000000) = -Real.log (500000000000 / 777155519227) := by
    rw [show ((777155519227 / 500000000000) : ℝ) = ((500000000000 / 777155519227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (22085623 / 50000000) ≤ -Real.log (5000000000 / 7776842229) ∧
    -Real.log (5000000000 / 7776842229) ≤ (441712461 / 1000000000) := by
  have h := checkLog_sound (w := (2776842229 / 12776842229)) (n := 12)
    (lo := (22085623 / 50000000)) (hi := (441712461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7776842229 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7776842229 / 5000000000) = 1/(5000000000 / 7776842229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (22085623 / 50000000) (441712461 / 1000000000) (Real.log (7776842229 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7776842229 / 5000000000) = -Real.log (5000000000 / 7776842229) := by
    rw [show ((7776842229 / 5000000000) : ℝ) = ((5000000000 / 7776842229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0439
