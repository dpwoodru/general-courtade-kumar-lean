import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0454
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

theorem reflection_log_1_neg : (187192487 / 1000000000) ≤ -Real.log (2560 / 3087) ∧
    -Real.log (2560 / 3087) ≤ (23399061 / 125000000) := by
  have h := checkLog_sound (w := (527 / 5647)) (n := 12)
    (lo := (187192487 / 1000000000)) (hi := (23399061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3087 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3087 / 2560) = 1/(2560 / 3087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187192487 / 1000000000) (23399061 / 125000000) (Real.log (3087 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3087 / 2560) = -Real.log (2560 / 3087) := by
    rw [show ((3087 / 2560) : ℝ) = ((2560 / 3087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230494723 / 1000000000) ≤ -Real.log (2033 / 2560) ∧
    -Real.log (2033 / 2560) ≤ (57623681 / 250000000) := by
  have h := checkLog_sound (w := (527 / 4593)) (n := 12)
    (lo := (230494723 / 1000000000)) (hi := (57623681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2033) = 1/(2033 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57623681 / 250000000) (-230494723 / 1000000000) (Real.log (2033 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (186949503 / 1000000000) ≤ -Real.log (2048 / 2469) ∧
    -Real.log (2048 / 2469) ≤ (1460543 / 7812500) := by
  have h := checkLog_sound (w := (421 / 4517)) (n := 12)
    (lo := (186949503 / 1000000000)) (hi := (1460543 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2048) = 1/(2048 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (186949503 / 1000000000) (1460543 / 7812500) (Real.log (2469 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2469 / 2048) = -Real.log (2048 / 2469) := by
    rw [show ((2469 / 2048) : ℝ) = ((2048 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (115062939 / 500000000) ≤ -Real.log (1627 / 2048) ∧
    -Real.log (1627 / 2048) ≤ (230125879 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3675)) (n := 12)
    (lo := (115062939 / 500000000)) (hi := (230125879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1627) = 1/(1627 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-230125879 / 1000000000) (-115062939 / 500000000) (Real.log (1627 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (344807933 / 1000000000) ≤ -Real.log (1280 / 1807) ∧
    -Real.log (1280 / 1807) ≤ (172403967 / 500000000) := by
  have h := checkLog_sound (w := (527 / 3087)) (n := 12)
    (lo := (344807933 / 1000000000)) (hi := (172403967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807 / 1280) = 1/(1280 / 1807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (344807933 / 1000000000) (172403967 / 500000000) (Real.log (1807 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1807 / 1280) = -Real.log (1280 / 1807) := by
    rw [show ((1807 / 1280) : ℝ) = ((1280 / 1807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (530550129 / 1000000000) ≤ -Real.log (753 / 1280) ∧
    -Real.log (753 / 1280) ≤ (53055013 / 100000000) := by
  have h := checkLog_sound (w := (527 / 2033)) (n := 12)
    (lo := (530550129 / 1000000000)) (hi := (53055013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 753) = 1/(753 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-53055013 / 100000000) (-530550129 / 1000000000) (Real.log (753 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172196397 / 500000000) ≤ -Real.log (1024 / 1445) ∧
    -Real.log (1024 / 1445) ≤ (68878559 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2469)) (n := 12)
    (lo := (172196397 / 500000000)) (hi := (68878559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445 / 1024) = 1/(1024 / 1445) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172196397 / 500000000) (68878559 / 200000000) (Real.log (1445 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1445 / 1024) = -Real.log (1024 / 1445) := by
    rw [show ((1445 / 1024) : ℝ) = ((1024 / 1445) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33097163 / 62500000) ≤ -Real.log (603 / 1024) ∧
    -Real.log (603 / 1024) ≤ (529554609 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1627)) (n := 12)
    (lo := (33097163 / 62500000)) (hi := (529554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 603) = 1/(603 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-529554609 / 1000000000) (-33097163 / 62500000) (Real.log (603 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (64225613 / 250000000) ≤ -Real.log (1000000 / 1292919) ∧
    -Real.log (1000000 / 1292919) ≤ (256902453 / 1000000000) := by
  have h := checkLog_sound (w := (292919 / 2292919)) (n := 12)
    (lo := (64225613 / 250000000)) (hi := (256902453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292919 / 1000000) = 1/(1000000 / 1292919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (64225613 / 250000000) (256902453 / 1000000000) (Real.log (1292919 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1292919 / 1000000) = -Real.log (1000000 / 1292919) := by
    rw [show ((1292919 / 1000000) : ℝ) = ((1000000 / 1292919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (346610051 / 1000000000) ≤ -Real.log (707081 / 1000000) ∧
    -Real.log (707081 / 1000000) ≤ (86652513 / 250000000) := by
  have h := checkLog_sound (w := (292919 / 1707081)) (n := 12)
    (lo := (346610051 / 1000000000)) (hi := (86652513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707081) = 1/(707081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86652513 / 250000000) (-346610051 / 1000000000) (Real.log (707081 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51446377 / 200000000) ≤ -Real.log (200000 / 258669) ∧
    -Real.log (200000 / 258669) ≤ (128615943 / 500000000) := by
  have h := checkLog_sound (w := (58669 / 458669)) (n := 12)
    (lo := (51446377 / 200000000)) (hi := (128615943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258669 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(258669 / 200000) = 1/(200000 / 258669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51446377 / 200000000) (128615943 / 500000000) (Real.log (258669 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (258669 / 200000) = -Real.log (200000 / 258669) := by
    rw [show ((258669 / 200000) : ℝ) = ((200000 / 258669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347212709 / 1000000000) ≤ -Real.log (141331 / 200000) ∧
    -Real.log (141331 / 200000) ≤ (34721271 / 100000000) := by
  have h := checkLog_sound (w := (58669 / 341331)) (n := 12)
    (lo := (347212709 / 1000000000)) (hi := (34721271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 141331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 141331) = 1/(141331 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34721271 / 100000000) (-347212709 / 1000000000) (Real.log (141331 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (192408841 / 1000000000) ≤ -Real.log (500000 / 606083) ∧
    -Real.log (500000 / 606083) ≤ (96204421 / 500000000) := by
  have h := checkLog_sound (w := (106083 / 1106083)) (n := 12)
    (lo := (192408841 / 1000000000)) (hi := (96204421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606083 / 500000) = 1/(500000 / 606083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (192408841 / 1000000000) (96204421 / 500000000) (Real.log (606083 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (606083 / 500000) = -Real.log (500000 / 606083) := by
    rw [show ((606083 / 500000) : ℝ) = ((500000 / 606083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238467871 / 1000000000) ≤ -Real.log (393917 / 500000) ∧
    -Real.log (393917 / 500000) ≤ (7452121 / 31250000) := by
  have h := checkLog_sound (w := (106083 / 893917)) (n := 12)
    (lo := (238467871 / 1000000000)) (hi := (7452121 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393917) = 1/(393917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7452121 / 31250000) (-238467871 / 1000000000) (Real.log (393917 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192675271 / 1000000000) ≤ -Real.log (1000000 / 1212489) ∧
    -Real.log (1000000 / 1212489) ≤ (24084409 / 125000000) := by
  have h := checkLog_sound (w := (212489 / 2212489)) (n := 12)
    (lo := (192675271 / 1000000000)) (hi := (24084409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212489 / 1000000) = 1/(1000000 / 1212489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192675271 / 1000000000) (24084409 / 125000000) (Real.log (1212489 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1212489 / 1000000) = -Real.log (1000000 / 1212489) := by
    rw [show ((1212489 / 1000000) : ℝ) = ((1000000 / 1212489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11943897 / 50000000) ≤ -Real.log (787511 / 1000000) ∧
    -Real.log (787511 / 1000000) ≤ (238877941 / 1000000000) := by
  have h := checkLog_sound (w := (212489 / 1787511)) (n := 12)
    (lo := (11943897 / 50000000)) (hi := (238877941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787511) = 1/(787511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-238877941 / 1000000000) (-11943897 / 50000000) (Real.log (787511 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (603512503 / 1000000000) ≤ -Real.log (250000000000 / 457132563313) ∧
    -Real.log (250000000000 / 457132563313) ≤ (75439063 / 125000000) := by
  have h := checkLog_sound (w := (207132563313 / 707132563313)) (n := 12)
    (lo := (603512503 / 1000000000)) (hi := (75439063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457132563313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457132563313 / 250000000000) = 1/(250000000000 / 457132563313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (603512503 / 1000000000) (75439063 / 125000000) (Real.log (457132563313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (457132563313 / 250000000000) = -Real.log (250000000000 / 457132563313) := by
    rw [show ((457132563313 / 250000000000) : ℝ) = ((250000000000 / 457132563313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (120888919 / 200000000) ≤ -Real.log (100000000000 / 183023540483) ∧
    -Real.log (100000000000 / 183023540483) ≤ (151111149 / 250000000) := by
  have h := checkLog_sound (w := (83023540483 / 283023540483)) (n := 12)
    (lo := (120888919 / 200000000)) (hi := (151111149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183023540483 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183023540483 / 100000000000) = 1/(100000000000 / 183023540483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (120888919 / 200000000) (151111149 / 250000000) (Real.log (183023540483 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (183023540483 / 100000000000) = -Real.log (100000000000 / 183023540483) := by
    rw [show ((183023540483 / 100000000000) : ℝ) = ((100000000000 / 183023540483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (430876713 / 1000000000) ≤ -Real.log (25000000000 / 38465146211) ∧
    -Real.log (25000000000 / 38465146211) ≤ (215438357 / 500000000) := by
  have h := checkLog_sound (w := (13465146211 / 63465146211)) (n := 12)
    (lo := (430876713 / 1000000000)) (hi := (215438357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38465146211 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38465146211 / 25000000000) = 1/(25000000000 / 38465146211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (430876713 / 1000000000) (215438357 / 500000000) (Real.log (38465146211 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38465146211 / 25000000000) = -Real.log (25000000000 / 38465146211) := by
    rw [show ((38465146211 / 25000000000) : ℝ) = ((25000000000 / 38465146211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (431553211 / 1000000000) ≤ -Real.log (31250000000 / 48113970789) ∧
    -Real.log (31250000000 / 48113970789) ≤ (107888303 / 250000000) := by
  have h := checkLog_sound (w := (16863970789 / 79363970789)) (n := 12)
    (lo := (431553211 / 1000000000)) (hi := (107888303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48113970789 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48113970789 / 31250000000) = 1/(31250000000 / 48113970789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (431553211 / 1000000000) (107888303 / 250000000) (Real.log (48113970789 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48113970789 / 31250000000) = -Real.log (31250000000 / 48113970789) := by
    rw [show ((48113970789 / 31250000000) : ℝ) = ((31250000000 / 48113970789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0454
