import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0380
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

theorem reflection_log_1_neg : (102505701 / 500000000) ≤ -Real.log (1024 / 1257) ∧
    -Real.log (1024 / 1257) ≤ (205011403 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2281)) (n := 12)
    (lo := (102505701 / 500000000)) (hi := (205011403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1024) = 1/(1024 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (102505701 / 500000000) (205011403 / 1000000000) (Real.log (1257 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1257 / 1024) = -Real.log (1024 / 1257) := by
    rw [show ((1257 / 1024) : ℝ) = ((1024 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (258173837 / 1000000000) ≤ -Real.log (791 / 1024) ∧
    -Real.log (791 / 1024) ≤ (129086919 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1815)) (n := 12)
    (lo := (258173837 / 1000000000)) (hi := (129086919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 791) = 1/(791 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129086919 / 500000000) (-258173837 / 1000000000) (Real.log (791 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204772711 / 1000000000) ≤ -Real.log (10240 / 12567) ∧
    -Real.log (10240 / 12567) ≤ (25596589 / 125000000) := by
  have h := checkLog_sound (w := (2327 / 22807)) (n := 12)
    (lo := (204772711 / 1000000000)) (hi := (25596589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12567 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12567 / 10240) = 1/(10240 / 12567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204772711 / 1000000000) (25596589 / 125000000) (Real.log (12567 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12567 / 10240) = -Real.log (10240 / 12567) := by
    rw [show ((12567 / 10240) : ℝ) = ((10240 / 12567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (128897321 / 500000000) ≤ -Real.log (7913 / 10240) ∧
    -Real.log (7913 / 10240) ≤ (257794643 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 18153)) (n := 12)
    (lo := (128897321 / 500000000)) (hi := (257794643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7913) = 1/(7913 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-257794643 / 1000000000) (-128897321 / 500000000) (Real.log (7913 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (375059593 / 1000000000) ≤ -Real.log (512 / 745) ∧
    -Real.log (512 / 745) ≤ (187529797 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1257)) (n := 12)
    (lo := (375059593 / 1000000000)) (hi := (187529797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745 / 512) = 1/(512 / 745) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (375059593 / 1000000000) (187529797 / 500000000) (Real.log (745 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (745 / 512) = -Real.log (512 / 745) := by
    rw [show ((745 / 512) : ℝ) = ((512 / 745) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (607112843 / 1000000000) ≤ -Real.log (279 / 512) ∧
    -Real.log (279 / 512) ≤ (151778211 / 250000000) := by
  have h := checkLog_sound (w := (233 / 791)) (n := 12)
    (lo := (607112843 / 1000000000)) (hi := (151778211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 279) = 1/(279 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-151778211 / 250000000) (-607112843 / 1000000000) (Real.log (279 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (374656827 / 1000000000) ≤ -Real.log (5120 / 7447) ∧
    -Real.log (5120 / 7447) ≤ (93664207 / 250000000) := by
  have h := checkLog_sound (w := (2327 / 12567)) (n := 12)
    (lo := (374656827 / 1000000000)) (hi := (93664207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7447 / 5120) = 1/(5120 / 7447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (374656827 / 1000000000) (93664207 / 250000000) (Real.log (7447 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7447 / 5120) = -Real.log (5120 / 7447) := by
    rw [show ((7447 / 5120) : ℝ) = ((5120 / 7447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75754769 / 125000000) ≤ -Real.log (2793 / 5120) ∧
    -Real.log (2793 / 5120) ≤ (606038153 / 1000000000) := by
  have h := checkLog_sound (w := (2327 / 7913)) (n := 12)
    (lo := (75754769 / 125000000)) (hi := (606038153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2793) = 1/(2793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-606038153 / 1000000000) (-75754769 / 125000000) (Real.log (2793 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (70241203 / 250000000) ≤ -Real.log (1000000 / 1324407) ∧
    -Real.log (1000000 / 1324407) ≤ (280964813 / 1000000000) := by
  have h := checkLog_sound (w := (324407 / 2324407)) (n := 12)
    (lo := (70241203 / 250000000)) (hi := (280964813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324407 / 1000000) = 1/(1000000 / 1324407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (70241203 / 250000000) (280964813 / 1000000000) (Real.log (1324407 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1324407 / 1000000) = -Real.log (1000000 / 1324407) := by
    rw [show ((1324407 / 1000000) : ℝ) = ((1000000 / 1324407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78432891 / 200000000) ≤ -Real.log (675593 / 1000000) ∧
    -Real.log (675593 / 1000000) ≤ (49020557 / 125000000) := by
  have h := checkLog_sound (w := (324407 / 1675593)) (n := 12)
    (lo := (78432891 / 200000000)) (hi := (49020557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675593) = 1/(675593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49020557 / 125000000) (-78432891 / 200000000) (Real.log (675593 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (281287923 / 1000000000) ≤ -Real.log (200000 / 264967) ∧
    -Real.log (200000 / 264967) ≤ (70321981 / 250000000) := by
  have h := checkLog_sound (w := (64967 / 464967)) (n := 12)
    (lo := (281287923 / 1000000000)) (hi := (70321981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264967 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(264967 / 200000) = 1/(200000 / 264967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (281287923 / 1000000000) (70321981 / 250000000) (Real.log (264967 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (264967 / 200000) = -Real.log (200000 / 264967) := by
    rw [show ((264967 / 200000) : ℝ) = ((200000 / 264967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (392798173 / 1000000000) ≤ -Real.log (135033 / 200000) ∧
    -Real.log (135033 / 200000) ≤ (196399087 / 500000000) := by
  have h := checkLog_sound (w := (64967 / 335033)) (n := 12)
    (lo := (392798173 / 1000000000)) (hi := (196399087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 135033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 135033) = 1/(135033 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196399087 / 500000000) (-392798173 / 1000000000) (Real.log (135033 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26512651 / 125000000) ≤ -Real.log (1000000 / 1236273) ∧
    -Real.log (1000000 / 1236273) ≤ (212101209 / 1000000000) := by
  have h := checkLog_sound (w := (236273 / 2236273)) (n := 12)
    (lo := (26512651 / 125000000)) (hi := (212101209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236273 / 1000000) = 1/(1000000 / 1236273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26512651 / 125000000) (212101209 / 1000000000) (Real.log (1236273 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1236273 / 1000000) = -Real.log (1000000 / 1236273) := by
    rw [show ((1236273 / 1000000) : ℝ) = ((1000000 / 1236273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (269544883 / 1000000000) ≤ -Real.log (763727 / 1000000) ∧
    -Real.log (763727 / 1000000) ≤ (67386221 / 250000000) := by
  have h := checkLog_sound (w := (236273 / 1763727)) (n := 12)
    (lo := (269544883 / 1000000000)) (hi := (67386221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763727) = 1/(763727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-67386221 / 250000000) (-269544883 / 1000000000) (Real.log (763727 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (26546013 / 125000000) ≤ -Real.log (1000000 / 1236603) ∧
    -Real.log (1000000 / 1236603) ≤ (42473621 / 200000000) := by
  have h := checkLog_sound (w := (236603 / 2236603)) (n := 12)
    (lo := (26546013 / 125000000)) (hi := (42473621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236603 / 1000000) = 1/(1000000 / 1236603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (26546013 / 125000000) (42473621 / 200000000) (Real.log (1236603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1236603 / 1000000) = -Real.log (1000000 / 1236603) := by
    rw [show ((1236603 / 1000000) : ℝ) = ((1000000 / 1236603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (67494267 / 250000000) ≤ -Real.log (763397 / 1000000) ∧
    -Real.log (763397 / 1000000) ≤ (269977069 / 1000000000) := by
  have h := checkLog_sound (w := (236603 / 1763397)) (n := 12)
    (lo := (67494267 / 250000000)) (hi := (269977069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763397) = 1/(763397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-269977069 / 1000000000) (-67494267 / 250000000) (Real.log (763397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (673129267 / 1000000000) ≤ -Real.log (500000000000 / 980181114961) ∧
    -Real.log (500000000000 / 980181114961) ≤ (168282317 / 250000000) := by
  have h := checkLog_sound (w := (480181114961 / 1480181114961)) (n := 12)
    (lo := (673129267 / 1000000000)) (hi := (168282317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980181114961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980181114961 / 500000000000) = 1/(500000000000 / 980181114961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (673129267 / 1000000000) (168282317 / 250000000) (Real.log (980181114961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (980181114961 / 500000000000) = -Real.log (500000000000 / 980181114961) := by
    rw [show ((980181114961 / 500000000000) : ℝ) = ((500000000000 / 980181114961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (42130381 / 62500000) ≤ -Real.log (250000000000 / 490559715033) ∧
    -Real.log (250000000000 / 490559715033) ≤ (674086097 / 1000000000) := by
  have h := checkLog_sound (w := (240559715033 / 740559715033)) (n := 12)
    (lo := (42130381 / 62500000)) (hi := (674086097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490559715033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490559715033 / 250000000000) = 1/(250000000000 / 490559715033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (42130381 / 62500000) (674086097 / 1000000000) (Real.log (490559715033 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (490559715033 / 250000000000) = -Real.log (250000000000 / 490559715033) := by
    rw [show ((490559715033 / 250000000000) : ℝ) = ((250000000000 / 490559715033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (481646091 / 1000000000) ≤ -Real.log (125000000000 / 202342099991) ∧
    -Real.log (125000000000 / 202342099991) ≤ (120411523 / 250000000) := by
  have h := checkLog_sound (w := (77342099991 / 327342099991)) (n := 12)
    (lo := (481646091 / 1000000000)) (hi := (120411523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202342099991 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202342099991 / 125000000000) = 1/(125000000000 / 202342099991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (481646091 / 1000000000) (120411523 / 250000000) (Real.log (202342099991 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (202342099991 / 125000000000) = -Real.log (125000000000 / 202342099991) := by
    rw [show ((202342099991 / 125000000000) : ℝ) = ((125000000000 / 202342099991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120586293 / 250000000) ≤ -Real.log (100000000000 / 161986882317) ∧
    -Real.log (100000000000 / 161986882317) ≤ (482345173 / 1000000000) := by
  have h := checkLog_sound (w := (61986882317 / 261986882317)) (n := 12)
    (lo := (120586293 / 250000000)) (hi := (482345173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161986882317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161986882317 / 100000000000) = 1/(100000000000 / 161986882317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120586293 / 250000000) (482345173 / 1000000000) (Real.log (161986882317 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161986882317 / 100000000000) = -Real.log (100000000000 / 161986882317) := by
    rw [show ((161986882317 / 100000000000) : ℝ) = ((100000000000 / 161986882317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0380
