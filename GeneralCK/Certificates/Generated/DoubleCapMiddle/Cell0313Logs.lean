import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0313
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

theorem reflection_log_1_neg : (44175071 / 200000000) ≤ -Real.log (10240 / 12771) ∧
    -Real.log (10240 / 12771) ≤ (55218839 / 250000000) := by
  have h := checkLog_sound (w := (2531 / 23011)) (n := 12)
    (lo := (44175071 / 200000000)) (hi := (55218839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12771 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12771 / 10240) = 1/(10240 / 12771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44175071 / 200000000) (55218839 / 250000000) (Real.log (12771 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12771 / 10240) = -Real.log (10240 / 12771) := by
    rw [show ((12771 / 10240) : ℝ) = ((10240 / 12771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141956571 / 500000000) ≤ -Real.log (7709 / 10240) ∧
    -Real.log (7709 / 10240) ≤ (283913143 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 17949)) (n := 12)
    (lo := (141956571 / 500000000)) (hi := (283913143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7709) = 1/(7709 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-283913143 / 1000000000) (-141956571 / 500000000) (Real.log (7709 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (220640421 / 1000000000) ≤ -Real.log (320 / 399) ∧
    -Real.log (320 / 399) ≤ (110320211 / 500000000) := by
  have h := checkLog_sound (w := (79 / 719)) (n := 12)
    (lo := (220640421 / 1000000000)) (hi := (110320211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 320) = 1/(320 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (220640421 / 1000000000) (110320211 / 500000000) (Real.log (399 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (399 / 320) = -Real.log (320 / 399) := by
    rw [show ((399 / 320) : ℝ) = ((320 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141762031 / 500000000) ≤ -Real.log (241 / 320) ∧
    -Real.log (241 / 320) ≤ (283524063 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 561)) (n := 12)
    (lo := (141762031 / 500000000)) (hi := (283524063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 241) = 1/(241 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-283524063 / 1000000000) (-141762031 / 500000000) (Real.log (241 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (401681919 / 1000000000) ≤ -Real.log (5120 / 7651) ∧
    -Real.log (5120 / 7651) ≤ (156907 / 390625) := by
  have h := checkLog_sound (w := (2531 / 12771)) (n := 12)
    (lo := (401681919 / 1000000000)) (hi := (156907 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7651 / 5120) = 1/(5120 / 7651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (401681919 / 1000000000) (156907 / 390625) (Real.log (7651 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7651 / 5120) = -Real.log (5120 / 7651) := by
    rw [show ((7651 / 5120) : ℝ) = ((5120 / 7651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (340941369 / 500000000) ≤ -Real.log (2589 / 5120) ∧
    -Real.log (2589 / 5120) ≤ (681882739 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 7709)) (n := 12)
    (lo := (340941369 / 500000000)) (hi := (681882739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2589) = 1/(2589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-681882739 / 1000000000) (-340941369 / 500000000) (Real.log (2589 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50161217 / 125000000) ≤ -Real.log (160 / 239) ∧
    -Real.log (160 / 239) ≤ (401289737 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399)) (n := 12)
    (lo := (50161217 / 125000000)) (hi := (401289737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 160) = 1/(160 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50161217 / 125000000) (401289737 / 1000000000) (Real.log (239 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (239 / 160) = -Real.log (160 / 239) := by
    rw [show ((239 / 160) : ℝ) = ((160 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (34036233 / 50000000) ≤ -Real.log (81 / 160) ∧
    -Real.log (81 / 160) ≤ (680724661 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 81) = 1/(81 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-680724661 / 1000000000) (-34036233 / 50000000) (Real.log (81 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151196911 / 500000000) ≤ -Real.log (500000 / 676547) ∧
    -Real.log (500000 / 676547) ≤ (302393823 / 1000000000) := by
  have h := checkLog_sound (w := (176547 / 1176547)) (n := 12)
    (lo := (151196911 / 500000000)) (hi := (302393823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676547 / 500000) = 1/(500000 / 676547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151196911 / 500000000) (302393823 / 1000000000) (Real.log (676547 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (676547 / 500000) = -Real.log (500000 / 676547) := by
    rw [show ((676547 / 500000) : ℝ) = ((500000 / 676547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10888857 / 25000000) ≤ -Real.log (323453 / 500000) ∧
    -Real.log (323453 / 500000) ≤ (435554281 / 1000000000) := by
  have h := checkLog_sound (w := (176547 / 823453)) (n := 12)
    (lo := (10888857 / 25000000)) (hi := (435554281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 323453) = 1/(323453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-435554281 / 1000000000) (-10888857 / 25000000) (Real.log (323453 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302711561 / 1000000000) ≤ -Real.log (250000 / 338381) ∧
    -Real.log (250000 / 338381) ≤ (151355781 / 500000000) := by
  have h := checkLog_sound (w := (88381 / 588381)) (n := 12)
    (lo := (302711561 / 1000000000)) (hi := (151355781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338381 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338381 / 250000) = 1/(250000 / 338381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302711561 / 1000000000) (151355781 / 500000000) (Real.log (338381 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (338381 / 250000) = -Real.log (250000 / 338381) := by
    rw [show ((338381 / 250000) : ℝ) = ((250000 / 338381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109054801 / 250000000) ≤ -Real.log (161619 / 250000) ∧
    -Real.log (161619 / 250000) ≤ (87243841 / 200000000) := by
  have h := checkLog_sound (w := (88381 / 411619)) (n := 12)
    (lo := (109054801 / 250000000)) (hi := (87243841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161619) = 1/(161619 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87243841 / 200000000) (-109054801 / 250000000) (Real.log (161619 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (229996019 / 1000000000) ≤ -Real.log (200000 / 251719) ∧
    -Real.log (200000 / 251719) ≤ (11499801 / 50000000) := by
  have h := checkLog_sound (w := (51719 / 451719)) (n := 12)
    (lo := (229996019 / 1000000000)) (hi := (11499801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251719 / 200000) = 1/(200000 / 251719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (229996019 / 1000000000) (11499801 / 50000000) (Real.log (251719 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (251719 / 200000) = -Real.log (200000 / 251719) := by
    rw [show ((251719 / 200000) : ℝ) = ((200000 / 251719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74802061 / 250000000) ≤ -Real.log (148281 / 200000) ∧
    -Real.log (148281 / 200000) ≤ (59841649 / 200000000) := by
  have h := checkLog_sound (w := (51719 / 348281)) (n := 12)
    (lo := (74802061 / 250000000)) (hi := (59841649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148281) = 1/(148281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59841649 / 200000000) (-74802061 / 250000000) (Real.log (148281 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28783067 / 125000000) ≤ -Real.log (1000000 / 1258933) ∧
    -Real.log (1000000 / 1258933) ≤ (230264537 / 1000000000) := by
  have h := checkLog_sound (w := (258933 / 2258933)) (n := 12)
    (lo := (28783067 / 125000000)) (hi := (230264537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258933 / 1000000) = 1/(1000000 / 1258933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28783067 / 125000000) (230264537 / 1000000000) (Real.log (1258933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1258933 / 1000000) = -Real.log (1000000 / 1258933) := by
    rw [show ((1258933 / 1000000) : ℝ) = ((1000000 / 1258933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299664239 / 1000000000) ≤ -Real.log (741067 / 1000000) ∧
    -Real.log (741067 / 1000000) ≤ (3745803 / 12500000) := by
  have h := checkLog_sound (w := (258933 / 1741067)) (n := 12)
    (lo := (299664239 / 1000000000)) (hi := (3745803 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741067) = 1/(741067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3745803 / 12500000) (-299664239 / 1000000000) (Real.log (741067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (368974051 / 500000000) ≤ -Real.log (500000000000 / 1045819639947) ∧
    -Real.log (500000000000 / 1045819639947) ≤ (92243513 / 125000000) := by
  have h := checkLog_sound (w := (45819639947 / 2045819639947)) (n := 12)
    (lo := (22400461 / 500000000)) (hi := (44800923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1045819639947 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1045819639947 / 1000000000000) = 1/(500000000000 / 1045819639947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (368974051 / 500000000) (92243513 / 125000000) (Real.log (1045819639947 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1045819639947 / 500000000000) = -Real.log (500000000000 / 1045819639947) := by
    rw [show ((1045819639947 / 500000000000) : ℝ) = ((500000000000 / 1045819639947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (147786153 / 200000000) ≤ -Real.log (100000000000 / 209369566697) ∧
    -Real.log (100000000000 / 209369566697) ≤ (738930767 / 1000000000) := by
  have h := checkLog_sound (w := (9369566697 / 409369566697)) (n := 12)
    (lo := (9156717 / 200000000)) (hi := (22891793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209369566697 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209369566697 / 200000000000) = 1/(100000000000 / 209369566697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (147786153 / 200000000) (738930767 / 1000000000) (Real.log (209369566697 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (209369566697 / 100000000000) = -Real.log (100000000000 / 209369566697) := by
    rw [show ((209369566697 / 100000000000) : ℝ) = ((100000000000 / 209369566697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (529204263 / 1000000000) ≤ -Real.log (31250000000 / 53049404509) ∧
    -Real.log (31250000000 / 53049404509) ≤ (66150533 / 125000000) := by
  have h := checkLog_sound (w := (21799404509 / 84299404509)) (n := 12)
    (lo := (529204263 / 1000000000)) (hi := (66150533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53049404509 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53049404509 / 31250000000) = 1/(31250000000 / 53049404509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (529204263 / 1000000000) (66150533 / 125000000) (Real.log (53049404509 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53049404509 / 31250000000) = -Real.log (31250000000 / 53049404509) := by
    rw [show ((53049404509 / 31250000000) : ℝ) = ((31250000000 / 53049404509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (66241097 / 125000000) ≤ -Real.log (12500000000 / 21235141357) ∧
    -Real.log (12500000000 / 21235141357) ≤ (529928777 / 1000000000) := by
  have h := checkLog_sound (w := (8735141357 / 33735141357)) (n := 12)
    (lo := (66241097 / 125000000)) (hi := (529928777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21235141357 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21235141357 / 12500000000) = 1/(12500000000 / 21235141357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (66241097 / 125000000) (529928777 / 1000000000) (Real.log (21235141357 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21235141357 / 12500000000) = -Real.log (12500000000 / 21235141357) := by
    rw [show ((21235141357 / 12500000000) : ℝ) = ((12500000000 / 21235141357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0313
