import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell111
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (274311837 / 1000000000) ≤ -Real.log (320 / 421) ∧
    -Real.log (320 / 421) ≤ (137155919 / 500000000) := by
  have h := checkLog_sound (w := (101 / 741)) (n := 12)
    (lo := (274311837 / 1000000000)) (hi := (137155919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421 / 320) = 1/(320 / 421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (274311837 / 1000000000) (137155919 / 500000000) (Real.log (421 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (421 / 320) = -Real.log (320 / 421) := by
    rw [show ((421 / 320) : ℝ) = ((320 / 421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75849853 / 200000000) ≤ -Real.log (219 / 320) ∧
    -Real.log (219 / 320) ≤ (189624633 / 500000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 219) = 1/(219 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-189624633 / 500000000) (-75849853 / 200000000) (Real.log (219 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27386637 / 100000000) ≤ -Real.log (5120 / 6733) ∧
    -Real.log (5120 / 6733) ≤ (273866371 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 11853)) (n := 12)
    (lo := (27386637 / 100000000)) (hi := (273866371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6733 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6733 / 5120) = 1/(5120 / 6733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27386637 / 100000000) (273866371 / 1000000000) (Real.log (6733 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6733 / 5120) = -Real.log (5120 / 6733) := by
    rw [show ((6733 / 5120) : ℝ) = ((5120 / 6733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (378393467 / 1000000000) ≤ -Real.log (3507 / 5120) ∧
    -Real.log (3507 / 5120) ≤ (94598367 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 8627)) (n := 12)
    (lo := (378393467 / 1000000000)) (hi := (94598367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3507) = 1/(3507 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-94598367 / 250000000) (-378393467 / 1000000000) (Real.log (3507 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (201901119 / 1000000000) ≤ -Real.log (1000000 / 1223727) ∧
    -Real.log (1000000 / 1223727) ≤ (630941 / 3125000) := by
  have h := checkLog_sound (w := (223727 / 2223727)) (n := 12)
    (lo := (201901119 / 1000000000)) (hi := (630941 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223727 / 1000000) = 1/(1000000 / 1223727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (201901119 / 1000000000) (630941 / 3125000) (Real.log (1223727 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223727 / 1000000) = -Real.log (1000000 / 1223727) := by
    rw [show ((1223727 / 1000000) : ℝ) = ((1000000 / 1223727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31656377 / 125000000) ≤ -Real.log (776273 / 1000000) ∧
    -Real.log (776273 / 1000000) ≤ (253251017 / 1000000000) := by
  have h := checkLog_sound (w := (223727 / 1776273)) (n := 12)
    (lo := (31656377 / 125000000)) (hi := (253251017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776273) = 1/(776273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-253251017 / 1000000000) (-31656377 / 125000000) (Real.log (776273 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202245091 / 1000000000) ≤ -Real.log (250000 / 306037) ∧
    -Real.log (250000 / 306037) ≤ (50561273 / 250000000) := by
  have h := checkLog_sound (w := (56037 / 556037)) (n := 12)
    (lo := (202245091 / 1000000000)) (hi := (50561273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306037 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306037 / 250000) = 1/(250000 / 306037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202245091 / 1000000000) (50561273 / 250000000) (Real.log (306037 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (306037 / 250000) = -Real.log (250000 / 306037) := by
    rw [show ((306037 / 250000) : ℝ) = ((250000 / 306037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126896749 / 500000000) ≤ -Real.log (193963 / 250000) ∧
    -Real.log (193963 / 250000) ≤ (253793499 / 1000000000) := by
  have h := checkLog_sound (w := (56037 / 443963)) (n := 12)
    (lo := (126896749 / 500000000)) (hi := (253793499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193963) = 1/(193963 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-253793499 / 1000000000) (-126896749 / 500000000) (Real.log (193963 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29757091 / 200000000) ≤ -Real.log (125000 / 145053) ∧
    -Real.log (125000 / 145053) ≤ (9299091 / 62500000) := by
  have h := checkLog_sound (w := (20053 / 270053)) (n := 12)
    (lo := (29757091 / 200000000)) (hi := (9299091 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145053 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145053 / 125000) = 1/(125000 / 145053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29757091 / 200000000) (9299091 / 62500000) (Real.log (145053 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145053 / 125000) = -Real.log (125000 / 145053) := by
    rw [show ((145053 / 125000) : ℝ) = ((125000 / 145053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (43714569 / 250000000) ≤ -Real.log (104947 / 125000) ∧
    -Real.log (104947 / 125000) ≤ (174858277 / 1000000000) := by
  have h := checkLog_sound (w := (20053 / 229947)) (n := 12)
    (lo := (43714569 / 250000000)) (hi := (174858277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104947) = 1/(104947 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174858277 / 1000000000) (-43714569 / 250000000) (Real.log (104947 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149052563 / 1000000000) ≤ -Real.log (500000 / 580367) ∧
    -Real.log (500000 / 580367) ≤ (37263141 / 250000000) := by
  have h := checkLog_sound (w := (80367 / 1080367)) (n := 12)
    (lo := (149052563 / 1000000000)) (hi := (37263141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580367 / 500000) = 1/(500000 / 580367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149052563 / 1000000000) (37263141 / 250000000) (Real.log (580367 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (580367 / 500000) = -Real.log (500000 / 580367) := by
    rw [show ((580367 / 500000) : ℝ) = ((500000 / 580367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (87613789 / 500000000) ≤ -Real.log (419633 / 500000) ∧
    -Real.log (419633 / 500000) ≤ (175227579 / 1000000000) := by
  have h := checkLog_sound (w := (80367 / 919633)) (n := 12)
    (lo := (87613789 / 500000000)) (hi := (175227579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419633) = 1/(419633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175227579 / 1000000000) (-87613789 / 500000000) (Real.log (419633 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326129919 / 500000000) ≤ -Real.log (3125000000 / 5999607927) ∧
    -Real.log (3125000000 / 5999607927) ≤ (652259839 / 1000000000) := by
  have h := checkLog_sound (w := (2874607927 / 9124607927)) (n := 12)
    (lo := (326129919 / 500000000)) (hi := (652259839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5999607927 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5999607927 / 3125000000) = 1/(3125000000 / 5999607927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326129919 / 500000000) (652259839 / 1000000000) (Real.log (5999607927 / 3125000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (5999607927 / 3125000000) = -Real.log (3125000000 / 5999607927) := by
    rw [show ((5999607927 / 3125000000) : ℝ) = ((3125000000 / 5999607927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (653561103 / 1000000000) ≤ -Real.log (125000000000 / 240296803653) ∧
    -Real.log (125000000000 / 240296803653) ≤ (40847569 / 62500000) := by
  have h := checkLog_sound (w := (115296803653 / 365296803653)) (n := 12)
    (lo := (653561103 / 1000000000)) (hi := (40847569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240296803653 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240296803653 / 125000000000) = 1/(125000000000 / 240296803653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (653561103 / 1000000000) (40847569 / 62500000) (Real.log (240296803653 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (240296803653 / 125000000000) = -Real.log (125000000000 / 240296803653) := by
    rw [show ((240296803653 / 125000000000) : ℝ) = ((125000000000 / 240296803653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (56894017 / 125000000) ≤ -Real.log (500000000000 / 788206597421) ∧
    -Real.log (500000000000 / 788206597421) ≤ (455152137 / 1000000000) := by
  have h := checkLog_sound (w := (288206597421 / 1288206597421)) (n := 12)
    (lo := (56894017 / 125000000)) (hi := (455152137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788206597421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788206597421 / 500000000000) = 1/(500000000000 / 788206597421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56894017 / 125000000) (455152137 / 1000000000) (Real.log (788206597421 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (788206597421 / 500000000000) = -Real.log (500000000000 / 788206597421) := by
    rw [show ((788206597421 / 500000000000) : ℝ) = ((500000000000 / 788206597421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (45603859 / 100000000) ≤ -Real.log (25000000000 / 39445280801) ∧
    -Real.log (25000000000 / 39445280801) ≤ (456038591 / 1000000000) := by
  have h := checkLog_sound (w := (14445280801 / 64445280801)) (n := 12)
    (lo := (45603859 / 100000000)) (hi := (456038591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39445280801 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39445280801 / 25000000000) = 1/(25000000000 / 39445280801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (45603859 / 100000000) (456038591 / 1000000000) (Real.log (39445280801 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (39445280801 / 25000000000) = -Real.log (25000000000 / 39445280801) := by
    rw [show ((39445280801 / 25000000000) : ℝ) = ((25000000000 / 39445280801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (80910933 / 250000000) ≤ -Real.log (500000000000 / 691077400973) ∧
    -Real.log (500000000000 / 691077400973) ≤ (323643733 / 1000000000) := by
  have h := checkLog_sound (w := (191077400973 / 1191077400973)) (n := 12)
    (lo := (80910933 / 250000000)) (hi := (323643733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691077400973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691077400973 / 500000000000) = 1/(500000000000 / 691077400973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (80910933 / 250000000) (323643733 / 1000000000) (Real.log (691077400973 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (691077400973 / 500000000000) = -Real.log (500000000000 / 691077400973) := by
    rw [show ((691077400973 / 500000000000) : ℝ) = ((500000000000 / 691077400973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (162140071 / 500000000) ≤ -Real.log (100000000000 / 138303469937) ∧
    -Real.log (100000000000 / 138303469937) ≤ (324280143 / 1000000000) := by
  have h := checkLog_sound (w := (38303469937 / 238303469937)) (n := 12)
    (lo := (162140071 / 500000000)) (hi := (324280143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138303469937 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138303469937 / 100000000000) = 1/(100000000000 / 138303469937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (162140071 / 500000000) (324280143 / 1000000000) (Real.log (138303469937 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (138303469937 / 100000000000) = -Real.log (100000000000 / 138303469937) := by
    rw [show ((138303469937 / 100000000000) : ℝ) = ((100000000000 / 138303469937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5235003 / 200000000) ≤ -Real.log (243541145311 / 250000000000) ∧
    -Real.log (243541145311 / 250000000000) ≤ (3271877 / 125000000) := by
  have h := checkLog_sound (w := (6458854689 / 493541145311)) (n := 12)
    (lo := (5235003 / 200000000)) (hi := (3271877 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243541145311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243541145311) = 1/(243541145311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3271877 / 125000000) (-5235003 / 200000000) (Real.log (243541145311 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1303641 / 50000000) ≤ -Real.log (15222877191 / 15625000000) ∧
    -Real.log (15222877191 / 15625000000) ≤ (26072821 / 1000000000) := by
  have h := checkLog_sound (w := (402122809 / 30847877191)) (n := 12)
    (lo := (1303641 / 50000000)) (hi := (26072821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15222877191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15222877191) = 1/(15222877191 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26072821 / 1000000000) (-1303641 / 50000000) (Real.log (15222877191 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell111
