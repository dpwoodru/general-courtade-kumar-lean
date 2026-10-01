import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0304
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

theorem reflection_log_1_neg : (222987289 / 1000000000) ≤ -Real.log (5120 / 6399) ∧
    -Real.log (5120 / 6399) ≤ (22298729 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 11519)) (n := 12)
    (lo := (222987289 / 1000000000)) (hi := (22298729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6399 / 5120) = 1/(5120 / 6399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (222987289 / 1000000000) (22298729 / 100000000) (Real.log (6399 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6399 / 5120) = -Real.log (5120 / 6399) := by
    rw [show ((6399 / 5120) : ℝ) = ((5120 / 6399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (287421689 / 1000000000) ≤ -Real.log (3841 / 5120) ∧
    -Real.log (3841 / 5120) ≤ (28742169 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 8961)) (n := 12)
    (lo := (287421689 / 1000000000)) (hi := (28742169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3841) = 1/(3841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28742169 / 100000000) (-287421689 / 1000000000) (Real.log (3841 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4455057 / 20000000) ≤ -Real.log (2048 / 2559) ∧
    -Real.log (2048 / 2559) ≤ (222752851 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 4607)) (n := 12)
    (lo := (4455057 / 20000000)) (hi := (222752851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2559 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2559 / 2048) = 1/(2048 / 2559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4455057 / 20000000) (222752851 / 1000000000) (Real.log (2559 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2559 / 2048) = -Real.log (2048 / 2559) := by
    rw [show ((2559 / 2048) : ℝ) = ((2048 / 2559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (143515621 / 500000000) ≤ -Real.log (1537 / 2048) ∧
    -Real.log (1537 / 2048) ≤ (287031243 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3585)) (n := 12)
    (lo := (143515621 / 500000000)) (hi := (287031243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1537) = 1/(1537 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-287031243 / 1000000000) (-143515621 / 500000000) (Real.log (1537 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (405204657 / 1000000000) ≤ -Real.log (2560 / 3839) ∧
    -Real.log (2560 / 3839) ≤ (202602329 / 500000000) := by
  have h := checkLog_sound (w := (1279 / 6399)) (n := 12)
    (lo := (405204657 / 1000000000)) (hi := (202602329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3839 / 2560) = 1/(2560 / 3839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (405204657 / 1000000000) (202602329 / 500000000) (Real.log (3839 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3839 / 2560) = -Real.log (2560 / 3839) := by
    rw [show ((3839 / 2560) : ℝ) = ((2560 / 3839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138473247 / 200000000) ≤ -Real.log (1281 / 2560) ∧
    -Real.log (1281 / 2560) ≤ (173091559 / 250000000) := by
  have h := checkLog_sound (w := (1279 / 3841)) (n := 12)
    (lo := (138473247 / 200000000)) (hi := (173091559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1281) = 1/(1281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-173091559 / 250000000) (-138473247 / 200000000) (Real.log (1281 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202406927 / 500000000) ≤ -Real.log (1024 / 1535) ∧
    -Real.log (1024 / 1535) ≤ (80962771 / 200000000) := by
  have h := checkLog_sound (w := (511 / 2559)) (n := 12)
    (lo := (202406927 / 500000000)) (hi := (80962771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535 / 1024) = 1/(1024 / 1535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202406927 / 500000000) (80962771 / 200000000) (Real.log (1535 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1535 / 1024) = -Real.log (1024 / 1535) := by
    rw [show ((1535 / 1024) : ℝ) = ((1024 / 1535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (17279899 / 25000000) ≤ -Real.log (513 / 1024) ∧
    -Real.log (513 / 1024) ≤ (691195961 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1537)) (n := 12)
    (lo := (17279899 / 25000000)) (hi := (691195961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 513) = 1/(513 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-691195961 / 1000000000) (-17279899 / 25000000) (Real.log (513 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (305248377 / 1000000000) ≤ -Real.log (500000 / 678481) ∧
    -Real.log (500000 / 678481) ≤ (152624189 / 500000000) := by
  have h := checkLog_sound (w := (178481 / 1178481)) (n := 12)
    (lo := (305248377 / 1000000000)) (hi := (152624189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678481 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678481 / 500000) = 1/(500000 / 678481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (305248377 / 1000000000) (152624189 / 500000000) (Real.log (678481 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678481 / 500000) = -Real.log (500000 / 678481) := by
    rw [show ((678481 / 500000) : ℝ) = ((500000 / 678481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (220775729 / 500000000) ≤ -Real.log (321519 / 500000) ∧
    -Real.log (321519 / 500000) ≤ (441551459 / 1000000000) := by
  have h := checkLog_sound (w := (178481 / 821519)) (n := 12)
    (lo := (220775729 / 500000000)) (hi := (441551459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321519) = 1/(321519 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-441551459 / 1000000000) (-220775729 / 500000000) (Real.log (321519 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (76391487 / 250000000) ≤ -Real.log (1000000 / 1357393) ∧
    -Real.log (1000000 / 1357393) ≤ (305565949 / 1000000000) := by
  have h := checkLog_sound (w := (357393 / 2357393)) (n := 12)
    (lo := (76391487 / 250000000)) (hi := (305565949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357393 / 1000000) = 1/(1000000 / 1357393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (76391487 / 250000000) (305565949 / 1000000000) (Real.log (1357393 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1357393 / 1000000) = -Real.log (1000000 / 1357393) := by
    rw [show ((1357393 / 1000000) : ℝ) = ((1000000 / 1357393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (442221939 / 1000000000) ≤ -Real.log (642607 / 1000000) ∧
    -Real.log (642607 / 1000000) ≤ (22111097 / 50000000) := by
  have h := checkLog_sound (w := (357393 / 1642607)) (n := 12)
    (lo := (442221939 / 1000000000)) (hi := (22111097 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642607) = 1/(642607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22111097 / 50000000) (-442221939 / 1000000000) (Real.log (642607 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (232406913 / 1000000000) ≤ -Real.log (1000000 / 1261633) ∧
    -Real.log (1000000 / 1261633) ≤ (116203457 / 500000000) := by
  have h := checkLog_sound (w := (261633 / 2261633)) (n := 12)
    (lo := (232406913 / 1000000000)) (hi := (116203457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261633 / 1000000) = 1/(1000000 / 1261633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (232406913 / 1000000000) (116203457 / 500000000) (Real.log (1261633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1261633 / 1000000) = -Real.log (1000000 / 1261633) := by
    rw [show ((1261633 / 1000000) : ℝ) = ((1000000 / 1261633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18957143 / 62500000) ≤ -Real.log (738367 / 1000000) ∧
    -Real.log (738367 / 1000000) ≤ (303314289 / 1000000000) := by
  have h := checkLog_sound (w := (261633 / 1738367)) (n := 12)
    (lo := (18957143 / 62500000)) (hi := (303314289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738367) = 1/(738367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-303314289 / 1000000000) (-18957143 / 62500000) (Real.log (738367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (29084447 / 125000000) ≤ -Real.log (250000 / 315493) ∧
    -Real.log (250000 / 315493) ≤ (232675577 / 1000000000) := by
  have h := checkLog_sound (w := (65493 / 565493)) (n := 12)
    (lo := (29084447 / 125000000)) (hi := (232675577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315493 / 250000) = 1/(250000 / 315493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (29084447 / 125000000) (232675577 / 1000000000) (Real.log (315493 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (315493 / 250000) = -Real.log (250000 / 315493) := by
    rw [show ((315493 / 250000) : ℝ) = ((250000 / 315493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151886757 / 500000000) ≤ -Real.log (184507 / 250000) ∧
    -Real.log (184507 / 250000) ≤ (60754703 / 200000000) := by
  have h := checkLog_sound (w := (65493 / 434507)) (n := 12)
    (lo := (151886757 / 500000000)) (hi := (60754703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184507) = 1/(184507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60754703 / 200000000) (-151886757 / 500000000) (Real.log (184507 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (149359967 / 200000000) ≤ -Real.log (500000000000 / 1055118049011) ∧
    -Real.log (500000000000 / 1055118049011) ≤ (746799837 / 1000000000) := by
  have h := checkLog_sound (w := (55118049011 / 2055118049011)) (n := 12)
    (lo := (10730531 / 200000000)) (hi := (3353291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055118049011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055118049011 / 1000000000000) = 1/(500000000000 / 1055118049011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (149359967 / 200000000) (746799837 / 1000000000) (Real.log (1055118049011 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1055118049011 / 500000000000) = -Real.log (500000000000 / 1055118049011) := by
    rw [show ((1055118049011 / 500000000000) : ℝ) = ((500000000000 / 1055118049011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (373893943 / 500000000) ≤ -Real.log (500000000000 / 1056161075121) ∧
    -Real.log (500000000000 / 1056161075121) ≤ (46736743 / 62500000) := by
  have h := checkLog_sound (w := (56161075121 / 2056161075121)) (n := 12)
    (lo := (27320353 / 500000000)) (hi := (54640707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056161075121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056161075121 / 1000000000000) = 1/(500000000000 / 1056161075121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (373893943 / 500000000) (46736743 / 62500000) (Real.log (1056161075121 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1056161075121 / 500000000000) = -Real.log (500000000000 / 1056161075121) := by
    rw [show ((1056161075121 / 500000000000) : ℝ) = ((500000000000 / 1056161075121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (535721201 / 1000000000) ≤ -Real.log (62500000000 / 106792506301) ∧
    -Real.log (62500000000 / 106792506301) ≤ (267860601 / 500000000) := by
  have h := checkLog_sound (w := (44292506301 / 169292506301)) (n := 12)
    (lo := (535721201 / 1000000000)) (hi := (267860601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106792506301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106792506301 / 62500000000) = 1/(62500000000 / 106792506301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (535721201 / 1000000000) (267860601 / 500000000) (Real.log (106792506301 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (106792506301 / 62500000000) = -Real.log (62500000000 / 106792506301) := by
    rw [show ((106792506301 / 62500000000) : ℝ) = ((62500000000 / 106792506301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (536449091 / 1000000000) ≤ -Real.log (250000000000 / 427481071179) ∧
    -Real.log (250000000000 / 427481071179) ≤ (134112273 / 250000000) := by
  have h := checkLog_sound (w := (177481071179 / 677481071179)) (n := 12)
    (lo := (536449091 / 1000000000)) (hi := (134112273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427481071179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427481071179 / 250000000000) = 1/(250000000000 / 427481071179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (536449091 / 1000000000) (134112273 / 250000000) (Real.log (427481071179 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (427481071179 / 250000000000) = -Real.log (250000000000 / 427481071179) := by
    rw [show ((427481071179 / 250000000000) : ℝ) = ((250000000000 / 427481071179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0304
